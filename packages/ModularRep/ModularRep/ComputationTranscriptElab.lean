import Lean.Elab.BuiltinTerm

/-!
# Build-time readers for computation transcripts

The terms in this file parse an embedded string while Lean elaborates the
source and emit ordinary numeral or numeral-list expressions.  The resulting
constants are literal kernel terms, and the kernel checks later equalities over
those emitted terms.  The elaborator's parsing is audited build provenance,
however, rather than a kernel theorem relating a literal to the source file or
to a field in the embedded string.

These readers are deliberately small.  They recognise exact `KEY=value`
records and exact line prefixes in the machine-readable GAP transcripts used
by the manuscript audit.
-/

namespace ModularRep.ComputationTranscriptElab

open Lean Elab Term Meta

/-- The numerical and label fields extracted from one `G_RADICAL` record.
The structure strings are checked by the parser but deliberately not assigned
mathematical meaning here. -/
structure RadicalRowProjection where
  pSubgroupClassIndex : Nat
  subgroupOrder : Nat
  normalizerOrder : Nat
  weightQuotientOrder : Nat
  trivialLabels : List Nat
  faithfulOneLabels : List Nat
  faithfulTwoLabels : List Nat
  deriving DecidableEq, Repr

/-- The fields of one `U_BLOCK_i` record used by the arithmetic certificate.
The sector code is `0`, `1`, or `2`, according to the exact central-ratio
string printed in the transcript. -/
structure BlockRowProjection where
  blockIndex : Nat
  defectExponent : Nat
  brauerLabels : List Nat
  sectorCode : Nat
  deriving DecidableEq, Repr

/-- One row of the printed Sylow subgroup order distribution. -/
structure SubgroupOrderMultiplicityProjection where
  subgroupOrder : Nat
  multiplicity : Nat
  deriving DecidableEq, Repr

/-- The three numerical fields of one printed `P_RADICAL` record. -/
structure PRadicalRowProjection where
  pSubgroupClassIndex : Nat
  subgroupOrder : Nat
  normalizerOrder : Nat
  deriving DecidableEq, Repr

/-- The two class indices in one printed `G_FUSION` record. -/
structure GFusionRowProjection where
  sourcePClassIndex : Nat
  targetPClassIndex : Nat
  deriving DecidableEq, Repr

/-- The complete numerical bookkeeping printed before the twelve
`G_RADICAL` records.  The parser preserves transcript order. -/
structure RadicalSearchBookkeepingProjection where
  subgroupClassCountInSylow : Nat
  subgroupOrderDistribution : List SubgroupOrderMultiplicityProjection
  pRadicalRows : List PRadicalRowProjection
  pRadicalRepresentativeCount : Nat
  fusionRows : List GFusionRowProjection
  gRadicalClassCount : Nat
  deriving DecidableEq, Repr

private meta def literalString (stx : Syntax) (kind : String) : TermElabM String := do
  let some value := stx.isStrLit?
    | throwError "expected a literal {kind}"
  pure value

private meta def transcriptContents (stx : Syntax) : TermElabM String := do
  let expression ← elabTerm stx (some (mkConst ``String))
  let expression ← withTransparency .all <| whnf expression
  let some contents := getStringValue? expression
    | throwError "expected an embedded transcript string"
  pure contents

private meta def valueAtKey (contents key : String) : TermElabM String := do
  let keyPrefix := key ++ "="
  let lines := contents.splitOn "\n"
  match lines.filter (·.startsWith keyPrefix) with
  | [] => throwError "key `{key}` not found in the transcript"
  | [_] => pure ()
  | duplicateLines =>
      throwError "key `{key}` occurs {duplicateLines.length} times in the transcript"
  let some start := lines.findIdx? (·.startsWith keyPrefix)
    | throwError "internal error while locating key `{key}`"
  let first := (lines[start]!).drop keyPrefix.length |>.trimAscii.copy
  let rec collect (remaining : List String) (balance : Int)
      (accumulator : String) : TermElabM String := do
    match remaining with
    | [] => throwError "unterminated bracketed value for `{key}`"
    | line :: tail =>
        let next := line.trimAscii.copy
        let balance := balance + next.toList.count '[' - next.toList.count ']'
        let accumulator := accumulator ++ "\n" ++ next
        if balance ≤ 0 then pure accumulator else collect tail balance accumulator
  let rec beginValue (candidate : String) (remaining : List String) : TermElabM String := do
    if candidate.isEmpty then
      match remaining with
      | [] => throwError "empty value for `{key}`"
      | line :: tail => beginValue line.trimAscii.copy tail
    else
      let opens := candidate.toList.count '['
      let closes := candidate.toList.count ']'
      if opens ≤ closes then pure candidate
      else collect remaining (Int.ofNat (opens - closes)) candidate
  beginValue first (lines.drop (start + 1))

private meta def lineAtPrefix (contents linePrefix : String) : TermElabM String := do
  match (contents.splitOn "\n").filter (·.startsWith linePrefix) with
  | [] => throwError "line prefix `{linePrefix}` not found in the transcript"
  | [line] => pure line
  | duplicateLines =>
      throwError "line prefix `{linePrefix}` occurs {duplicateLines.length} times in the transcript"

private def isTranscriptWhitespace : Char → Bool
  | ' ' | '\t' | '\r' | '\n' => true
  | _ => false

private def skipTranscriptWhitespace (characters : List Char) : List Char :=
  characters.dropWhile isTranscriptWhitespace

private def isDecimalDigit (character : Char) : Bool :=
  '0' ≤ character && character ≤ '9'

private def parseNaturalPrefix (characters : List Char) :
    Except String (Nat × List Char) := do
  let characters := skipTranscriptWhitespace characters
  let (digits, remaining) := characters.span isDecimalDigit
  if digits.isEmpty then
    throw "expected a natural number"
  let some value := (String.ofList digits).toNat?
    | throw "invalid natural number"
  pure (value, remaining)

private partial def parseNaturalListPrefix (characters : List Char) :
    Except String (List Nat × List Char) := do
  let characters := skipTranscriptWhitespace characters
  let remaining ← match characters with
    | '[' :: remaining => pure remaining
    | _ => throw "expected `[`"
  let remaining := skipTranscriptWhitespace remaining
  match remaining with
  | ']' :: tail => pure ([], tail)
  | _ =>
      let (first, remaining) ← parseNaturalPrefix remaining
      let rec parseMore (values : List Nat) (remaining : List Char) :
          Except String (List Nat × List Char) := do
        let remaining := skipTranscriptWhitespace remaining
        match remaining with
        | ']' :: tail => pure (values.reverse, tail)
        | ',' :: tail =>
            let (next, remaining) ← parseNaturalPrefix tail
            parseMore (next :: values) remaining
        | _ => throw "expected `,` or `]`"
      parseMore [first] remaining

private partial def parseNaturalMatrixPrefix (characters : List Char) :
    Except String (List (List Nat) × List Char) := do
  let characters := skipTranscriptWhitespace characters
  let remaining ← match characters with
    | '[' :: remaining => pure remaining
    | _ => throw "expected outer `[`"
  let remaining := skipTranscriptWhitespace remaining
  match remaining with
  | ']' :: tail => pure ([], tail)
  | _ =>
      let (first, remaining) ← parseNaturalListPrefix remaining
      let rec parseMore (rows : List (List Nat)) (remaining : List Char) :
          Except String (List (List Nat) × List Char) := do
        let remaining := skipTranscriptWhitespace remaining
        match remaining with
        | ']' :: tail => pure (rows.reverse, tail)
        | ',' :: tail =>
            let (next, remaining) ← parseNaturalListPrefix tail
            parseMore (next :: rows) remaining
        | _ => throw "expected `,` or outer `]`"
      parseMore [first] remaining

private def parseNaturalList (text : String) : Except String (List Nat) := do
  let (values, remaining) ← parseNaturalListPrefix text.toList
  if (skipTranscriptWhitespace remaining).isEmpty then
    pure values
  else
    throw "unexpected text after the closing bracket"

private def parseNaturalMatrix (text : String) : Except String (List (List Nat)) := do
  let (values, remaining) ← parseNaturalMatrixPrefix text.toList
  if (skipTranscriptWhitespace remaining).isEmpty then
    pure values
  else
    throw "unexpected text after the outer closing bracket"

private def consumeLiteral (literal : String) (characters : List Char) :
    Except String (List Char) :=
  if characters.take literal.length = literal.toList then
    pure (characters.drop literal.length)
  else
    throw s!"expected `{literal}`"

private def parseNonemptyTextToPipe (characters : List Char) :
    Except String (String × List Char) := do
  let (value, remaining) := characters.span (· != '|')
  let value := (String.ofList value).trimAscii.copy
  if value.isEmpty then
    throw "expected a nonempty field value"
  match remaining with
  | '|' :: tail => pure (value, tail)
  | _ => throw "expected `|` after the field value"

private def parseRadicalRow (text : String) :
    Except String (RadicalRowProjection × List Char) := do
  let remaining ← consumeLiteral "pclass=" text.toList
  let (pSubgroupClassIndex, remaining) ← parseNaturalPrefix remaining
  let remaining ← consumeLiteral "|qsize=" remaining
  let (subgroupOrder, remaining) ← parseNaturalPrefix remaining
  let remaining ← consumeLiteral "|qstructure=" remaining
  let (_, remaining) ← parseNonemptyTextToPipe remaining
  let remaining ← consumeLiteral "nsize=" remaining
  let (normalizerOrder, remaining) ← parseNaturalPrefix remaining
  let remaining ← consumeLiteral "|wsize=" remaining
  let (weightQuotientOrder, remaining) ← parseNaturalPrefix remaining
  let remaining ← consumeLiteral "|wstructure=" remaining
  let (_, remaining) ← parseNonemptyTextToPipe remaining
  let remaining ← consumeLiteral "dz_z1=" remaining
  let (trivialLabels, remaining) ← parseNaturalListPrefix remaining
  let remaining ← consumeLiteral "|dz_omega=" remaining
  let (faithfulOneLabels, remaining) ← parseNaturalListPrefix remaining
  let remaining ← consumeLiteral "|dz_omega2=" remaining
  let (faithfulTwoLabels, remaining) ← parseNaturalListPrefix remaining
  pure ({ pSubgroupClassIndex := pSubgroupClassIndex
          subgroupOrder := subgroupOrder
          normalizerOrder := normalizerOrder
          weightQuotientOrder := weightQuotientOrder
          trivialLabels := trivialLabels
          faithfulOneLabels := faithfulOneLabels
          faithfulTwoLabels := faithfulTwoLabels }, remaining)

private def parseAllRadicalRows (contents : String) :
    Except String (List RadicalRowProjection) := do
  let pieces := contents.splitOn "G_RADICAL|"
  let rowPieces := pieces.drop 1
  if rowPieces.length != 12 then
    throw s!"expected exactly 12 `G_RADICAL` records, found {rowPieces.length}"
  let rec parseRows (remainingPieces : List String)
      (rows : List RadicalRowProjection) :
      Except String (List RadicalRowProjection) := do
    match remainingPieces with
    | [] => pure rows.reverse
    | [last] =>
        let (row, remaining) ← parseRadicalRow last
        let remaining := skipTranscriptWhitespace remaining
        let _ ← consumeLiteral
          "ORDER_CONTRIBUTIONS_[QSIZE,Z1,OMEGA,OMEGA2]=" remaining
        pure (row :: rows).reverse
    | piece :: tail =>
        let (row, remaining) ← parseRadicalRow piece
        if !(skipTranscriptWhitespace remaining).isEmpty then
          throw "unexpected text after a `G_RADICAL` record"
        parseRows tail (row :: rows)
  parseRows rowPieces []

private def uniqueTailAfter (contents recordPrefix : String) : Except String String := do
  match contents.splitOn recordPrefix with
  | [_, tail] => pure tail
  | [_] => throw s!"record prefix `{recordPrefix}` not found in the transcript"
  | pieces =>
      throw s!"record prefix `{recordPrefix}` occurs {pieces.length - 1} times in the transcript"

private def parseBooleanPrefix (characters : List Char) :
    Except String (Bool × List Char) := do
  if characters.take 4 = "true".toList then
    pure (true, characters.drop 4)
  else if characters.take 5 = "false".toList then
    pure (false, characters.drop 5)
  else
    throw "expected `true` or `false`"

private def compactTranscriptValue (value : String) : String :=
  String.ofList (value.toList.filter (fun character => !isTranscriptWhitespace character))

private def parseSectorCode (value : String) : Except String Nat :=
  match compactTranscriptValue value with
  | "[1,1,1]" => pure 0
  | "[1,E(3),E(3)^2]" => pure 1
  | "[1,E(3)^2,E(3)]" => pure 2
  | compact => throw s!"unrecognised central-ratio value `{compact}`"

private meta def parseBlockRow (contents : String) (blockIndex : Nat) :
    TermElabM BlockRowProjection := do
  let recordPrefix := s!"U_BLOCK_{blockIndex}_DEFECT="
  let tail ← match uniqueTailAfter contents recordPrefix with
    | .ok tail => pure tail
    | .error message => throwError message
  let (defectExponent, remaining) ← match parseNaturalPrefix tail.toList with
    | .ok result => pure result
    | .error message => throwError "invalid `{recordPrefix}` record: {message}"
  let remaining ← match consumeLiteral ";IBR=" remaining with
    | .ok remaining => pure remaining
    | .error message => throwError "invalid `{recordPrefix}` record: {message}"
  let (brauerLabels, remaining) ← match parseNaturalListPrefix remaining with
    | .ok result => pure result
    | .error message => throwError "invalid `{recordPrefix}` record: {message}"
  let remaining ← match consumeLiteral ";ORD=" remaining with
    | .ok remaining => pure remaining
    | .error message => throwError "invalid `{recordPrefix}` record: {message}"
  let (_, remaining) ← match parseNaturalListPrefix remaining with
    | .ok result => pure result
    | .error message => throwError "invalid `{recordPrefix}` record: {message}"
  let remaining ← match consumeLiteral ";BRAUER_TREE_STORED=" remaining with
    | .ok remaining => pure remaining
    | .error message => throwError "invalid `{recordPrefix}` record: {message}"
  let (_, remaining) ← match parseBooleanPrefix remaining with
    | .ok result => pure result
    | .error message => throwError "invalid `{recordPrefix}` record: {message}"
  let expectedNext := s!"U_BLOCK_{blockIndex}_DECOMPOSITION_SUBMATRIX="
  match consumeLiteral expectedNext (skipTranscriptWhitespace remaining) with
  | .error message => throwError "invalid `{recordPrefix}` record: {message}"
  | .ok _ => pure ()
  let sectorValue ← valueAtKey contents s!"U_BLOCK_{blockIndex}_CENTRAL_RATIOS"
  let sectorCode ← match parseSectorCode sectorValue with
    | .ok sectorCode => pure sectorCode
    | .error message =>
        throwError "invalid central ratios for block {blockIndex}: {message}"
  pure { blockIndex := blockIndex
         defectExponent := defectExponent
         brauerLabels := brauerLabels
         sectorCode := sectorCode }

private meta def parseAllBlockRows (contents : String) :
    TermElabM (List BlockRowProjection) := do
  let defectLines := (contents.splitOn "\n").filter fun line =>
    line.startsWith "U_BLOCK_" && (line.splitOn "_DEFECT=").length = 2
  if defectLines.length != 9 then
    throwError "expected exactly 9 `U_BLOCK_i_DEFECT` records, found {defectLines.length}"
  let sectorLines := (contents.splitOn "\n").filter fun line =>
    line.startsWith "U_BLOCK_" &&
      (line.splitOn "_CENTRAL_RATIOS=").length = 2
  if sectorLines.length != 9 then
    throwError "expected exactly 9 `U_BLOCK_i_CENTRAL_RATIOS` records, found {sectorLines.length}"
  (List.range 9).mapM fun zeroBased => parseBlockRow contents (zeroBased + 1)

private def parseSubgroupOrderDistribution (text : String) :
    Except String (List SubgroupOrderMultiplicityProjection) := do
  let rows ← parseNaturalMatrix text
  if rows.length != 10 then
    throw s!"expected exactly 10 subgroup-order rows, found {rows.length}"
  rows.mapM fun row =>
    match row with
    | [subgroupOrder, multiplicity] =>
        pure { subgroupOrder := subgroupOrder, multiplicity := multiplicity }
    | _ => throw "each subgroup-order row must contain exactly two natural numbers"

private def parsePRadicalRow (line : String) : Except String PRadicalRowProjection := do
  let remaining ← consumeLiteral "P_RADICAL|pclass=" line.toList
  let (pSubgroupClassIndex, remaining) ← parseNaturalPrefix remaining
  let remaining ← consumeLiteral "|qsize=" remaining
  let (subgroupOrder, remaining) ← parseNaturalPrefix remaining
  let remaining ← consumeLiteral "|nsize=" remaining
  let (normalizerOrder, remaining) ← parseNaturalPrefix remaining
  if !(skipTranscriptWhitespace remaining).isEmpty then
    throw "unexpected text after a `P_RADICAL` record"
  pure { pSubgroupClassIndex := pSubgroupClassIndex
         subgroupOrder := subgroupOrder
         normalizerOrder := normalizerOrder }

private def parseGFusionRow (line : String) : Except String GFusionRowProjection := do
  let remaining ← consumeLiteral "G_FUSION|pclass=" line.toList
  let (sourcePClassIndex, remaining) ← parseNaturalPrefix remaining
  let remaining ← consumeLiteral "|representative=" remaining
  let (targetPClassIndex, remaining) ← parseNaturalPrefix remaining
  if !(skipTranscriptWhitespace remaining).isEmpty then
    throw "unexpected text after a `G_FUSION` record"
  pure { sourcePClassIndex := sourcePClassIndex
         targetPClassIndex := targetPClassIndex }

private meta def naturalAtKey (contents key : String) : TermElabM Nat := do
  let valueText ← valueAtKey contents key
  let some value := valueText.toNat?
    | throwError "value for `{key}` is not a natural number: `{valueText}`"
  pure value

private meta def parseRadicalSearchBookkeeping (contents : String) :
    TermElabM RadicalSearchBookkeepingProjection := do
  let subgroupClassCountInSylow ← naturalAtKey contents "P_SUBGROUP_CLASS_COUNT"
  let distributionText ← valueAtKey contents "P_SUBGROUP_ORDER_DISTRIBUTION"
  let subgroupOrderDistribution ←
    match parseSubgroupOrderDistribution distributionText with
    | .ok rows => pure rows
    | .error message =>
        throwError "invalid `P_SUBGROUP_ORDER_DISTRIBUTION`: {message}"
  let pRadicalLines := (contents.splitOn "\n").filter
    (fun line => line.startsWith "P_RADICAL|")
  if pRadicalLines.length != 26 then
    throwError "expected exactly 26 `P_RADICAL` records, found {pRadicalLines.length}"
  let pRadicalRows ← pRadicalLines.mapM fun line =>
    match parsePRadicalRow line with
    | .ok row => pure row
    | .error message => throwError "invalid `P_RADICAL` record: {message}"
  let pRadicalRepresentativeCount ← naturalAtKey contents "P_RADICAL_COUNT"
  let fusionLines := (contents.splitOn "\n").filter
    (fun line => line.startsWith "G_FUSION|")
  if fusionLines.length != 14 then
    throwError "expected exactly 14 `G_FUSION` records, found {fusionLines.length}"
  let fusionRows ← fusionLines.mapM fun line =>
    match parseGFusionRow line with
    | .ok row => pure row
    | .error message => throwError "invalid `G_FUSION` record: {message}"
  let gRadicalClassCount ← naturalAtKey contents "G_RADICAL_CLASS_COUNT"
  pure { subgroupClassCountInSylow := subgroupClassCountInSylow
         subgroupOrderDistribution := subgroupOrderDistribution
         pRadicalRows := pRadicalRows
         pRadicalRepresentativeCount := pRadicalRepresentativeCount
         fusionRows := fusionRows
         gRadicalClassCount := gRadicalClassCount }

private meta def elaborateNatList (values : List Nat) : TermElabM Expr :=
  mkListLit (mkConst ``Nat) (values.map mkNatLit)

private meta def elaborateNatMatrix (values : List (List Nat)) : TermElabM Expr := do
  let natType := Lean.mkConst ``Nat
  let rowType := Lean.mkApp (Lean.mkConst ``List [Level.zero]) natType
  let rows ← values.mapM fun row => mkListLit natType (row.map mkNatLit)
  mkListLit rowType rows

private meta def elaborateRadicalRows
    (rows : List RadicalRowProjection) : TermElabM Expr := do
  let rows ← rows.mapM fun row => do
    let trivialLabels ← elaborateNatList row.trivialLabels
    let faithfulOneLabels ← elaborateNatList row.faithfulOneLabels
    let faithfulTwoLabels ← elaborateNatList row.faithfulTwoLabels
    pure <| mkAppN (mkConst ``RadicalRowProjection.mk)
      #[mkNatLit row.pSubgroupClassIndex, mkNatLit row.subgroupOrder,
        mkNatLit row.normalizerOrder, mkNatLit row.weightQuotientOrder,
        trivialLabels, faithfulOneLabels, faithfulTwoLabels]
  mkListLit (mkConst ``RadicalRowProjection) rows

private meta def elaborateBlockRows
    (rows : List BlockRowProjection) : TermElabM Expr := do
  let rows ← rows.mapM fun row => do
    let brauerLabels ← elaborateNatList row.brauerLabels
    pure <| mkAppN (mkConst ``BlockRowProjection.mk)
      #[mkNatLit row.blockIndex, mkNatLit row.defectExponent,
        brauerLabels, mkNatLit row.sectorCode]
  mkListLit (mkConst ``BlockRowProjection) rows

private meta def elaborateSubgroupOrderDistribution
    (rows : List SubgroupOrderMultiplicityProjection) : TermElabM Expr := do
  let rows := rows.map fun row =>
    mkAppN (mkConst ``SubgroupOrderMultiplicityProjection.mk)
      #[mkNatLit row.subgroupOrder, mkNatLit row.multiplicity]
  mkListLit (mkConst ``SubgroupOrderMultiplicityProjection) rows

private meta def elaboratePRadicalRows
    (rows : List PRadicalRowProjection) : TermElabM Expr := do
  let rows := rows.map fun row =>
    mkAppN (mkConst ``PRadicalRowProjection.mk)
      #[mkNatLit row.pSubgroupClassIndex, mkNatLit row.subgroupOrder,
        mkNatLit row.normalizerOrder]
  mkListLit (mkConst ``PRadicalRowProjection) rows

private meta def elaborateGFusionRows
    (rows : List GFusionRowProjection) : TermElabM Expr := do
  let rows := rows.map fun row =>
    mkAppN (mkConst ``GFusionRowProjection.mk)
      #[mkNatLit row.sourcePClassIndex, mkNatLit row.targetPClassIndex]
  mkListLit (mkConst ``GFusionRowProjection) rows

private meta def elaborateRadicalSearchBookkeeping
    (bookkeeping : RadicalSearchBookkeepingProjection) : TermElabM Expr := do
  let subgroupOrderDistribution ←
    elaborateSubgroupOrderDistribution bookkeeping.subgroupOrderDistribution
  let pRadicalRows ← elaboratePRadicalRows bookkeeping.pRadicalRows
  let fusionRows ← elaborateGFusionRows bookkeeping.fusionRows
  pure <| mkAppN (mkConst ``RadicalSearchBookkeepingProjection.mk)
    #[mkNatLit bookkeeping.subgroupClassCountInSylow,
      subgroupOrderDistribution, pRadicalRows,
      mkNatLit bookkeeping.pRadicalRepresentativeCount, fusionRows,
      mkNatLit bookkeeping.gRadicalClassCount]

syntax (name := outputNat) "output_nat" term:max str : term
syntax (name := outputNatList) "output_nat_list" term:max str : term
syntax (name := outputNatMatrix) "output_nat_matrix" term:max str : term
syntax (name := outputLineNat) "output_line_nat" term:max str str : term
syntax (name := outputGRadicalRows) "output_g_radical_rows" term:max : term
syntax (name := outputUBlockRows) "output_u_block_rows" term:max : term
syntax (name := outputRadicalSearchBookkeeping)
  "output_radical_search_bookkeeping" term:max : term

/-- Read the natural number on the unique line `KEY=value`. -/
@[term_elab outputNat] meta def elabOutputNat : TermElab := fun stx _ => do
  let key ← literalString stx[2] "key"
  let valueText ← valueAtKey (← transcriptContents stx[1]) key
  let some value := valueText.toNat?
    | throwError "value for `{key}` is not a natural number: `{valueText}`"
  pure (mkNatLit value)

/-- Read a flat natural-number list on the unique `KEY=value` record. -/
@[term_elab outputNatList] meta def elabOutputNatList : TermElab := fun stx _ => do
  let key ← literalString stx[2] "key"
  let valueText ← valueAtKey (← transcriptContents stx[1]) key
  let values ← match parseNaturalList valueText with
    | .ok values => pure values
    | .error message => throwError "invalid list for `{key}`: {message}"
  elaborateNatList values

/-- Read a matrix of natural numbers on the unique `KEY=value` record,
preserving both the number of rows and the length of every row. -/
@[term_elab outputNatMatrix] meta def elabOutputNatMatrix : TermElab := fun stx _ => do
  let key ← literalString stx[2] "key"
  let valueText ← valueAtKey (← transcriptContents stx[1]) key
  let values ← match parseNaturalMatrix valueText with
    | .ok values => pure values
    | .error message => throwError "invalid matrix for `{key}`: {message}"
  elaborateNatMatrix values

/-- Read one natural-valued `field=value` token from the first line with the
given exact prefix. -/
@[term_elab outputLineNat] meta def elabOutputLineNat : TermElab := fun stx _ => do
  let linePrefix ← literalString stx[2] "line prefix"
  let field ← literalString stx[3] "field"
  let line ← lineAtPrefix (← transcriptContents stx[1]) linePrefix
  let fieldPrefix := field ++ "="
  let tokens := (line.splitOn " ").filter (·.startsWith fieldPrefix)
  let token ← match tokens with
    | [] => throwError "field `{field}` not found after `{linePrefix}`"
    | [token] => pure token
    | _ => throwError "field `{field}` occurs {tokens.length} times after `{linePrefix}`"
  let valueText := (token.drop fieldPrefix.length).trimAscii.copy
  let some value := valueText.toNat?
    | throwError "field `{field}` after `{linePrefix}` is not a natural number: `{valueText}`"
  pure (mkNatLit value)

/-- Read and validate all twelve multiline `G_RADICAL` records. -/
@[term_elab outputGRadicalRows] meta def elabOutputGRadicalRows : TermElab := fun stx _ => do
  let rows ← match parseAllRadicalRows (← transcriptContents stx[1]) with
    | .ok rows => pure rows
    | .error message => throwError message
  elaborateRadicalRows rows

/-- Read and validate the nine multiline `U_BLOCK_i` records together with
their exact central-ratio sector encodings. -/
@[term_elab outputUBlockRows] meta def elabOutputUBlockRows : TermElab := fun stx _ => do
  let rows ← parseAllBlockRows (← transcriptContents stx[1])
  elaborateBlockRows rows

/-- Read and validate the ten subgroup-order rows, 26 `P_RADICAL` rows,
14 `G_FUSION` rows, and three numerical summary fields. -/
@[term_elab outputRadicalSearchBookkeeping]
meta def elabOutputRadicalSearchBookkeeping : TermElab := fun stx _ => do
  let bookkeeping ← parseRadicalSearchBookkeeping (← transcriptContents stx[1])
  elaborateRadicalSearchBookkeeping bookkeeping

end ModularRep.ComputationTranscriptElab


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
