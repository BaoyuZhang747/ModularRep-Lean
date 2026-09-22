/-!
# Pure parsers for selected computation transcript fields

Unlike `ComputationTranscriptElab`, the functions in this module are ordinary
Lean definitions.  A theorem whose statement contains one of these parser
applications therefore leaves the parsing computation visible to the kernel.
The functions recognise the first matching `KEY=value` record, flat lists and
matrices of natural numbers, and natural valued fields on the first matching
prefixed line.  The stricter build-time elaborator separately rejects duplicate
selected keys and fields.

These functions start from an already embedded `String`.  They do not verify
the build tool operation by which `include_str` read a file and produced that
string.
-/

namespace ModularRep.ComputationTranscriptPure

def isWhitespace : Char -> Bool
  | ' ' | '\t' | '\r' | '\n' => true
  | _ => false

def takeLine : List Char -> List Char × List Char
  | [] => ([], [])
  | '\n' :: remaining => ([], remaining)
  | character :: remaining =>
      let (line, afterLine) := takeLine remaining
      (character :: line, afterLine)

def startsWithChars : List Char -> List Char -> Bool
  | _, [] => true
  | [], _ :: _ => false
  | actual :: remaining, expected :: expectedRemaining =>
      actual == expected && startsWithChars remaining expectedRemaining

def dropPrefix? : List Char -> List Char -> Option (List Char)
  | remaining, [] => some remaining
  | [], _ :: _ => none
  | actual :: remaining, expected :: expectedRemaining =>
      if actual == expected then dropPrefix? remaining expectedRemaining else none

def bracketsClosed (characters : List Char) : Bool :=
  characters.count '[' <= characters.count ']'

def collectValueFromText : Nat -> List Char -> List Char -> Option (List Char)
  | 0, _, _ => none
  | fuel + 1, accumulator, remainingText =>
      if !accumulator.all isWhitespace && bracketsClosed accumulator then
        some accumulator
      else
        match remainingText with
        | [] => none
        | _ =>
            let (line, afterLine) := takeLine remainingText
            let nextAccumulator :=
              if accumulator.all isWhitespace then line
              else (accumulator ++ ['\n']) ++ line
            collectValueFromText fuel nextAccumulator afterLine

def findKeyValue : Nat -> List Char -> List Char -> Option (List Char)
  | 0, _, _ => none
  | fuel + 1, remainingText, needle =>
      match remainingText with
      | [] => none
      | _ =>
          let (line, afterLine) := takeLine remainingText
          if startsWithChars line needle then do
            let initial <- dropPrefix? line needle
            collectValueFromText fuel initial afterLine
          else
            findKeyValue fuel afterLine needle

/-- A conservative line bound for the current root output transcripts.  It is
part of the parser definition, not a claim that a search or computation is
complete. -/
def parserFuel : Nat := 1024

/-- The value of the first `KEY=value` record.  A bracketed value may continue
on following lines. -/
def valueAtKeyChars? (contents key : String) : Option (List Char) := do
  let needle := key.toList ++ ['=']
  findKeyValue parserFuel contents.toList needle

/-- The value of the first `KEY=value` record as a string.  Numerical parsers
below use the character-list version directly. -/
def valueAtKey? (contents key : String) : Option String :=
  (valueAtKeyChars? contents key).map String.ofList

def stripBrackets? (characters : List Char) : Option (List Char) :=
  match characters with
  | '[' :: remaining =>
      match remaining.reverse with
      | ']' :: reversedMiddle => some reversedMiddle.reverse
      | _ => none
  | _ => none

def digitValue? : Char -> Option Nat
  | '0' => some 0
  | '1' => some 1
  | '2' => some 2
  | '3' => some 3
  | '4' => some 4
  | '5' => some 5
  | '6' => some 6
  | '7' => some 7
  | '8' => some 8
  | '9' => some 9
  | _ => none

def parseDigits : List Char -> Nat -> Bool -> Option (Nat × List Char)
  | [], value, true => some (value, [])
  | [], _, false => none
  | character :: remaining, value, seen =>
      match digitValue? character with
      | some digit => parseDigits remaining (10 * value + digit) true
      | none => if seen then some (value, character :: remaining) else none

def skipWhitespace (characters : List Char) : List Char :=
  characters.dropWhile isWhitespace

def trimWhitespace (characters : List Char) : List Char :=
  let withoutLeading := characters.dropWhile isWhitespace
  (withoutLeading.reverse.dropWhile isWhitespace).reverse

def parseNatPrefix? (characters : List Char) : Option (Nat × List Char) :=
  parseDigits (skipWhitespace characters) 0 false

/-- Parse one natural number with no sign or trailing characters. -/
def parseNat? (text : String) : Option Nat :=
  match parseNatPrefix? text.toList with
  | some (value, remaining) =>
      if remaining.all isWhitespace then some value else none
  | none => none

def splitCommasAux (currentReversed : List Char) :
    List Char -> List (List Char)
  | [] => [currentReversed.reverse]
  | ',' :: remaining =>
      currentReversed.reverse :: splitCommasAux [] remaining
  | character :: remaining =>
      splitCommasAux (character :: currentReversed) remaining

def parseNatChars? (characters : List Char) : Option Nat :=
  match parseNatPrefix? characters with
  | some (value, remaining) =>
      if remaining.all isWhitespace then some value else none
  | none => none

def parseBareNatList? (characters : List Char) : Option (List Nat) :=
  if characters.all isWhitespace then some []
  else (splitCommasAux [] characters).mapM parseNatChars?

def parseNatListChars? (characters : List Char) : Option (List Nat) := do
  let middle <- stripBrackets? (trimWhitespace characters)
  parseBareNatList? middle

/-- Parse a flat bracketed list of natural numbers. -/
def parseNatList? (text : String) : Option (List Nat) := do
  parseNatListChars? text.toList

def splitTopLevelCommasAux (depth : Nat)
    (currentReversed : List Char) :
    List Char -> Option (List (List Char))
  | [] =>
      if depth = 0 then some [currentReversed.reverse] else none
  | '[' :: remaining =>
      splitTopLevelCommasAux (depth + 1)
        ('[' :: currentReversed) remaining
  | ']' :: remaining =>
      match depth with
      | 0 => none
      | nextDepth + 1 =>
          splitTopLevelCommasAux nextDepth
            (']' :: currentReversed) remaining
  | ',' :: remaining =>
      if depth = 0 then do
        let later <- splitTopLevelCommasAux 0 [] remaining
        some (currentReversed.reverse :: later)
      else
        splitTopLevelCommasAux depth (',' :: currentReversed) remaining
  | character :: remaining =>
      splitTopLevelCommasAux depth
        (character :: currentReversed) remaining

def parseNatMatrixChars? (characters : List Char) :
    Option (List (List Nat)) := do
  let rowsText <- stripBrackets? (trimWhitespace characters)
  if (trimWhitespace rowsText).isEmpty then
    some []
  else do
    let rows <- splitTopLevelCommasAux 0 [] rowsText
    rows.mapM parseNatListChars?

/-- Parse a bracketed list of bracketed natural number lists, retaining every
row boundary. -/
def parseNatMatrix? (text : String) : Option (List (List Nat)) := do
  parseNatMatrixChars? text.toList

/-- Parse a natural number from the first `KEY=value` record. -/
def natAtKey? (contents key : String) : Option Nat := do
  parseNatChars? (<- valueAtKeyChars? contents key)

/-- Parse a flat natural number list from the first `KEY=value` record. -/
def natListAtKey? (contents key : String) : Option (List Nat) := do
  let value <- valueAtKeyChars? contents key
  parseNatListChars? value

/-- Parse a natural number matrix from the first `KEY=value` record. -/
def natMatrixAtKey? (contents key : String) : Option (List (List Nat)) := do
  let value <- valueAtKeyChars? contents key
  parseNatMatrixChars? value

def findLine : Nat -> List Char -> List Char -> Option (List Char)
  | 0, _, _ => none
  | fuel + 1, remainingText, needle =>
      match remainingText with
      | [] => none
      | _ =>
          let (line, afterLine) := takeLine remainingText
          if startsWithChars line needle then some line
          else findLine fuel afterLine needle

def splitWordsAux (currentReversed : List Char) :
    List Char -> List (List Char)
  | [] =>
      if currentReversed.isEmpty then [] else [currentReversed.reverse]
  | character :: remaining =>
      if character = ' ' then
        if currentReversed.isEmpty then splitWordsAux [] remaining
        else currentReversed.reverse :: splitWordsAux [] remaining
      else
        splitWordsAux (character :: currentReversed) remaining

/-- Parse a unique natural valued `field=value` token on the first line
beginning with `linePrefix`. -/
def lineNat? (contents linePrefix field : String) : Option Nat := do
  let line <- findLine parserFuel contents.toList linePrefix.toList
  let fieldPrefix := field.toList ++ ['=']
  let matching := (splitWordsAux [] line).filter
    (fun token => startsWithChars token fieldPrefix)
  let token <- match matching with
    | [token] => some token
    | _ => none
  parseNatChars? (<- dropPrefix? token fieldPrefix)

/-! These small checks exercise representative accepted and rejected parser
cases by kernel reduction.  They are deliberately not presented as a complete
parser-correctness proof or as provenance certificates for the embedded output
files. -/

theorem scalar_parser_smoke : natAtKey? "A=17\n" "A" = some 17 := by
  decide

theorem list_parser_smoke :
    natListAtKey? "A=[ 1, 2, 3 ]\n" "A" = some [1, 2, 3] := by
  decide

theorem matrix_parser_smoke :
    natMatrixAtKey? "A=[ [ 1, 0 ], [ 2, 3 ] ]\n" "A" =
      some [[1, 0], [2, 3]] := by
  decide

theorem line_parser_smoke :
    lineNat? "ROW id=4 total=9\n" "ROW id=4 " "total" = some 9 := by
  decide

theorem list_parser_rejects_missing_comma :
    parseNatList? "[1 2]" = none := by
  decide

theorem matrix_parser_rejects_missing_row_comma :
    parseNatMatrix? "[[1,2] [3,4]]" = none := by
  decide

theorem line_parser_rejects_tab_as_token_separator :
    lineNat? "ROW id=4\ttotal=9\n" "ROW id=4" "total" = none := by
  decide

end ModularRep.ComputationTranscriptPure


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
