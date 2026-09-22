import ModularRep.PaperProofs.ComputationTranscriptActual
import ModularRep.PaperProofs.ComputationTranscriptAdditionalBindings
import Mathlib.Tactic

/-!
# Selected numerical consequences near Proposition 5.7

This endpoint proves selected finite numerical deductions directly from the
public definitions parsed from the current computation transcripts.  It is
not a formalisation of Proposition 5.7.  It proves no instance of AWC or iBAW.

The trust boundary is deliberately visible.  Finite numerical values copied
from a published table or count are E3 data.  A cited theorem identifying two
mathematical counts is an E2 input.  The assertion that a transcript row or
identifier represents a named mathematical block is a U carrier input.  The
kernel checks the remaining list manipulation and arithmetic.

At three for `Fi'_24`, the endpoint compares only the numerical orbit data in
three printed transcript rows with the numerical entries in the corrected
published table.  It does not identify those rows with mathematical blocks or
sectors and does not assert that they are complete.  The endpoint does not
treat the faithful rows at two, the case at seven, the larger-prime
empty-noncyclic checks, the corresponding Baby Monster and Monster odd-prime
reductions, or the `J_4` branch.  The correctness of GAP and the character
tables, completeness of searches, and the semantic interpretation of the
current files also remain external.
-/

namespace ModularRep.PaperProofs

open ModularRep.PaperProofs.ComputationTranscriptActual
open ModularRep.PaperProofs.ComputationTranscriptAdditionalBindings
open ModularRep.PaperProofs.SporadicProposition57ComputationRelative
open Formalisation.C2Cancellation

/-! ## External source and carrier interfaces -/

/-- Inputs for the Baby Monster subtraction.

`publishedTotalWeightCount` is E3 finite data.  `nonprincipalCountEquality`
is the E2 theorem input.  `transcriptBlockAlignment` is U: it identifies the
two rows in `baby.out` with the principal and nonprincipal mathematical
blocks, in that order. -/
structure BabySubtractionInputs where
  totalWeightCount : Nat
  nonprincipalWeightCount : Nat
  principalBrauerCount : Nat
  nonprincipalBrauerCount : Nat
  publishedTotalWeightCount : totalWeightCount = 27
  nonprincipalCountEquality :
    nonprincipalBrauerCount = nonprincipalWeightCount
  transcriptBlockAlignment :
    babyBrauerBlockRanksFromTranscript =
      [principalBrauerCount, nonprincipalBrauerCount]

def BabySubtractionInputs.principalWeightResidual
    (source : BabySubtractionInputs) : Nat :=
  source.totalWeightCount - source.nonprincipalWeightCount

/-- Inputs for the Monster cancellation.

The total `61` is E3 finite data and the equality for the defect-four block is
E2.  The two decomposition equalities are composite E1/E2/E3/U inputs.  They
package the regular-class interpretation, the exhaustive block census and
local block facts, the published finite totals, and the allocation of the
printed contributions to named mathematical blocks.  K credit begins only
with cancellation from these explicit equations. -/
structure MonsterCancellationInputs where
  totalWeightCount : Nat
  principalBrauerCount : Nat
  principalWeightCount : Nat
  defectFourBrauerCount : Nat
  defectFourWeightCount : Nat
  publishedTotalWeightCount : totalWeightCount = 61
  defectFourCountEquality : defectFourBrauerCount = defectFourWeightCount
  brauerBlockDecomposition :
    principalBrauerCount + defectFourBrauerCount +
        monsterDefectZeroLabelsFromTranscript.length =
      monsterRegularClassCountFromTranscript
  weightBlockDecomposition :
    principalWeightCount + defectFourWeightCount +
        monsterDefectZeroLabelsFromTranscript.length = totalWeightCount

/-- A signature records `(total points, fixed points)` for an involution. -/
abbrev InvolutionSignature := Nat × Nat

def sumSignatures (rows : List InvolutionSignature) : InvolutionSignature :=
  ((rows.map Prod.fst).sum, (rows.map Prod.snd).sum)

def fi24TwoSignaturesFromTranscript : List InvolutionSignature :=
  fi24TwoSelectedRowsFromTranscript.map fun row => (row.1, row.2.1)

/-- The twelve entries in the `3`-part of the corrected An--Dietrich Table 8,
in table order.  This is E3 source data.  The definition records only the
published `(fixed,nonfixed)` numbers and gives them no block or sector
interpretation. -/
def fi24Table8AtThree : List TableSignatureEntry :=
  [⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩,
   ⟨2, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨4, 0⟩, ⟨4, 0⟩, ⟨8, 0⟩]

/-- Orbit data `(fixed points,two-element orbits)` obtained by adding the
three literal transcript rows. -/
def fi24ThreeTranscriptOrbitData : C2OrbitData :=
  ((fi24ThreePrintedRowsFromTranscript.map fun row => row.2.1).sum,
    (fi24ThreePrintedRowsFromTranscript.map fun row => row.2.2).sum)

/-- Orbit data obtained from the raw table entries.  Evenness of every
`nonfixed` entry is checked in `fi24ThreeLiteralOrbitDataAgreement`. -/
def fi24ThreeTableOrbitData : C2OrbitData :=
  ((fi24Table8AtThree.map TableSignatureEntry.fixed).sum,
    (fi24Table8AtThree.map fun entry => entry.nonfixed / 2).sum)

/-- Orbit data in the second and third printed transcript rows.  No
mathematical meaning is attached to this raw row order. -/
def fi24ThreeOtherPrintedOrbitData : C2OrbitData :=
  let rows := fi24ThreePrintedRowsFromTranscript.drop 1
  ((rows.map fun row => row.2.1).sum,
    (rows.map fun row => row.2.2).sum)

/-- Inputs for the cancellation at two for `Fi'_24`.

The 34-entry list `correctedFi24Table8AtTwo` is the E3 datum transcribed from
the corrected published table; its sum is proved in the existing K theorem
`correctedFi24Table8AtTwo_signature_sum`.  The defect-four and defect-zero
signatures below are composite E2/E3/U data: the cited blockwise results and
finite tables supply the values, while their allocation is U.  The
three-point orbit cardinality and its two known fixed points are likewise
explicit E2/E3/U inputs.  Lean derives its signature `(3,3)` by the
involution-parity theorem instead of accepting that signature.
`principalRowAlignment` is U: it says that the first of the three parsed rows
is the principal block row. -/
structure Fi24TwoCancellationInputs where
  principalBrauerSignature : InvolutionSignature
  defectFourWeightSignature : InvolutionSignature
  defectZeroWeightSignatures : List InvolutionSignature
  threePointOrbitData : C2OrbitData
  principalRowAlignment :
    fi24TwoSignaturesFromTranscript.head? = some principalBrauerSignature
  defectFourSignatureData : defectFourWeightSignature = (3, 1)
  defectZeroSignatureData : defectZeroWeightSignatures = [(1, 1), (1, 1)]
  threePointCard : card threePointOrbitData = 3
  threePointKnownFixed : 2 ≤ fixedOrbits threePointOrbitData

def Fi24TwoCancellationInputs.otherBlockWeightSignatures
    (source : Fi24TwoCancellationInputs) : List InvolutionSignature :=
  [source.defectFourWeightSignature,
    signature source.threePointOrbitData] ++
    source.defectZeroWeightSignatures

structure SporadicExternalInputs where
  baby : BabySubtractionInputs
  monster : MonsterCancellationInputs
  fi24Two : Fi24TwoCancellationInputs

/-! ## Literal transcript projections -/

def oneBasedZeroPositionsAux : List Nat → Nat → List Nat
  | [], _ => []
  | value :: values, position =>
      (if value = 0 then [position] else []) ++
        oneBasedZeroPositionsAux values (position + 1)

def oneBasedZeroPositions (values : List Nat) : List Nat :=
  oneBasedZeroPositionsAux values 1

def valuesAtOneBasedPositionsAux (positions : List Nat) :
    List Nat → Nat → List Nat
  | [], _ => []
  | value :: values, position =>
      (if positions.contains position then [value] else []) ++
        valuesAtOneBasedPositionsAux positions values (position + 1)

def valuesAtOneBasedPositions
    (positions values : List Nat) : List Nat :=
  valuesAtOneBasedPositionsAux positions values 1

def monsterDefectZeroPositionsFromTranscript : List Nat :=
  oneBasedZeroPositions monsterBlockDefectsFromTranscript

def monsterDefectZeroOrdinaryCountsFromTranscript : List Nat :=
  valuesAtOneBasedPositions monsterDefectZeroPositionsFromTranscript
    monsterOrdinaryBlockCountsFromTranscript

def fi24FiveSignatureRowsTotal
    (rows : List SignatureRow) : Nat :=
  (rows.map fun row => row.2.1).sum

def fi24FiveCountRowsTotal (rows : List CountRow) : Nat :=
  (rows.map Prod.snd).sum

def fi24FiveCountRowsTotalFor
    (blockIds : List Nat) (rows : List CountRow) : Nat :=
  ((rows.filter fun row => blockIds.contains row.1).map Prod.snd).sum

def fi24TwoSectorSignatureFromCorrectedTable : InvolutionSignature :=
  ((correctedFi24Table8AtTwo.map TableSignatureEntry.total).sum,
    (correctedFi24Table8AtTwo.map TableSignatureEntry.fixed).sum)

def Fi24TwoCancellationInputs.principalWeightResidual
    (source : Fi24TwoCancellationInputs) : InvolutionSignature :=
  (fi24TwoSectorSignatureFromCorrectedTable.1 -
      (sumSignatures source.otherBlockWeightSignatures).1,
    fi24TwoSectorSignatureFromCorrectedTable.2 -
      (sumSignatures source.otherBlockWeightSignatures).2)

/-! ## Individually audited deductions -/

theorem babyPrincipalResidualFromTranscript
    (source : BabySubtractionInputs) :
    babyRegularClassCountFromTranscript = source.totalWeightCount ∧
      source.principalBrauerCount = source.principalWeightResidual := by
  have hRegular : babyRegularClassCountFromTranscript = 27 := by decide
  have hRows : babyBrauerBlockRanksFromTranscript = [25, 2] := by decide
  have hAlignment := source.transcriptBlockAlignment
  rw [hRows] at hAlignment
  have hCounts :
      source.principalBrauerCount = 25 ∧
        source.nonprincipalBrauerCount = 2 := by
    simpa using hAlignment.symm
  rcases hCounts with ⟨hPrincipal, hNonprincipalBrauer⟩
  have hTotalWeights := source.publishedTotalWeightCount
  have hNonprincipal := source.nonprincipalCountEquality
  constructor
  · exact hRegular.trans source.publishedTotalWeightCount.symm
  · rw [BabySubtractionInputs.principalWeightResidual]
    omega

theorem babySevenNumericalRowsFromTranscript :
    babySevenRegularClassCountFromTranscript = 222 ∧
      babySevenRestrictionRanksFromTranscript = [24, 24, 21, 24] := by
  decide

theorem monsterDefectZeroRowsFromTranscript :
    monsterDefectZeroPositionsFromTranscript = [2, 3, 5] ∧
      monsterDefectZeroLabelsFromTranscript =
        monsterDefectZeroPositionsFromTranscript ∧
      monsterDefectZeroOrdinaryCountsFromTranscript = [1, 1, 1] := by
  decide

theorem monsterPrincipalCancellationFromTranscript
    (source : MonsterCancellationInputs) :
    source.principalBrauerCount = source.principalWeightCount := by
  have hRegular : monsterRegularClassCountFromTranscript = 61 := by decide
  have hDefectZero : monsterDefectZeroLabelsFromTranscript.length = 3 := by
    decide
  have hTotal : source.totalWeightCount =
      monsterRegularClassCountFromTranscript :=
    source.publishedTotalWeightCount.trans hRegular.symm
  have hBrauer := source.brauerBlockDecomposition
  have hWeight := source.weightBlockDecomposition
  have hDefectFour := source.defectFourCountEquality
  omega

theorem fi24TwoNumericalRowsFromTranscript :
    fi24TwoSelectedRowsFromTranscript =
        [(33, 25, 4), (3, 1, 1), (3, 3, 0)] ∧
      (∀ row ∈ fi24TwoSelectedRowsFromTranscript,
        row.1 = row.2.1 + 2 * row.2.2) := by
  decide

theorem fi24TwoPrincipalResidualFromTranscript
    (source : Fi24TwoCancellationInputs) :
    source.principalBrauerSignature = source.principalWeightResidual := by
  have hParsed : fi24TwoSignaturesFromTranscript.head? = some (33, 25) := by
    decide
  have hPrincipalAlignment := source.principalRowAlignment
  rw [hParsed] at hPrincipalAlignment
  have hPrincipal : source.principalBrauerSignature = (33, 25) := by
    exact Option.some.inj hPrincipalAlignment.symm
  have hTable := correctedFi24Table8AtTwo_signature_sum
  have hThreePoint := three_weights_two_fixed_force_all_fixed
    source.threePointOrbitData source.threePointCard source.threePointKnownFixed
  have hResidual : source.principalWeightResidual = (33, 25) := by
    rw [Fi24TwoCancellationInputs.principalWeightResidual,
      fi24TwoSectorSignatureFromCorrectedTable,
      Fi24TwoCancellationInputs.otherBlockWeightSignatures,
      source.defectFourSignatureData, source.defectZeroSignatureData,
      hThreePoint]
    rw [hTable.1, hTable.2]
    decide
  exact hPrincipal.trans hResidual.symm

/-- A label-neutral comparison of the literal `Fi'_24` data at three.

The table entries and the transcript numerals are E3 inputs, while embedding
and parsing the transcript are build provenance.  The kernel checks the row
arithmetic, evenness, orbit-data sum, and residual.  Nothing here identifies
the printed rows with blocks or sectors, proves that they are exhaustive, or
establishes AWC, iBAW, or Proposition 5.7. -/
structure Fi24ThreeLiteralConsequences : Prop where
  printedRowsExact :
    fi24ThreePrintedRowsFromTranscript =
      [(25, 25, 0), (4, 2, 1), (1, 1, 0)]
  rowOrbitArithmetic :
    ∀ row ∈ fi24ThreePrintedRowsFromTranscript,
      row.1 = row.2.1 + 2 * row.2.2
  tableLength : fi24Table8AtThree.length = 12
  tableNonfixedEven :
    ∀ entry ∈ fi24Table8AtThree, Even entry.nonfixed
  orbitDataAgreement :
    fi24ThreeTranscriptOrbitData = fi24ThreeTableOrbitData
  totalOrbitData : fi24ThreeTranscriptOrbitData = (28, 1)
  totalSignature : signature fi24ThreeTranscriptOrbitData = (30, 28)
  firstPrintedResidual :
    signature
      (fi24ThreeTranscriptOrbitData.1 -
          fi24ThreeOtherPrintedOrbitData.1,
        fi24ThreeTranscriptOrbitData.2 -
          fi24ThreeOtherPrintedOrbitData.2) = (25, 25)

theorem fi24ThreeLiteralOrbitDataAgreement :
    Fi24ThreeLiteralConsequences := by
  exact
    { printedRowsExact := by decide
      rowOrbitArithmetic := by decide
      tableLength := by decide
      tableNonfixedEven := by decide
      orbitDataAgreement := by decide
      totalOrbitData := by decide
      totalSignature := by decide
      firstPrintedResidual := by decide }

/-- Literal comparisons between the rows carrying the same printed
identifiers in the two current `Fi'_24` transcripts.  The row groups
`[45,47]` and `[46,48]` and the decoded action are intentionally not called
faithful sectors or mathematical block orbits here.  Those interpretations,
and the assertion that an identifier in one file denotes the same block as
the identifier in the other file, remain U. -/
structure Fi24FiveLiteralConsequences : Prop where
  trivialRowsEqual :
    fi24FiveBrauerTrivialRowsFromTranscript =
      fi24FiveWeightTrivialRowsFromTranscript
  trivialRowTotals :
    fi24FiveSignatureRowsTotal fi24FiveBrauerTrivialRowsFromTranscript = 46 ∧
      fi24FiveSignatureRowsTotal fi24FiveWeightTrivialRowsFromTranscript = 46
  coverRowsEqual :
    fi24FiveBrauerCoverRowsFromTranscript =
      fi24FiveWeightCoverRowsFromTranscript
  coverRowTotals :
    fi24FiveCountRowsTotal fi24FiveBrauerCoverRowsFromTranscript = 106 ∧
      fi24FiveCountRowsTotal fi24FiveWeightCoverRowsFromTranscript = 106
  printedIdGroupTotals :
    fi24FiveCountRowsTotalFor [45, 47]
        fi24FiveWeightCoverRowsFromTranscript = 30 ∧
      fi24FiveCountRowsTotalFor [46, 48]
        fi24FiveWeightCoverRowsFromTranscript = 30
  decodedActionOnPositions45To48 :
    fi24FaithfulFiveOuterFromTranscript .b45 = some .b46 ∧
      fi24FaithfulFiveOuterFromTranscript .b46 = some .b45 ∧
      fi24FaithfulFiveOuterFromTranscript .b47 = some .b48 ∧
      fi24FaithfulFiveOuterFromTranscript .b48 = some .b47
  decodedActionHasNoFixedPosition :
    ∀ block, fi24FaithfulFiveOuterFromTranscript block ≠ some block

theorem fi24FiveParsedComparisonAndAction :
    Fi24FiveLiteralConsequences := by
  refine
    { trivialRowsEqual := by decide
      trivialRowTotals := by decide
      coverRowsEqual := by decide
      coverRowTotals := by decide
      printedIdGroupTotals := by decide
      decodedActionOnPositions45To48 := by decide
      decodedActionHasNoFixedPosition := ?_ }
  intro block
  cases block <;> decide

/-! ## Selected endpoint -/

/-- A packaging of only the selected numerical consequences above.  This
structure is not a certificate for Proposition 5.7. -/
structure SporadicTranscriptConsequences
    (source : SporadicExternalInputs) : Prop where
  babyResidual :
    babyRegularClassCountFromTranscript = source.baby.totalWeightCount ∧
      source.baby.principalBrauerCount =
        source.baby.principalWeightResidual
  babySevenRows :
    babySevenRegularClassCountFromTranscript = 222 ∧
      babySevenRestrictionRanksFromTranscript = [24, 24, 21, 24]
  monsterDefectZeroRows :
    monsterDefectZeroPositionsFromTranscript = [2, 3, 5] ∧
      monsterDefectZeroLabelsFromTranscript =
        monsterDefectZeroPositionsFromTranscript ∧
      monsterDefectZeroOrdinaryCountsFromTranscript = [1, 1, 1]
  monsterCancellation :
    source.monster.principalBrauerCount =
      source.monster.principalWeightCount
  fi24TwoRows :
    fi24TwoSelectedRowsFromTranscript =
        [(33, 25, 4), (3, 1, 1), (3, 3, 0)] ∧
      (∀ row ∈ fi24TwoSelectedRowsFromTranscript,
        row.1 = row.2.1 + 2 * row.2.2)
  fi24TwoResidual :
    source.fi24Two.principalBrauerSignature =
      source.fi24Two.principalWeightResidual
  fi24ThreeLiteral : Fi24ThreeLiteralConsequences
  fi24FiveRowsAndAction : Fi24FiveLiteralConsequences

theorem selectedSporadicTranscriptConsequences
    (source : SporadicExternalInputs) :
    SporadicTranscriptConsequences source where
  babyResidual := babyPrincipalResidualFromTranscript source.baby
  babySevenRows := babySevenNumericalRowsFromTranscript
  monsterDefectZeroRows := monsterDefectZeroRowsFromTranscript
  monsterCancellation :=
    monsterPrincipalCancellationFromTranscript source.monster
  fi24TwoRows := fi24TwoNumericalRowsFromTranscript
  fi24TwoResidual := fi24TwoPrincipalResidualFromTranscript source.fi24Two
  fi24ThreeLiteral := fi24ThreeLiteralOrbitDataAgreement
  fi24FiveRowsAndAction := fi24FiveParsedComparisonAndAction

end ModularRep.PaperProofs


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
