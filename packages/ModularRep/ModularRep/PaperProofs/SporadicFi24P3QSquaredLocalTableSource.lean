import Mathlib.Data.ZMod.Basic
import ModularRep.BrauerReduction
import ModularRep.LocalNormalizerBrauerBlock

/-!
# A generic four row local table adapter at three for `Q` of order `3^2`

This file defines a generic, nonexhaustive rowwise adapter for an arbitrary
finite group `X` and subgroup `Q`.  It is intended to model four named table
rows arising in the `Fi'_24` calculation at three, but it neither constructs a
literal `Fi'_24` group or subgroup nor connects `printedRow` to the tracked
computation transcript.  A concrete use must separately supply every
identification between the external table and the literal Lean carriers.

The `Source` takes only fixed-`Q` quotient block, inflation, and normaliser
decomposition operations.  Constructing those operations still requires the
corresponding external local block data, but it requires no ambient block or
all-weight block-induction package.

The four rows are not asserted to exhaust a normaliser block, a radical
subgroup fibre, or a Fischer block fibre.  This file does not construct a
selected weight, instantiate the universal Navarro compatibility source,
invoke block induction, or prove BAW or iBAW.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3QSquaredLocalTableSource

open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero

universe u

variable {k K X : Type u}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

/-! The six entries in each list are, in order, the quotient ordinary character
row position, its degree, the quotient block index, the inflated local ordinary
character row position, the local block index, and the decomposition matrix
column position.  They are provenance labels only, not Lean characters or
primitive idempotents, and no theorem below identifies them with the tracked
computation transcript. -/

inductive P3QSquaredTableRow
  | r23 | r24 | r51 | r52
  deriving DecidableEq, Repr

def printedRow : P3QSquaredTableRow → List Nat
  | .r23 => [23, 729, 2, 23, 2, 8]
  | .r24 => [24, 729, 3, 24, 2, 9]
  | .r51 => [51, 729, 5, 51, 2, 18]
  | .r52 => [52, 729, 6, 52, 2, 17]

/-- Separately supplied rowwise carrier hypotheses for an arbitrary `X` and `Q`.

The radical and elementary abelian assertions have E2/U provenance.  The
character, reduction, and literal block identifications have E1/E3/U
provenance.  This structure does not construct an `Fi'_24` instance or connect
`printedRow` to an external table.  Its operations argument contains only the
fixed-`Q` local data described above.  The structure makes no coverage claim,
and its fields are not a universal local compatibility law. -/
structure Source
    (Q : Subgroup X)
    (operations : LocalNormalizerBlockOperations
      (p := 3) (k := k) (K := K) (G := X) Q) where
  q_radical : IsRadicalSubgroup 3 Q
  q_elementary : Q ≃* Multiplicative (Fin 2 → ZMod 3)
  ordinary :
    P3QSquaredTableRow →
      OrdinaryIrreducibleCharacter.Irr K (NormalizerQuotient Q)
  ordinary_defectZero :
    ∀ r, IsDefectZeroOrdinaryCharacter 3 (ordinary r)
  ordinary_injective : Function.Injective ordinary
  quotientBlock :
    P3QSquaredTableRow → LocalQuotientBlock (k := k) Q
  quotientBlock_injective : Function.Injective quotientBlock
  quotientBlock_of_ordinary :
    ∀ r, operations.localCharacterBlock (ordinary r)
      (ordinary_defectZero r) = quotientBlock r
  normalizerRoot : PrimeRegularRootEmbedding 3 k K
    (Subgroup.normalizer (Q : Set X))
  normalizerBrauer : P3QSquaredTableRow → IBr normalizerRoot
  normalizerBrauer_injective : Function.Injective normalizerBrauer
  reduction :
    ∀ r, NormalizerInflatedReduction Q (ordinary r)
      normalizerRoot (normalizerBrauer r)
  normalizerBlock : InflatedNormalizerBlock (k := k) Q
  normalizerBlock_of_brauer :
    ∀ r,
      operations.normalizerBrauerBlock normalizerRoot
        (normalizerBrauer r) = normalizerBlock
  inflated_quotientBlock :
    ∀ r,
      operations.inflateToNormalizer (quotientBlock r) = normalizerBlock

namespace Source

variable {Q : Subgroup X}
variable {operations : LocalNormalizerBlockOperations
  (p := 3) (k := k) (K := K) (G := X) Q}

/-- Each supplied normaliser Brauer character is the pointwise reduction of
the inflation of its supplied defect zero quotient character. -/
theorem normalizerReduction
    (S : Source Q operations) (r : P3QSquaredTableRow) :
    NormalizerInflatedReduction Q (S.ordinary r) S.normalizerRoot
      (S.normalizerBrauer r) := by
  exact S.reduction r

/-- For each supplied row, the block selected from the literal normaliser
decomposition is the inflation of the block of its defect zero quotient
character. -/
theorem normalizerBlock_eq_inflate
    (S : Source Q operations) (r : P3QSquaredTableRow) :
    operations.normalizerBrauerBlock S.normalizerRoot
        (S.normalizerBrauer r) =
      operations.inflateToNormalizer
        (operations.localCharacterBlock (S.ordinary r)
          (S.ordinary_defectZero r)) := by
  calc
    operations.normalizerBrauerBlock S.normalizerRoot
        (S.normalizerBrauer r) = S.normalizerBlock :=
      S.normalizerBlock_of_brauer r
    _ = operations.inflateToNormalizer (S.quotientBlock r) :=
      (S.inflated_quotientBlock r).symm
    _ = operations.inflateToNormalizer
        (operations.localCharacterBlock (S.ordinary r)
          (S.ordinary_defectZero r)) :=
      congrArg operations.inflateToNormalizer
        (S.quotientBlock_of_ordinary r).symm

end Source

end ModularRep.PaperProofs.SporadicFi24P3QSquaredLocalTableSource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
