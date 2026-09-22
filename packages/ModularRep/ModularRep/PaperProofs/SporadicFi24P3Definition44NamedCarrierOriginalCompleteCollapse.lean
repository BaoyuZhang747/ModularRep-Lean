import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalIdentityFamily
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalTrivialBlock
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalIdentityFamily

/-! Complete collapse for the original perfect prime-to-p cover, including
nontrivial centre. One numerical correspondence supplies every raw match;
all packets are constructed from the same unselected quotient data. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalCompleteCollapse

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllPairs
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalTrivialBlock
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalDefinition41
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalIdentityFamily

universe u
variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

local instance brauerFintype (iota : PrimeRegularRootEmbedding p k K X) : Fintype (IBr iota) :=
  Fintype.ofFinite _

variable [Fintype (WeightClass (p := p) (K := K) (X := X))]

theorem exists_definition41_of_numerical
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralBlockSource (p := p) (k := k) (K := K) (X := X))
    (C : ∀ V : CharacterWeight p K X, CanonicalRawReduction iota V)
    (Cover : EllPrimeCoverSource p X)
    (allInner : AllAutomorphismsInner (X := X))
    (D : DefectZeroReductionSource iota) (T : TrivialWeightSource (p := p) (X := X))
    (hAWC :
      letI := R.1.operations.ambientBlockData.fintypeBlock
      NumericalBlockwiseAWC (iota := iota) (hinj := hinj)
        (blocks := R.1.operations.ambientBlockData.blocks) (R := R))
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (lower : QuotientDataFamily iota hinj R C Cover)
    (fieldSource : SpathCoefficientField p k iota.prime) :
    Nonempty (Definition41Witness iota hinj R C Cover D T) := by
  let := R.1.operations.ambientBlockData.fintypeBlock
  let : Finite (GlobalDefectZeroCharacter (p := p) (K := K) (X := X)) :=
    Finite.of_injective (D.reduce (iota := iota)) (D.reduce_injective (iota := iota))
  let : Fintype (GlobalDefectZeroCharacter (p := p) (K := K) (X := X)) := Fintype.ofFinite _
  let blocks := R.1.operations.ambientBlockData.blocks
  let Cblock := trivialWeightBlockCompatibilityOfCanonicalOperations iota hinj R C D T compatibility
  let TI := SporadicFi24P3Definition44NamedCarrierCanonicalIdentityFamily.trivialWeightIdentification (K := K) T
  let Omega := globalEquiv (iota := iota) (hinj := hinj) (blocks := blocks)
    (R := R) (D := D) (T := T) (C := Cblock) TI hAWC
  refine ⟨ofNormalizedEquiv iota hinj R C Cover allInner D T
    Omega ?_ ?_ compatibility lower fieldSource⟩
  · intro phi
    exact (globalEquiv_block_preserving
      (iota := iota) (hinj := hinj) (blocks := blocks)
      (R := R) (D := D) (T := T) (C := Cblock) (TI := TI) (hAWC := hAWC) phi).trans
      (operationsBlock_eq iota hinj R blocks phi).symm
  · exact globalEquiv_normalisation
      (iota := iota) (hinj := hinj) (blocks := blocks)
      (R := R) (D := D) (T := T) (C := Cblock) (TI := TI) (hAWC := hAWC)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalCompleteCollapse


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
