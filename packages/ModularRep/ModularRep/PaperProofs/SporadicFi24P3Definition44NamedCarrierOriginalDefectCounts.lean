import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalCompleteCollapse
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierJ4Numerical

/-! The actual cyclic/noncyclic defect split feeds the general original-
cover criterion. Both numerical branches refer to the same primitive
block and actual defect representative; no sector decomposition is added. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalDefectCounts

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalDefinition41
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalIdentityFamily
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalCompleteCollapse
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierJ4Numerical

universe u
variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

local instance brauerFintype (iota : PrimeRegularRootEmbedding p k K X) : Fintype (IBr iota) :=
  Fintype.ofFinite _

variable [Fintype (WeightClass (p := p) (K := K) (X := X))]

theorem exists_definition41_of_defect_counts
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralBlockSource (p := p) (k := k) (K := K) (X := X))
    (C : ∀ V : CharacterWeight p K X, CanonicalRawReduction iota V)
    (Cover : EllPrimeCoverSource p X) (allInner : AllAutomorphismsInner (X := X))
    (D : DefectZeroReductionSource iota) (T : TrivialWeightSource (p := p) (X := X))
    (source : CyclicNoncyclicNumericalSource iota hinj R)
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (lower : QuotientDataFamily iota hinj R C Cover)
    (fieldSource : SpathCoefficientField p k iota.prime) :
    Nonempty (Definition41Witness iota hinj R C Cover D T) :=
  exists_definition41_of_numerical iota hinj R C Cover allInner D T
    (numericalBlockwiseAWC iota hinj R source) compatibility lower fieldSource

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalDefectCounts


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
