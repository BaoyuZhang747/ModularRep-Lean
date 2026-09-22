import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBabyTwoSources
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCompleteCollapse

/-! Baby at two: cancellation on actual character and weight fibres.
Only the nonprincipal small-defect count is external. The principal weight
count and all-block numerical criterion are derived from the literal census. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBabyTwoNumerical

open ModularRep
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
  (ActualBlock WeightClass LiteralBlockSource DefectZeroReductionSource TrivialWeightSource NumericalBlockwiseAWC)
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllPairs
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBabyTwoSources
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierDefinition41
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCompleteCollapse

universe u
variable {k K X : Type u}
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
variable (iota : PrimeRegularRootEmbedding 2 k K X)
variable (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (R : LiteralBlockSource (p := 2) (k := k) (K := K) (X := X))
variable (source : BabyTwoSource iota hinj R)
variable (small : SmallDefectNumericalSource iota hinj R)

include source small

theorem nonprincipal_count_eq :
    Nat.card (BrauerFibre iota hinj R (source.roles 1)) =
      Nat.card (WeightFibre R (source.roles 1)) := by
  obtain ⟨D, hD, hcard⟩ := source.nonprincipal_defect
  exact small.card_eq _ D hD (by omega)

theorem principal_counts :
    Nat.card (BrauerFibre iota hinj R (source.roles 0)) = 25 ∧
      Nat.card (WeightFibre R (source.roles 0)) = 25 ∧
      Nat.card (BrauerFibre iota hinj R (source.roles 0)) =
        Nat.card (WeightFibre R (source.roles 0)) := by
  have hRanks := source.brauer_ranks iota hinj R
  have hNonprincipal := nonprincipal_count_eq iota hinj R source small
  exact SporadicProposition57ComputationRelative.baby_two_principal_count_forced _ _ _ _
    (by omega)
    ((source.actual_weight_decomposition iota hinj R).symm.trans source.totalWeights)
    hRanks.2 (hNonprincipal.symm.trans hRanks.2)

theorem principal_weight_count :
    Nat.card (WeightFibre R (operationsBlock iota hinj R
      (SporadicFi24P3Definition44Clause3ACWindow.trivialIBr iota))) = 25 := by
  rw [← source.principal_role]
  exact (principal_counts iota hinj R source small).2.1

theorem all_block_counts (b : ActualBlock (k := k) (X := X)) :
    Nat.card (BrauerFibre iota hinj R b) = Nat.card (WeightFibre R b) := by
  rcases source.roles_cover iota hinj R b with rfl | rfl
  · exact (principal_counts iota hinj R source small).2.2
  · exact nonprincipal_count_eq iota hinj R source small

local instance brauerFintype : Fintype (IBr iota) := Fintype.ofFinite _

theorem numericalBlockwiseAWC [Fintype (WeightClass (p := 2) (K := K) (X := X))] :
    letI := R.1.operations.ambientBlockData.fintypeBlock
    NumericalBlockwiseAWC (iota := iota) (hinj := hinj)
      (blocks := R.1.operations.ambientBlockData.blocks) (R := R) := by
  classical
  let := R.1.operations.ambientBlockData.fintypeBlock
  intro b
  let e :
      {phi : IBr iota // SporadicCompleteCollapseLemma52Actual.brauerBlock
        (iota := iota) (hinj := hinj) (blocks := R.1.operations.ambientBlockData.blocks) phi = b} ≃
      BrauerFibre iota hinj R b :=
    Equiv.subtypeEquivRight (fun phi => by
      rw [operationsBlock_eq iota hinj R R.1.operations.ambientBlockData.blocks phi]
      rfl)
  simpa only [← Nat.card_eq_fintype_card] using
    (Nat.card_congr e).trans (all_block_counts iota hinj R source small b)

theorem exists_definition41_of_baby_two_sources
    (localReduction : ∀ (b : ActualBlock (k := k) (X := X)) (w : LiteralWeightFibre R.1 b),
      SelectedLocalReductionSource R.1 b w)
    (Cover : EllPrimeCoverSource 2 X) (hc : Subgroup.center X = ⊥)
    (allInner : SporadicCompleteCollapseLemma52Actual.AllAutomorphismsInner (X := X))
    (D : DefectZeroReductionSource iota) (T : TrivialWeightSource (p := 2) (X := X))
    (compatibility : NavarroLocalReductionInflationBlockCompatibility.Source R.1.operations)
    (fieldSource : SpathCoefficientField 2 k iota.prime) :
    Nonempty (Definition41Witness iota hinj R localReduction Cover hc D T) := by
  let := source.weight_finite iota hinj R
  let : Fintype (WeightClass (p := 2) (K := K) (X := X)) := Fintype.ofFinite _
  exact exists_definition41_of_numerical iota hinj R localReduction Cover hc allInner D T
    (numericalBlockwiseAWC iota hinj R source small) compatibility fieldSource

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBabyTwoNumerical


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
