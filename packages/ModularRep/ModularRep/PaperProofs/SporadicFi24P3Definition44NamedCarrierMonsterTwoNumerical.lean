import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierMonsterTwoSources
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCompleteCollapse

/-! Monster at two: actual fibre cancellation and the centreless criterion.
All nonprincipal counts are derived from actual small defect; the principal
count equality follows from the two totals and the actual block assignments. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierMonsterTwoNumerical

open ModularRep
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
  (ActualBlock WeightClass LiteralBlockSource DefectZeroReductionSource TrivialWeightSource NumericalBlockwiseAWC)
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllPairs
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBabyTwoSources
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierMonsterTwoSources
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFiniteFibres
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierDefinition41
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCompleteCollapse

universe u
variable {k K X : Type u}
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
variable (iota : PrimeRegularRootEmbedding 2 k K X)
variable (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (R : LiteralBlockSource (p := 2) (k := k) (K := K) (X := X))
variable (source : MonsterTwoSource iota hinj R)
variable (small : SmallDefectNumericalSource iota hinj R)

include source small

theorem nonprincipal_count_eq (b : ActualBlock (k := k) (X := X))
    (hb : b ≠ source.roles 0) :
    Nat.card (BrauerFibre iota hinj R b) = Nat.card (WeightFibre R b) := by
  obtain ⟨i, rfl⟩ := (source.roles_bijective iota hinj R).surjective b
  have hi : i ≠ 0 := fun h => hb (congrArg source.roles h)
  obtain ⟨D, hD, hcard⟩ := source.nonprincipal_defect i hi
  apply small.card_eq _ D hD
  rw [hcard]
  exact nonprincipal_defect_bound i hi

theorem principal_count_eq :
    Nat.card (BrauerFibre iota hinj R (source.roles 0)) =
      Nat.card (WeightFibre R (source.roles 0)) := by
  let := R.1.operations.ambientBlockData.fintypeBlock
  let := source.weight_finite iota hinj R
  exact card_fibre_eq_of_other_fibres (operationsBlock iota hinj R) R.1.weightBlock
    (source.roles 0) (source.total_card_eq iota hinj R)
    (nonprincipal_count_eq iota hinj R source small)

theorem principal_block_count_eq :
    Nat.card (BrauerFibre iota hinj R (operationsBlock iota hinj R
      (SporadicFi24P3Definition44Clause3ACWindow.trivialIBr iota))) =
      Nat.card (WeightFibre R (operationsBlock iota hinj R
        (SporadicFi24P3Definition44Clause3ACWindow.trivialIBr iota))) := by
  rw [← source.principal_role]
  exact principal_count_eq iota hinj R source small

theorem all_block_counts (b : ActualBlock (k := k) (X := X)) :
    Nat.card (BrauerFibre iota hinj R b) = Nat.card (WeightFibre R b) := by
  by_cases hb : b = source.roles 0
  · subst b
    exact principal_count_eq iota hinj R source small
  · exact nonprincipal_count_eq iota hinj R source small b hb

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

theorem exists_definition41_of_monster_two_sources
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

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierMonsterTwoNumerical



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
