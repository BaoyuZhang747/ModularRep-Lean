import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierMonsterTwoNumerical
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierMonsterTwoSources
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalCompleteCollapse

/-! Monster at two: actual fibre cancellation and the centreless criterion.
All nonprincipal counts are derived from actual small defect; the principal
count equality follows from the two totals and the actual block assignments. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalMonsterTwoNumerical

open ModularRep
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
  (ActualBlock WeightClass LiteralBlockSource DefectZeroReductionSource TrivialWeightSource NumericalBlockwiseAWC)
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllPairs
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBabyTwoSources
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierMonsterTwoSources
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFiniteFibres
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalDefinition41
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalCompleteCollapse

open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierMonsterTwoNumerical
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction

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

local instance brauerFintype : Fintype (IBr iota) := Fintype.ofFinite _

theorem exists_definition41_of_monster_two_sources
    (C : ∀ V : CharacterWeight 2 K X, CanonicalRawReduction iota V)
    (Cover : EllPrimeCoverSource 2 X) (hc : Subgroup.center X = ⊥)
    (allInner : SporadicCompleteCollapseLemma52Actual.AllAutomorphismsInner (X := X))
    (D : DefectZeroReductionSource iota) (T : TrivialWeightSource (p := 2) (X := X))
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (fieldSource : SpathCoefficientField 2 k iota.prime) :
    Nonempty (Definition41Witness iota hinj R C Cover hc D T) := by
  let := source.weight_finite iota hinj R
  let : Fintype (WeightClass (p := 2) (K := K) (X := X)) := Fintype.ofFinite _
  exact exists_definition41_of_numerical iota hinj R C Cover hc allInner D T
    (numericalBlockwiseAWC iota hinj R source small) compatibility fieldSource

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalMonsterTwoNumerical



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
