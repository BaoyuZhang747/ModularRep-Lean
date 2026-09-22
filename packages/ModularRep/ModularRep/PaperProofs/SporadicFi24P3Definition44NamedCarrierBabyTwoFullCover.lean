import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBabyTwoNumerical
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierJ4FullCover

/-! Conditional Baby-at-two join from its actual full cover and literal
two-block source. The order-two kernel is removed in the universal 2'-cover. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBabyTwoFullCover

open ModularRep
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
  (ActualBlock LiteralBlockSource DefectZeroReductionSource TrivialWeightSource)
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSelfCover
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierJ4FullCover
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBabyTwoSources
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBabyTwoNumerical
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierDefinition41

universe u

def identityTwoPrimeCover_of_fullCover_kernel_card_two
    {U X : Type u} [Group U] [Group X] [Fintype X]
    (cover : U →* X) (hcover : IsUniversalCentralExtension cover)
    (hkernel : Nat.card cover.ker = 2)
    (hsimple : IsSimpleGroup X) (hnonabelian : ¬ IsMulCommutative X) :
    EllPrimeCoverSource 2 X :=
  identityEllPrimeCover_of_fullCover_pKernel (by decide) cover hcover
    (IsPGroup.of_card (n := 1) (by simpa using hkernel)) hsimple hnonabelian

variable {k K U X : Type u}
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [Group U] [Group X] [Fintype X]

theorem exists_definition41_of_full_cover_and_baby_two_sources
    (iota : PrimeRegularRootEmbedding 2 k K X)
    (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralBlockSource (p := 2) (k := k) (K := K) (X := X))
    (source : BabyTwoSource iota hinj R)
    (small : SmallDefectNumericalSource iota hinj R)
    (localReduction : ∀ (b : ActualBlock (k := k) (X := X)) (w : LiteralWeightFibre R.1 b),
      SelectedLocalReductionSource R.1 b w)
    (cover : U →* X) (hcover : IsUniversalCentralExtension cover)
    (hkernel : Nat.card cover.ker = 2)
    (hsimple : IsSimpleGroup X) (hnonabelian : ¬ IsMulCommutative X)
    (hOuter : Nat.card ((MulAut X)ᵐᵒᵖ ⧸
      (RepresentationWeight.innerInverseOpHom (G := X)).range) = 1)
    (D : DefectZeroReductionSource iota) (T : TrivialWeightSource (p := 2) (X := X))
    (compatibility : NavarroLocalReductionInflationBlockCompatibility.Source R.1.operations)
    (fieldSource : SpathCoefficientField 2 k iota.prime) :
    let Cover := identityTwoPrimeCover_of_fullCover_kernel_card_two
      cover hcover hkernel hsimple hnonabelian
    let hc := center_eq_bot_of_nonabelian_simple hsimple hnonabelian
    Nonempty (Definition41Witness iota hinj R localReduction Cover hc D T) := by
  exact exists_definition41_of_baby_two_sources iota hinj R source small localReduction
    (identityTwoPrimeCover_of_fullCover_kernel_card_two cover hcover hkernel hsimple hnonabelian)
    (center_eq_bot_of_nonabelian_simple hsimple hnonabelian)
    (allAutomorphismsInner_of_outer_card_one hOuter) D T compatibility fieldSource

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBabyTwoFullCover



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
