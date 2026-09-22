import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalMonsterTwoNumerical
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierJ4FullCover

/-! Conditional Monster-at-two join on its actual centreless cover. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalMonsterTwoFullCover

open ModularRep
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
  (ActualBlock LiteralBlockSource DefectZeroReductionSource TrivialWeightSource)
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSelfCover
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierJ4FullCover
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBabyTwoSources
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierMonsterTwoSources
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalMonsterTwoNumerical
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalDefinition41

open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction

universe u

variable {k K U X : Type u}
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [Group U] [Group X] [Fintype X]

theorem exists_definition41_of_full_cover_and_monster_two_sources
    (iota : PrimeRegularRootEmbedding 2 k K X)
    (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralBlockSource (p := 2) (k := k) (K := K) (X := X))
    (source : MonsterTwoSource iota hinj R)
    (small : SmallDefectNumericalSource iota hinj R)
    (C : ∀ V : CharacterWeight 2 K X, CanonicalRawReduction iota V)
    (cover : U →* X) (hcover : IsUniversalCentralExtension cover)
    (hkernel : Nat.card cover.ker = 1)
    (hsimple : IsSimpleGroup X) (hnonabelian : ¬ IsMulCommutative X)
    (hOuter : Nat.card ((MulAut X)ᵐᵒᵖ ⧸
      (RepresentationWeight.innerInverseOpHom (G := X)).range) = 1)
    (D : DefectZeroReductionSource iota) (T : TrivialWeightSource (p := 2) (X := X))
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (fieldSource : SpathCoefficientField 2 k iota.prime) :
    let Cover := identityEllPrimeCover_of_fullCover_kernel_card_one
      iota.prime cover hcover hkernel hsimple hnonabelian
    let hc := center_eq_bot_of_nonabelian_simple hsimple hnonabelian
    Nonempty (Definition41Witness iota hinj R C Cover hc D T) := by
  exact SporadicFi24P3Definition44NamedCarrierCanonicalMonsterTwoNumerical.exists_definition41_of_monster_two_sources iota hinj R source small C
    (identityEllPrimeCover_of_fullCover_kernel_card_one
      iota.prime cover hcover hkernel hsimple hnonabelian)
    (center_eq_bot_of_nonabelian_simple hsimple hnonabelian)
    (allAutomorphismsInner_of_outer_card_one hOuter) D T compatibility fieldSource

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalMonsterTwoFullCover


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
