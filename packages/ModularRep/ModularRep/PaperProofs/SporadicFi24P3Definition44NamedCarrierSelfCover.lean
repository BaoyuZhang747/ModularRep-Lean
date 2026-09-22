import ModularRep.PaperProofs.EvenFieldFLZSourceConditions
import ModularRep.PaperProofs.EvenFieldUniversalCentralCoverSource
import Mathlib.GroupTheory.PGroup

/-!
# A full cover with p-group kernel gives the identity p'-cover

The universal property factors through its p-group kernel when the target
extension has prime-to-p kernel. Perfectness makes the resulting section
surjective. For Fi'24 at p=3 the remaining source binding is the actual full
covering map and its kernel order three (An--Dietrich, Appendix A.2/Table 1,
printed p.337). A table entry alone does not identify an arbitrary map.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSelfCover

open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions

universe u

theorem hom_eq_one_of_pGroup_of_primeTo_card
    {p : ℕ} (hp : p.Prime) {A B : Type u} [Group A] [Group B]
    (hA : IsPGroup p A) (hB : ¬ p ∣ Nat.card B)
    (f : A →* B) (a : A) : f a = 1 := by
  obtain ⟨n, hn⟩ := hA.exists_orderOf_dvd_pow a
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes
    ((hp.coprime_iff_not_dvd.mpr hB).symm.pow_right n)
    (orderOf_dvd_natCard (f a)) ((orderOf_map_dvd f a).trans hn)

theorem exists_surjective_section_of_fullCover_pKernel
    {p : ℕ} (hp : p.Prime)
    {U X D : Type u} [Group U] [Group X] [Group D]
    (cover : U →* X) (hcover : IsUniversalCentralExtension cover)
    (hkernel : IsPGroup p cover.ker)
    (f : D →* X) (hsurjective : Function.Surjective f)
    (hcentral : f.ker ≤ Subgroup.center D)
    (hperfect : commutator D = ⊤) (hprimeTo : ¬ p ∣ Nat.card f.ker) :
    ∃ s : X →* D, Function.Surjective s ∧ f.comp s = MonoidHom.id X := by
  obtain ⟨lift, hlift, _⟩ := hcover.2 D f ⟨hsurjective, hcentral⟩
  let kernelLift : cover.ker →* f.ker := {
    toFun := fun x => ⟨lift x, by
      change f (lift x.1) = 1
      exact (DFunLike.congr_fun hlift x.1).trans x.property⟩
    map_one' := by apply Subtype.ext; exact lift.map_one
    map_mul' := by intro a b; apply Subtype.ext; exact lift.map_mul a b }
  have hdescend : cover.ker ≤ lift.ker := by
    intro x hx
    change lift x = 1
    exact congrArg Subtype.val
      (hom_eq_one_of_pGroup_of_primeTo_card hp hkernel hprimeTo kernelLift ⟨x, hx⟩)
  let quotientLift : U ⧸ cover.ker →* D := QuotientGroup.lift cover.ker lift hdescend
  let quotientEquiv : U ⧸ cover.ker ≃* X :=
    QuotientGroup.quotientKerEquivOfSurjective cover hcover.1.1
  let s : X →* D := quotientLift.comp quotientEquiv.symm.toMonoidHom
  have hsection : f.comp s = MonoidHom.id X := by
    ext y
    obtain ⟨x, rfl⟩ := hcover.1.1 y
    have he : quotientEquiv (QuotientGroup.mk x) = cover x := rfl
    have hes : quotientEquiv.symm (cover x) = QuotientGroup.mk x := by
      rw [← he, quotientEquiv.symm_apply_apply]
    change f (quotientLift (quotientEquiv.symm (cover x))) = cover x
    rw [hes]
    change f (lift x) = cover x
    exact DFunLike.congr_fun hlift x
  exact ⟨s, centralExtension_section_surjective f hcentral s hsection hperfect, hsection⟩

theorem perfect_of_nonabelian_simple
    {X : Type u} [Group X] (hsimple : IsSimpleGroup X)
    (hnonabelian : ¬ IsMulCommutative X) : commutator X = ⊤ := by
  let : IsSimpleGroup X := hsimple
  have hnormal : (commutator X).Normal := inferInstance
  exact hnormal.eq_bot_or_eq_top.resolve_left
    (fun h => hnonabelian ((commutator_eq_bot_iff _).mp h))

theorem center_eq_bot_of_nonabelian_simple
    {X : Type u} [Group X] (hsimple : IsSimpleGroup X)
    (hnonabelian : ¬ IsMulCommutative X) : Subgroup.center X = ⊥ := by
  let : IsSimpleGroup X := hsimple
  have hnormal : (Subgroup.center X).Normal := inferInstance
  exact hnormal.eq_bot_or_eq_top.resolve_right
    (fun h => hnonabelian (Subgroup.center_eq_top_iff.mp h))

def identityEllPrimeCover_of_fullCover_pKernel
    {p : ℕ} (hp : p.Prime)
    {U X : Type u} [Group U] [Group X] [Fintype X]
    (cover : U →* X) (hcover : IsUniversalCentralExtension cover)
    (hkernel : IsPGroup p cover.ker)
    (hsimple : IsSimpleGroup X) (hnonabelian : ¬ IsMulCommutative X) :
    EllPrimeCoverSource p X where
  S := X
  groupS := inferInstance
  fintypeS := inferInstance
  quotient := MonoidHom.id X
  quotient_surjective := Function.surjective_id
  quotient_kernel := by
    simp [center_eq_bot_of_nonabelian_simple hsimple hnonabelian]
  perfect := perfect_of_nonabelian_simple hsimple hnonabelian
  simple := hsimple
  nonabelian := hnonabelian
  centerPrimeTo := by
    simpa [center_eq_bot_of_nonabelian_simple hsimple hnonabelian] using hp.not_dvd_one
  maximal := by
    intro D _ _ f hsurjective hcentral hperfect hprimeTo
    exact exists_surjective_section_of_fullCover_pKernel hp cover hcover hkernel
      f hsurjective hcentral hperfect hprimeTo

def identityThreePrimeCover_of_fullCover_kernel_card_three
    {U X : Type u} [Group U] [Group X] [Fintype X]
    (cover : U →* X) (hcover : IsUniversalCentralExtension cover)
    (hkernel : Nat.card cover.ker = 3)
    (hsimple : IsSimpleGroup X) (hnonabelian : ¬ IsMulCommutative X) :
    EllPrimeCoverSource 3 X :=
  identityEllPrimeCover_of_fullCover_pKernel (by decide) cover hcover
    (IsPGroup.of_card (n := 1) (by simpa using hkernel)) hsimple hnonabelian

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSelfCover


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
