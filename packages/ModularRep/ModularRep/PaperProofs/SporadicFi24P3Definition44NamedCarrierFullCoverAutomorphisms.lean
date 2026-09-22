import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCoverGroupFacts
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierJ4FullCover

/-! All-inner automorphisms of the actual full-cover group follow from
the simple quotient and uniqueness in its universal central extension.
No automorphism assertion about arbitrary central quotients is assumed. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCoverAutomorphisms

open ModularRep
open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCoverGroupFacts
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierJ4FullCover

universe u

theorem allInner_of_fullCover_of_outer_card_one
    {X S : Type u} [Group X] [Group S]
    (q : X →* S) (hq : IsUniversalCentralExtension q)
    (hs : IsSimpleGroup S) (hna : ¬ IsMulCommutative S)
    (hOuter : Nat.card ((MulAut S)ᵐᵒᵖ ⧸
      (RepresentationWeight.innerInverseOpHom (G := S)).range) = 1) :
    AllAutomorphismsInner (X := X) := by
  refine ⟨?_⟩
  intro alpha
  have hk := ker_eq_center_of_simple_quotient q hq.1 hs hna
  have hmap : q.ker.map alpha.toMonoidHom = q.ker := by
    rw [hk]
    exact Subgroup.characteristic_iff_map_eq.mp inferInstance alpha
  let e : X ⧸ q.ker ≃* S := QuotientGroup.quotientKerEquivOfSurjective q hq.1.1
  let aQ := QuotientGroup.congr q.ker q.ker alpha hmap
  let beta : MulAut S := e.symm.trans (aQ.trans e)
  have hbeta (x : X) : beta (q x) = q (alpha x) := by
    have he : e (QuotientGroup.mk x) = q x := rfl
    have hes : e.symm (q x) = QuotientGroup.mk x := by
      rw [← he, e.symm_apply_apply]
    change e (aQ (e.symm (q x))) = q (alpha x)
    rw [hes]
    rfl
  obtain ⟨s, hs_inner⟩ := (allAutomorphismsInner_of_outer_card_one hOuter).eq_conj beta
  obtain ⟨x, hx⟩ := hq.1.1 s
  have hinner (y : X) : q (MulAut.conj x y) = beta (q y) := by
    rw [hs_inner]
    simp [MulAut.conj_apply, map_mul, map_inv, hx]
  let f : X →* S := beta.symm.toMonoidHom.comp q
  have hf : IsCentralExtension f := by
    refine ⟨beta.symm.surjective.comp hq.1.1, ?_⟩
    intro z hz
    apply hq.1.2
    change q z = 1
    apply beta.symm.injective
    simpa only [map_one] using (show beta.symm (q z) = 1 from hz)
  have hAlpha : f.comp alpha.toMonoidHom = q := by
    ext y
    change beta.symm (q (alpha y)) = q y
    rw [← hbeta, beta.symm_apply_apply]
  have hConj : f.comp (MulAut.conj x).toMonoidHom = q := by
    ext y
    change beta.symm (q (MulAut.conj x y)) = q y
    rw [hinner, beta.symm_apply_apply]
  obtain ⟨l, hl, unique⟩ := hq.2 X f hf
  refine ⟨x, ?_⟩
  apply MulEquiv.toMonoidHom_injective
  exact (unique alpha.toMonoidHom hAlpha).trans
    (unique (MulAut.conj x).toMonoidHom hConj).symm

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCoverAutomorphisms


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
