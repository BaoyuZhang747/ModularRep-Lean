import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCoverGroupFacts

/-! Automorphisms lift uniquely along the actual universal central extension.
When its kernel is the centre, canonical descent is an equivalence. All
naturality equations refer to the supplied covering map. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCoverAutomorphismEquiv

open ModularRep
open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate

universe u

variable {X S : Type u} [Group X] [Group S]
variable (q : X →* S) (hq : IsUniversalCentralExtension q)
include hq

theorem existsUnique_lift_over_aut (beta : MulAut S) :
    ∃! l : X →* X, q.comp l = beta.toMonoidHom.comp q := by
  let f : X →* S := beta.symm.toMonoidHom.comp q
  have hf : IsCentralExtension f := by
    refine ⟨beta.symm.surjective.comp hq.1.1, ?_⟩
    intro z hz
    apply hq.1.2
    change q z = 1
    apply beta.symm.injective
    simpa only [map_one] using
      (show beta.symm (q z) = 1 from hz)
  have lift_iff (l : X →* X) :
      f.comp l = q ↔ q.comp l = beta.toMonoidHom.comp q := by
    constructor
    · intro h
      ext x
      have hx := DFunLike.congr_fun h x
      change beta.symm (q (l x)) = q x at hx
      change q (l x) = beta (q x)
      rw [← hx, beta.apply_symm_apply]
    · intro h
      ext x
      have hx := DFunLike.congr_fun h x
      change q (l x) = beta (q x) at hx
      change beta.symm (q (l x)) = q x
      rw [hx, beta.symm_apply_apply]
  obtain ⟨l, hl, unique⟩ := hq.2 X f hf
  refine ⟨l, (lift_iff l).mp hl, ?_⟩
  intro m hm
  exact unique m ((lift_iff m).mpr hm)

theorem lift_over_aut_ext (beta : MulAut S) (l r : X →* X)
    (hl : ∀ x, q (l x) = beta (q x))
    (hr : ∀ x, q (r x) = beta (q x)) :
    l = r := by
  obtain ⟨m, hm, unique⟩ := existsUnique_lift_over_aut q hq beta
  exact (unique l (by ext x; exact hl x)).trans
    (unique r (by ext x; exact hr x)).symm

theorem exists_aut_lift (beta : MulAut S) :
    ∃ alpha : MulAut X, ∀ x, q (alpha x) = beta (q x) := by
  obtain ⟨l, hl, _⟩ := existsUnique_lift_over_aut q hq beta
  obtain ⟨r, hr, _⟩ := existsUnique_lift_over_aut q hq beta.symm
  have hlx (x : X) : q (l x) = beta (q x) :=
    DFunLike.congr_fun hl x
  have hrx (x : X) : q (r x) = beta.symm (q x) :=
    DFunLike.congr_fun hr x
  have hrl : r.comp l = MonoidHom.id X := by
    apply lift_over_aut_ext q hq (1 : MulAut S)
    · intro x
      change q (r (l x)) = q x
      rw [hrx, hlx, beta.symm_apply_apply]
    · intro x
      rfl
  have hlr : l.comp r = MonoidHom.id X := by
    apply lift_over_aut_ext q hq (1 : MulAut S)
    · intro x
      change q (l (r x)) = q x
      rw [hlx, hrx, beta.apply_symm_apply]
    · intro x
      rfl
  let alpha : MulAut X :=
    { toFun := l
      invFun := r
      left_inv := fun x => DFunLike.congr_fun hrl x
      right_inv := fun x => DFunLike.congr_fun hlr x
      map_mul' := l.map_mul }
  exact ⟨alpha, hlx⟩

variable (hk : q.ker = Subgroup.center X)

def coverDescend (alpha : MulAut X) : MulAut S :=
  let hmap : q.ker.map alpha.toMonoidHom = q.ker := by
    rw [hk]
    exact Subgroup.characteristic_iff_map_eq.mp inferInstance alpha
  let e : X ⧸ q.ker ≃* S :=
    QuotientGroup.quotientKerEquivOfSurjective q hq.1.1
  let aQ := QuotientGroup.congr q.ker q.ker alpha hmap
  e.symm.trans (aQ.trans e)

theorem coverDescend_apply_q (alpha : MulAut X) (x : X) :
    coverDescend q hq hk alpha (q x) = q (alpha x) := by
  let e : X ⧸ q.ker ≃* S :=
    QuotientGroup.quotientKerEquivOfSurjective q hq.1.1
  have he : e (QuotientGroup.mk x) = q x := rfl
  have hes : e.symm (q x) = QuotientGroup.mk x := by
    rw [← he, e.symm_apply_apply]
  have hmap : q.ker.map alpha.toMonoidHom = q.ker := by
    rw [hk]
    exact Subgroup.characteristic_iff_map_eq.mp inferInstance alpha
  change e
    (QuotientGroup.congr q.ker q.ker alpha hmap
      (e.symm (q x))) = q (alpha x)
  rw [hes]
  rfl

def coverDescendHom : MulAut X →* MulAut S where
  toFun := coverDescend q hq hk
  map_one' := by
    ext s
    obtain ⟨x, rfl⟩ := hq.1.1 s
    rw [coverDescend_apply_q]
    rfl
  map_mul' alpha beta := by
    ext s
    obtain ⟨x, rfl⟩ := hq.1.1 s
    change coverDescend q hq hk (alpha * beta) (q x) =
      coverDescend q hq hk alpha
        (coverDescend q hq hk beta (q x))
    rw [coverDescend_apply_q, coverDescend_apply_q,
      coverDescend_apply_q]
    rfl

theorem coverDescendHom_injective :
    Function.Injective (coverDescendHom q hq hk) := by
  intro alpha gamma h
  change coverDescend q hq hk alpha =
    coverDescend q hq hk gamma at h
  apply MulEquiv.toMonoidHom_injective
  apply lift_over_aut_ext q hq (coverDescend q hq hk alpha)
  · intro x
    exact (coverDescend_apply_q q hq hk alpha x).symm
  · intro x
    change q (gamma x) = coverDescend q hq hk alpha (q x)
    rw [← coverDescend_apply_q q hq hk gamma x, ← h]

theorem coverDescendHom_surjective :
    Function.Surjective (coverDescendHom q hq hk) := by
  intro beta
  obtain ⟨alpha, halpha⟩ := exists_aut_lift q hq beta
  refine ⟨alpha, ?_⟩
  ext s
  obtain ⟨x, rfl⟩ := hq.1.1 s
  exact (coverDescend_apply_q q hq hk alpha x).trans (halpha x)

def fullCoverAutEquiv : MulAut X ≃* MulAut S :=
  MulEquiv.ofBijective (coverDescendHom q hq hk)
    ⟨coverDescendHom_injective q hq hk,
      coverDescendHom_surjective q hq hk⟩

theorem fullCoverAutEquiv_apply_q (alpha : MulAut X) (x : X) :
    fullCoverAutEquiv q hq hk alpha (q x) = q (alpha x) :=
  coverDescend_apply_q q hq hk alpha x

theorem fullCoverAutEquiv_symm_apply_q (beta : MulAut S) (x : X) :
    q (((fullCoverAutEquiv q hq hk).symm beta) x) = beta (q x) := by
  have h := fullCoverAutEquiv_apply_q q hq hk
    ((fullCoverAutEquiv q hq hk).symm beta) x
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

theorem fullCoverAutEquiv_conj (x : X) :
    fullCoverAutEquiv q hq hk (MulAut.conj x) =
      MulAut.conj (q x) := by
  ext s
  obtain ⟨y, rfl⟩ := hq.1.1 s
  rw [fullCoverAutEquiv_apply_q]
  simp only [MulAut.conj_apply, map_mul, map_inv]

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCoverAutomorphismEquiv


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
