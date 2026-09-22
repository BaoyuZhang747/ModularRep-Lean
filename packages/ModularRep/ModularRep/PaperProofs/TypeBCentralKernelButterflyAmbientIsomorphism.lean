import ModularRep.PaperProofs.TypeBCentralKernelButterflyLocalIdentification

/-!
# Actual ambient isomorphisms in the Butterfly construction

An ambient equivalence anchored to the same base equivalence identifies the
two conjugation actions. When the first local group contains the actual
base centralizer, the Butterfly local preimage is its actual ambient image.
The resulting local identifications preserve both the base and ambient
elements. These are group deductions; no character or new triple is sourced.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBCentralKernelButterflyAmbientIsomorphism

open ModularRep TypeBCentralKernelTripleCertificate
open TypeBCentralKernelButterflyCertificate
open TypeBCentralKernelButterflyLocalIdentification

universe u

variable {T1 T2 : Type u} [Group T1] [Group T2]
variable (N1 : Subgroup T1) (N2 : Subgroup T2) [N1.Normal] [N2.Normal]
variable (eT : T1 ≃* T2) (eN : N1 ≃* N2)
variable (anchor : ∀ n : N1, eT (n : T1) = (eN n : T2))

include anchor in
/-- The two actual conjugation actions agree under the ambient equivalence. -/
theorem action_square (t : T1) :
    firstAction N1 t = secondAction N1 N2 eN (eT t) := by
  apply MulEquiv.ext
  intro n
  apply eN.injective
  rw [secondAction_value]
  apply Subtype.ext
  calc
    (eN (firstAction N1 t n) : T2) = eT (firstAction N1 t n : T1) :=
      (anchor (firstAction N1 t n)).symm
    _ = eT (t * (n : T1) * t⁻¹) := congrArg eT (firstAction_value N1 t n)
    _ = eT t * (eN n : T2) * (eT t)⁻¹ := by rw [map_mul, map_mul, map_inv, anchor n]
    _ = (MulAut.conjNormal (H := N2) (eT t) (eN n) : T2) := rfl

include anchor in
theorem sameConjugationImage : SameConjugationImage N1 N2 eN := by
  change (firstAction N1).range = (secondAction N1 N2 eN).range
  ext alpha
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨eT t, (action_square N1 N2 eT eN anchor t).symm⟩
  · rintro ⟨t, rfl⟩
    refine ⟨eT.symm t, ?_⟩
    have h := action_square N1 N2 eT eN anchor (eT.symm t)
    rw [eT.apply_symm_apply] at h
    exact h

variable (H1 : Subgroup T1)
variable (centralizer_le : Subgroup.centralizer (N1 : Set T1) ≤ H1)

include anchor centralizer_le in
/-- The prescribed Butterfly preimage equals the actual image of H1. -/
theorem secondLocalAmbient_eq_map :
    secondLocalAmbient N1 N2 eN H1 = H1.map eT.toMonoidHom := by
  ext t
  constructor
  · intro ht
    obtain ⟨h, hh, same⟩ := (mem_secondLocalAmbient N1 N2 eN H1 t).mp ht
    have square := action_square N1 N2 eT eN anchor (eT.symm t)
    rw [eT.apply_symm_apply] at square
    have actions : firstAction N1 h = firstAction N1 (eT.symm t) := same.trans square.symm
    have residual : firstAction N1 (h⁻¹ * eT.symm t) = 1 := by
      rw [map_mul, map_inv, actions, inv_mul_cancel]
    have hc := centralizer_le (centralizes_of_action_one N1 (h⁻¹ * eT.symm t) residual)
    have htH : eT.symm t ∈ H1 := by
      have product := H1.mul_mem hh hc
      simpa only [← mul_assoc, mul_inv_cancel, one_mul] using product
    exact ⟨eT.symm t, htH, eT.apply_symm_apply t⟩
  · rintro ⟨h, hh, rfl⟩
    exact (mem_secondLocalAmbient N1 N2 eN H1 (eT h)).mpr
      ⟨h, hh, action_square N1 N2 eT eN anchor h⟩

/-- The actual restriction of eT, followed only by the proved subgroup equality. -/
def localAmbientEquiv : H1 ≃* secondLocalAmbient N1 N2 eN H1 :=
  (H1.equivMapOfInjective eT.toMonoidHom eT.injective).trans
    (MulEquiv.subgroupCongr (secondLocalAmbient_eq_map N1 N2 eT eN anchor H1 centralizer_le).symm)

theorem localAmbientEquiv_value (h : H1) :
    (localAmbientEquiv N1 N2 eT eN anchor H1 centralizer_le h : T2) = eT (h : T1) := rfl

/-- Reuse the checked restriction of the anchored base equivalence. -/
def constructedLocalIdentification :
    LocalIdentification N1 N2 eN H1 (secondLocalAmbient N1 N2 eN H1) :=
  localIdentification N1 N2 eN H1 centralizer_le

include anchor in
theorem localIdentification_ambient_value (x : localBase N1 H1) :
    ((constructedLocalIdentification N1 N2 eN H1 centralizer_le).equiv x).val.val =
      eT x.val.val := by
  have h := congrArg Subtype.val
    ((constructedLocalIdentification N1 N2 eN H1 centralizer_le).base_value x)
  exact h.trans (anchor (localToBase N1 H1 x)).symm

/-- The actual local-base inclusion commutes with the restricted ambient map. -/
theorem localIdentification_inclusion_square (x : localBase N1 H1) :
    ((constructedLocalIdentification N1 N2 eN H1 centralizer_le).equiv x).val =
      localAmbientEquiv N1 N2 eT eN anchor H1 centralizer_le x.val := by
  apply Subtype.ext
  exact (localIdentification_ambient_value N1 N2 eT eN anchor H1 centralizer_le x).trans
    (localAmbientEquiv_value N1 N2 eT eN anchor H1 centralizer_le x.val).symm

end ModularRep.PaperProofs.TypeBCentralKernelButterflyAmbientIsomorphism


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
