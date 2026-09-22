import ModularRep.OrdinaryIrreducibleCharacter
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# Equivariance of induced character functions

This file defines the ordinary induced-character formula for a subgroup of a
finite group and proves its naturality under an automorphism stabilising that
subgroup.  It supplies the elementary equivariance step used after Clifford
correspondence in manuscript Lemma 3.6; equivariance is not accepted as an
extra external input.
-/

namespace ModularRep.PaperProofs.CharacterInductionEquivariance

open scoped BigOperators

universe u

variable {k N : Type u} [Field k] [Group N] [Fintype N]

/-- Restriction of an automorphism to a stable subgroup. -/
def restrictAut (I : Subgroup N) (tau : MulAut N)
    (stable : ∀ x : N, x ∈ I ↔ tau x ∈ I) : MulAut I where
  toFun x := ⟨tau x, (stable x).mp x.property⟩
  invFun x := ⟨tau.symm x, by
    apply (stable (tau.symm x)).mpr
    simpa using x.property⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv x := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul tau (x : N) (y : N)

@[simp]
theorem restrictAut_apply_coe (I : Subgroup N) (tau : MulAut N)
    (stable : ∀ x : N, x ∈ I ↔ tau x ∈ I) (x : I) :
    ((restrictAut I tau stable x : I) : N) = tau (x : N) :=
  rfl

/-- One summand in the ordinary induction formula. -/
noncomputable def inductionSummand (I : Subgroup N) (chi : I → k)
    (g x : N) : k := by
  classical
  exact if hx : x⁻¹ * g * x ∈ I then chi ⟨x⁻¹ * g * x, hx⟩ else 0

/-- The ordinary character induced from `I` to `N`, expressed by its standard
finite-sum formula. -/
noncomputable def inducedCharacter (I : Subgroup N) (chi : I → k) : N → k := by
  classical
  exact fun g ↦
    (Fintype.card I : k)⁻¹ * ∑ x : N, inductionSummand I chi g x

/-- Automorphisms carry induction summands to the corresponding summands. -/
theorem inductionSummand_natural
    (I : Subgroup N) (tau : MulAut N)
    (stable : ∀ x : N, x ∈ I ↔ tau x ∈ I)
    (chi : I → k) (g x : N) :
    inductionSummand I
        (fun y ↦ chi (restrictAut I tau stable y)) g x =
      inductionSummand I chi (tau g) (tau x) := by
  classical
  unfold inductionSummand
  have hconj : tau (x⁻¹ * g * x) = (tau x)⁻¹ * tau g * tau x := by
    simp
  by_cases hx : x⁻¹ * g * x ∈ I
  · have htx : (tau x)⁻¹ * tau g * tau x ∈ I := by
      rw [← hconj]
      exact (stable (x⁻¹ * g * x)).mp hx
    simp only [dif_pos hx, dif_pos htx]
    congr 1
    apply Subtype.ext
    exact hconj
  · have htx : (tau x)⁻¹ * tau g * tau x ∉ I := by
      intro h
      apply hx
      apply (stable (x⁻¹ * g * x)).mpr
      rwa [hconj]
    simp only [dif_neg hx, dif_neg htx]

/-- Induction commutes with an automorphism stabilising the subgroup. -/
theorem inducedCharacter_natural
    (I : Subgroup N) (tau : MulAut N)
    (stable : ∀ x : N, x ∈ I ↔ tau x ∈ I)
    (chi : I → k) (g : N) :
    inducedCharacter I
        (fun y ↦ chi (restrictAut I tau stable y)) g =
      inducedCharacter I chi (tau g) := by
  classical
  unfold inducedCharacter
  apply congrArg ((Fintype.card I : k)⁻¹ * ·)
  exact Fintype.sum_equiv tau.toEquiv _ _
    (fun x ↦ inductionSummand_natural I tau stable chi g x)

/-- If the inducing character is fixed by the restricted automorphism, its
induced character is fixed by the ambient automorphism. -/
theorem inducedCharacter_fixed
    (I : Subgroup N) (tau : MulAut N)
    (stable : ∀ x : N, x ∈ I ↔ tau x ∈ I)
    (chi : I → k)
    (chi_fixed : ∀ y : I, chi (restrictAut I tau stable y) = chi y) :
    (fun g ↦ inducedCharacter I chi (tau g)) = inducedCharacter I chi := by
  classical
  funext g
  rw [← inducedCharacter_natural I tau stable chi g]
  unfold inducedCharacter
  apply congrArg ((Fintype.card I : k)⁻¹ * ·)
  apply Finset.sum_congr rfl
  intro x _
  unfold inductionSummand
  split_ifs with hx
  · exact chi_fixed ⟨x⁻¹ * g * x, hx⟩
  · rfl

end ModularRep.PaperProofs.CharacterInductionEquivariance


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
