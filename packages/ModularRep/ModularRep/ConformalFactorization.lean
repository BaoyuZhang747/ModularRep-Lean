import ModularRep.OddOrderPower
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Tactic.Group

/-!
# Factorisation through a central square lift

This file isolates the elementary group-theoretic step behind the conformal
factorisation used in manuscript Proposition 3.9.  The concrete
representation theoretic assertions remain explicit hypotheses: a multiplier
homomorphism, a scalar map whose multiplier is its square, centrality of the
scalar image, and surjectivity of the square map in the multiplier group.

In the intended application `C` is a conformal symplectic group, the kernel of
`multiplier` is the symplectic group, `F` is the multiplicative group of the
ground field, and `scalar` sends a field element to its scalar matrix.  Nothing
in this file constructs or identifies any of those objects.
-/

namespace ModularRep.ManuscriptVerification.ConformalFactorization

variable {C F : Type*} [Group C] [Group F]

/-- Every element factors as an element of the multiplier kernel followed by
a scalar, provided scalar multipliers are squares and every multiplier has a
square root.

Centrality of the scalar image is not needed for this factorisation itself.
-/
theorem exists_ker_mul_scalar
    (multiplier : C →* F) (scalar : F → C)
    (multiplier_scalar : ∀ a : F, multiplier (scalar a) = a ^ 2)
    (square_surjective : Function.Surjective (fun a : F ↦ a ^ 2))
    (c : C) :
    ∃ k : multiplier.ker, ∃ a : F, c = (k : C) * scalar a := by
  obtain ⟨a, ha⟩ := square_surjective (multiplier c)
  change a ^ 2 = multiplier c at ha
  have hk : c * (scalar a)⁻¹ ∈ multiplier.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, multiplier_scalar, ← ha]
    exact mul_inv_cancel _
  refine ⟨⟨c * (scalar a)⁻¹, hk⟩, a, ?_⟩
  simp [mul_assoc]

/-- Version of `exists_ker_mul_scalar` that also records that the scalar
factor is central. -/
theorem exists_ker_mul_central_scalar
    (multiplier : C →* F) (scalar : F → C)
    (multiplier_scalar : ∀ a : F, multiplier (scalar a) = a ^ 2)
    (scalar_central : ∀ a : F, scalar a ∈ Subgroup.center C)
    (square_surjective : Function.Surjective (fun a : F ↦ a ^ 2))
    (c : C) :
    ∃ k : multiplier.ker, ∃ a : F,
      c = (k : C) * scalar a ∧ scalar a ∈ Subgroup.center C := by
  obtain ⟨k, a, hc⟩ := exists_ker_mul_scalar multiplier scalar
    multiplier_scalar square_surjective c
  exact ⟨k, a, hc, scalar_central a⟩

/-- Elementwise form of `C = ker(multiplier) * Z(C)`. -/
theorem exists_ker_mul_center
    (multiplier : C →* F) (scalar : F → C)
    (multiplier_scalar : ∀ a : F, multiplier (scalar a) = a ^ 2)
    (scalar_central : ∀ a : F, scalar a ∈ Subgroup.center C)
    (square_surjective : Function.Surjective (fun a : F ↦ a ^ 2))
    (c : C) :
    ∃ k : multiplier.ker, ∃ z : Subgroup.center C,
      c = (k : C) * (z : C) := by
  obtain ⟨k, a, hc, haCentral⟩ := exists_ker_mul_central_scalar
    multiplier scalar multiplier_scalar scalar_central square_surjective c
  exact ⟨k, ⟨scalar a, haCentral⟩, hc⟩

/-- If the scalar image is central, conjugation by an arbitrary element of
`C` on the multiplier kernel agrees pointwise with conjugation by the kernel
factor supplied by `exists_ker_mul_scalar`. -/
theorem exists_ker_factor_conjugation_eq
    (multiplier : C →* F) (scalar : F → C)
    (multiplier_scalar : ∀ a : F, multiplier (scalar a) = a ^ 2)
    (scalar_central : ∀ a : F, scalar a ∈ Subgroup.center C)
    (square_surjective : Function.Surjective (fun a : F ↦ a ^ 2))
    (c : C) :
    ∃ k : multiplier.ker, ∀ x : multiplier.ker,
      c * (x : C) * c⁻¹ = (k : C) * (x : C) * (k : C)⁻¹ := by
  obtain ⟨k, a, hc, haCentral⟩ := exists_ker_mul_central_scalar
    multiplier scalar multiplier_scalar scalar_central square_surjective c
  refine ⟨k, ?_⟩
  intro x
  have hcomm : (x : C) * scalar a = scalar a * (x : C) :=
    Subgroup.mem_center_iff.mp haCentral x
  rw [hc]
  calc
    ((k : C) * scalar a) * (x : C) * ((k : C) * scalar a)⁻¹ =
        (k : C) * (scalar a * (x : C) * (scalar a)⁻¹) * (k : C)⁻¹ := by
          group
    _ = (k : C) * (x : C) * (k : C)⁻¹ := by
      rw [← hcomm]
      simp [mul_assoc]

/-- Conjugation by every element of `C` induces an inner automorphism of the
multiplier kernel, under the same explicit square-lift and centrality
hypotheses. -/
theorem exists_ker_factor_conjNormal_eq_inner
    (multiplier : C →* F) (scalar : F → C)
    (multiplier_scalar : ∀ a : F, multiplier (scalar a) = a ^ 2)
    (scalar_central : ∀ a : F, scalar a ∈ Subgroup.center C)
    (square_surjective : Function.Surjective (fun a : F ↦ a ^ 2))
    (c : C) :
    ∃ k : multiplier.ker,
      MulAut.conjNormal (H := multiplier.ker) c = MulAut.conj k := by
  obtain ⟨k, hk⟩ := exists_ker_factor_conjugation_eq multiplier scalar
    multiplier_scalar scalar_central square_surjective c
  refine ⟨k, ?_⟩
  ext x
  simpa [MulAut.conj_apply] using hk x

/-- Odd cardinality of the multiplier group supplies the square-surjectivity
hypothesis in `exists_ker_mul_center`. -/
theorem exists_ker_mul_center_of_odd_card
    [Finite F] (hOdd : Odd (Nat.card F))
    (multiplier : C →* F) (scalar : F → C)
    (multiplier_scalar : ∀ a : F, multiplier (scalar a) = a ^ 2)
    (scalar_central : ∀ a : F, scalar a ∈ Subgroup.center C)
    (c : C) :
    ∃ k : multiplier.ker, ∃ z : Subgroup.center C,
      c = (k : C) * (z : C) :=
  exists_ker_mul_center multiplier scalar multiplier_scalar scalar_central
    (pow_two_bijective_of_odd_card hOdd).surjective c

/-- Odd cardinality of the multiplier group also makes the action of every
element of `C` on the multiplier kernel inner. -/
theorem exists_ker_factor_conjNormal_eq_inner_of_odd_card
    [Finite F] (hOdd : Odd (Nat.card F))
    (multiplier : C →* F) (scalar : F → C)
    (multiplier_scalar : ∀ a : F, multiplier (scalar a) = a ^ 2)
    (scalar_central : ∀ a : F, scalar a ∈ Subgroup.center C)
    (c : C) :
    ∃ k : multiplier.ker,
      MulAut.conjNormal (H := multiplier.ker) c = MulAut.conj k :=
  exists_ker_factor_conjNormal_eq_inner multiplier scalar multiplier_scalar
    scalar_central (pow_two_bijective_of_odd_card hOdd).surjective c

end ModularRep.ManuscriptVerification.ConformalFactorization


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
