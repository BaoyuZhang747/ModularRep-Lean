import ModularRep.PaperProofs.TypeBCliffordOrthogonalAction
import ModularRep.PaperProofs.TypeBOrthogonalOmegaCarriers
import Mathlib.LinearAlgebra.QuadraticForm.Radical

/-!
# Concrete geometry of the existing Type B split quadratic space

The polar bilinear form is computed from the already checked diagonal
`splitBilin`. Testing it against the displayed coordinate vectors proves
nondegeneracy when two is nonzero. The same vectors exhibit the actual
isotropic hyperbolic pair and a vector of quadratic value one. No geometric
source hypothesis, new quadratic space or Clifford identification is used.
The dimension theorem is reused from `TypeBOrthogonalOmegaCarriers`.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBSplitQuadraticGeometry

open TypeBCliffordCarriers TypeBCliffordOrthogonalAction

universe u

variable (n : ℕ) (F : Type u) [Field F]

/-- The polar form is the sum of the displayed bilinear form and its flip;
this is the polarization identity for that exact diagonal, in every field. -/
theorem polarBilin_eq :
    (splitForm n F).polarBilin = splitBilin n F + (splitBilin n F).flip := by
  rw [← splitBilin_toQuadraticMap n F]
  exact LinearMap.BilinMap.polarBilin_toQuadraticMap

theorem polarBilin_apply (v w : Vector n F) :
    (splitForm n F).polarBilin v w =
      (v none * w none +
        ∑ i : Fin n, v (some (Sum.inl i)) * w (some (Sum.inr i))) +
      (w none * v none +
        ∑ i : Fin n, w (some (Sum.inl i)) * v (some (Sum.inr i))) := by
  rw [polarBilin_eq]
  change splitBilin n F v w + splitBilin n F w v = _
  rw [splitBilin_apply, splitBilin_apply]

theorem polarBilin_symm (v w : Vector n F) :
    (splitForm n F).polarBilin v w = (splitForm n F).polarBilin w v := by
  simpa only [QuadraticMap.polarBilin_apply_apply] using
    QuadraticMap.polar_comm (splitForm n F) v w

/-- The vector epsilon_0 of the fixed coordinate model. -/
def axis : Vector n F := fun c =>
  match c with
  | none => 1
  | some _ => 0

/-- The actual epsilon_i coordinate vector, for a displayed index i. -/
def leftVector (i : Fin n) : Vector n F := fun c =>
  match c with
  | none => 0
  | some (Sum.inl j) => if j = i then 1 else 0
  | some (Sum.inr _) => 0

/-- The actual eta_i coordinate vector, paired with epsilon_i. -/
def rightVector (i : Fin n) : Vector n F := fun c =>
  match c with
  | none => 0
  | some (Sum.inl _) => 0
  | some (Sum.inr j) => if j = i then 1 else 0

@[simp] theorem splitForm_axis : splitForm n F (axis n F) = 1 := by
  simp [splitForm_apply, axis]

@[simp] theorem splitForm_leftVector (i : Fin n) :
    splitForm n F (leftVector n F i) = 0 := by
  simp [splitForm_apply, leftVector]

@[simp] theorem splitForm_rightVector (i : Fin n) :
    splitForm n F (rightVector n F i) = 0 := by
  simp [splitForm_apply, rightVector]

theorem axis_ne_zero : axis n F ≠ 0 := by
  intro h
  have h1 : (1 : F) = 0 := by simpa [axis] using congrFun h none
  exact one_ne_zero h1

theorem leftVector_ne_zero (i : Fin n) : leftVector n F i ≠ 0 := by
  intro h
  have h1 : (1 : F) = 0 := by
    simpa [leftVector] using congrFun h (some (Sum.inl i))
  exact one_ne_zero h1

theorem rightVector_ne_zero (i : Fin n) : rightVector n F i ≠ 0 := by
  intro h
  have h1 : (1 : F) = 0 := by
    simpa [rightVector] using congrFun h (some (Sum.inr i))
  exact one_ne_zero h1

@[simp] theorem polarBilin_axis (v : Vector n F) :
    (splitForm n F).polarBilin v (axis n F) = (2 : F) * v none := by
  rw [polarBilin_apply]
  simp [axis, two_mul]

@[simp] theorem polarBilin_leftVector (v : Vector n F) (i : Fin n) :
    (splitForm n F).polarBilin v (leftVector n F i) = v (some (Sum.inr i)) := by
  rw [polarBilin_apply]
  simp [leftVector, mul_ite, ite_mul]

@[simp] theorem polarBilin_rightVector (v : Vector n F) (i : Fin n) :
    (splitForm n F).polarBilin v (rightVector n F i) = v (some (Sum.inl i)) := by
  rw [polarBilin_apply]
  simp [rightVector, mul_ite, ite_mul]

@[simp] theorem polarBilin_left_right (i : Fin n) :
    (splitForm n F).polarBilin (leftVector n F i) (rightVector n F i) = 1 := by
  rw [polarBilin_rightVector]
  simp [leftVector]

@[simp] theorem polarBilin_right_left (i : Fin n) :
    (splitForm n F).polarBilin (rightVector n F i) (leftVector n F i) = 1 := by
  rw [polarBilin_leftVector]
  simp [rightVector]

/-- The actual displayed hyperbolic plane represents a*b. In particular,
epsilon_i + a*eta_i has quadratic value a, in every characteristic. -/
theorem splitForm_hyperbolic (i : Fin n) (a b : F) :
    splitForm n F (a • leftVector n F i + b • rightVector n F i) = a * b := by
  simp [splitForm_apply, leftVector, rightVector, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, mul_ite, ite_mul]

/-- Each annihilator coordinate vanishes by testing against its paired
coordinate vector. Only the epsilon_0 coordinate uses that two is nonzero. -/
theorem polar_separatingLeft (two_ne : (2 : F) ≠ 0) :
    (splitForm n F).polarBilin.SeparatingLeft := by
  intro v hv
  have h0 : (2 : F) * v none = 0 := by
    simpa only [polarBilin_axis] using hv (axis n F)
  have v0 : v none = 0 := (mul_eq_zero.mp h0).resolve_left two_ne
  funext c
  cases c with
  | none => exact v0
  | some c =>
    cases c with
    | inl i =>
      change v (some (Sum.inl i)) = 0
      simpa only [polarBilin_rightVector] using hv (rightVector n F i)
    | inr i =>
      change v (some (Sum.inr i)) = 0
      simpa only [polarBilin_leftVector] using hv (leftVector n F i)

theorem polar_nondegenerate (two_ne : (2 : F) ≠ 0) :
    (splitForm n F).polarBilin.Nondegenerate := by
  refine ⟨polar_separatingLeft n F two_ne, ?_⟩
  intro v hv
  apply polar_separatingLeft n F two_ne v
  intro w
  rw [polarBilin_symm]
  exact hv w

/-- The quadratic-form version uses Mathlib's exact invertibility-of-two
prerequisite, installed from the explicit field-level nonzero proof. -/
theorem splitForm_nondegenerate (two_ne : (2 : F) ≠ 0) :
    (splitForm n F).Nondegenerate := by
  letI : Invertible (2 : F) := invertibleOfNonzero two_ne
  exact (QuadraticMap.nondegenerate_polar_iff (Q := splitForm n F)).mp
    (polar_nondegenerate n F two_ne)

theorem exists_hyperbolic_pair (rank_pos : 1 ≤ n) :
    ∃ v w : Vector n F,
      v ≠ 0 ∧ w ≠ 0 ∧ splitForm n F v = 0 ∧ splitForm n F w = 0 ∧
        (splitForm n F).polarBilin v w = 1 := by
  let i : Fin n := ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one rank_pos⟩
  exact ⟨leftVector n F i, rightVector n F i,
    leftVector_ne_zero n F i, rightVector_ne_zero n F i,
    splitForm_leftVector n F i, splitForm_rightVector n F i,
    polarBilin_left_right n F i⟩

theorem exists_isotropic (rank_pos : 1 ≤ n) :
    ∃ v : Vector n F, v ≠ 0 ∧ splitForm n F v = 0 := by
  obtain ⟨v, w, hv, _, hQ, _, _⟩ := exists_hyperbolic_pair n F rank_pos
  exact ⟨v, hv, hQ⟩

section OddField

variable {p f : ℕ} [Finite F] [CharP F p]
  (parameters : OddFieldParameters F p f)

include parameters

/-- Oddness of the defining characteristic, not of a modular coefficient
prime, discharges the only field restriction in the polar calculation. -/
theorem two_ne_zero_of_oddFieldParameters : (2 : F) ≠ 0 := by
  intro h
  have hp : p ∣ 2 := (CharP.cast_eq_zero_iff F p 2).mp h
  exact (parameters.prime.coprime_iff_not_dvd.mp parameters.odd.coprime_two_right) hp

theorem polar_nondegenerate_of_oddFieldParameters :
    (splitForm n F).polarBilin.Nondegenerate :=
  polar_nondegenerate n F (two_ne_zero_of_oddFieldParameters F parameters)

theorem splitForm_nondegenerate_of_oddFieldParameters :
    (splitForm n F).Nondegenerate :=
  splitForm_nondegenerate n F (two_ne_zero_of_oddFieldParameters F parameters)

/-- The exact finite-field/rank geometry packet is a theorem, not an
external structural source. Dimension reuses the checked carrier theorem. -/
theorem source_geometry (rank : 3 ≤ n) :
    Module.finrank F (Vector n F) = 2 * n + 1 ∧
      (splitForm n F).polarBilin.Nondegenerate ∧
      (splitForm n F).Nondegenerate ∧
      (∃ v : Vector n F, v ≠ 0 ∧ splitForm n F v = 0) ∧
      (∃ v w : Vector n F,
        v ≠ 0 ∧ w ≠ 0 ∧ splitForm n F v = 0 ∧ splitForm n F w = 0 ∧
          (splitForm n F).polarBilin v w = 1) := by
  have rank_pos : 1 ≤ n := (by decide : 1 ≤ 3).trans rank
  exact ⟨TypeBOrthogonalOmegaCarriers.vector_finrank n F,
    polar_nondegenerate_of_oddFieldParameters n F parameters,
    splitForm_nondegenerate_of_oddFieldParameters n F parameters,
    exists_isotropic n F rank_pos, exists_hyperbolic_pair n F rank_pos⟩

end OddField

end ModularRep.PaperProofs.TypeBSplitQuadraticGeometry


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
