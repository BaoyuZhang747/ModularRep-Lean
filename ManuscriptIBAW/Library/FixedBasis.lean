import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Pointwise fixed bases

An action by linear maps which fixes a basis pointwise fixes the whole
module. For a permutation action on another basis, it therefore fixes every
index. This is the elementary deduction used with the integral basic set in
the proof of Proposition 3.8. No induction theorem is needed for it.
-/

namespace ManuscriptIBAW

open Module

section LinearAction

variable {R A V X Y : Type*} [Semiring R] [Monoid A]
    [AddCommMonoid V] [Module R V]

/-- A linear action fixing a basis pointwise is trivial on the whole module. -/
theorem linear_action_trivial_of_fixed_basis
    (ρ : A →* (V →ₗ[R] V)) (b : Basis X R V)
    (fixed : ∀ a x, ρ a (b x) = b x) :
    ∀ (a : A) (v : V), ρ a v = v := by
  intro a v
  have hid : ρ a = LinearMap.id := b.ext (fixed a)
  exact LinearMap.congr_fun hid v

/-- If a fixed basis spans a permutation module, the permutation action on
the indices of its distinguished basis is trivial. -/
theorem action_trivial_of_fixed_basis [Nontrivial R] [MulAction A Y]
    (ρ : A →* (V →ₗ[R] V)) (b : Basis X R V) (c : Basis Y R V)
    (fixed : ∀ a x, ρ a (b x) = b x)
    (natural : ∀ (a : A) (y : Y), ρ a (c y) = c (a • y)) :
    ∀ (a : A) (y : Y), a • y = y := by
  intro a y
  apply c.injective
  rw [← natural, linear_action_trivial_of_fixed_basis ρ b fixed]

end LinearAction

section Bijection

variable {R A V X Y : Type*} [Semiring R] [Nontrivial R] [InvariantBasisNumber R]
    [Monoid A] [AddCommMonoid V] [Module R V]
    [MulAction A X] [MulAction A Y]

/-- A pointwise fixed basis and a natural permutation basis give an
equivariant bijection between their index sets. -/
theorem equivariant_bijection_of_fixed_basis
    (ρ : A →* (V →ₗ[R] V)) (b : Basis X R V) (c : Basis Y R V)
    (fixedX : ∀ (a : A) (x : X), a • x = x)
    (naturalX : ∀ (a : A) (x : X), ρ a (b x) = b (a • x))
    (naturalY : ∀ (a : A) (y : Y), ρ a (c y) = c (a • y)) :
    ∃ e : X ≃ Y, ∀ (a : A) (x : X), e (a • x) = a • e x := by
  have hb : ∀ a x, ρ a (b x) = b x := by
    intro a x
    rw [naturalX, fixedX]
  have hy := action_trivial_of_fixed_basis ρ b c hb naturalY
  refine ⟨b.indexEquiv c, ?_⟩
  intro a x
  rw [fixedX, hy]

end Bijection

end ManuscriptIBAW

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
