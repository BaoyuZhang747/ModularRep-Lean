import Formalisation.C2Cancellation
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.Group.Subgroup.Lattice

/-!
# Equivariant bijections from fixed point counts

The action is determined by an involution when the remaining generators fix
both sets pointwise. Equality of the cardinalities and of the fixed point
counts then gives an equivariant bijection. This is the finite group action
argument used for the principal block in Proposition 3.3 of the manuscript.
The character and weight counts themselves remain separate hypotheses.
-/

namespace ManuscriptIBAW

section Generators

variable {A X Y : Type*} [Group A] [MulAction A X] [MulAction A Y]

/-- The elements with which a map commutes form a subgroup of the acting group. -/
def equivarianceSubgroup (f : X → Y) : Subgroup A where
  carrier := {a | ∀ x, f (a • x) = a • f x}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb x
    rw [mul_smul, ha, hb, mul_smul]
  inv_mem' := by
    intro a ha x
    have hx := ha (a⁻¹ • x)
    have hy := congrArg (fun y : Y => a⁻¹ • y) hx
    simpa using hy.symm

/-- Equivariance on a generating set implies equivariance for the whole group. -/
theorem equivariant_of_generators (f : X → Y) (S : Set A)
    (generates : Subgroup.closure S = ⊤)
    (commutes : ∀ a ∈ S, ∀ x, f (a • x) = a • f x) :
    ∀ (a : A) (x : X), f (a • x) = a • f x := by
  have hle : Subgroup.closure S ≤ equivarianceSubgroup f :=
    (Subgroup.closure_le (equivarianceSubgroup f)).mpr commutes
  intro a
  exact hle (by rw [generates]; trivial)

end Generators

section Involutions

variable {A X Y : Type*} [Group A] [MulAction A X] [MulAction A Y]
    [Fintype X] [Fintype Y]

/-- If one generator acts as an involution and all other generators act
trivially, the two relevant counts determine the action up to isomorphism. -/
theorem equivariant_bijection_of_involution_counts
    (T : Set A) (δ : A)
    (generates : Subgroup.closure (T ∪ {δ}) = ⊤)
    (trivialX : ∀ a ∈ T, ∀ x : X, a • x = x)
    (trivialY : ∀ a ∈ T, ∀ y : Y, a • y = y)
    (involutionX : Function.Involutive (fun x : X => δ • x))
    (involutionY : Function.Involutive (fun y : Y => δ • y))
    (cardinality : Fintype.card X = Fintype.card Y)
    (fixedPoints : Nat.card {x : X // δ • x = x} =
      Nat.card {y : Y // δ • y = y}) :
    ∃ e : X ≃ Y, ∀ (a : A) (x : X), e (a • x) = a • e x := by
  classical
  let σ : Equiv.Perm X := MulAction.toPerm δ
  let τ : Equiv.Perm Y := MulAction.toPerm δ
  have hf : Fintype.card (Function.fixedPoints σ) =
      Fintype.card (Function.fixedPoints τ) := by
    change Fintype.card {x : X // δ • x = x} =
      Fintype.card {y : Y // δ • y = y}
    simpa only [Nat.card_eq_fintype_card] using fixedPoints
  obtain ⟨e, he⟩ :=
    Formalisation.C2Cancellation.exists_equivariantEquiv_of_card_eq_of_fixed_card_eq
      σ τ involutionX involutionY cardinality hf
  refine ⟨e, equivariant_of_generators e (T ∪ {δ}) generates ?_⟩
  intro a ha x
  rcases ha with ha | ha
  · rw [trivialX a ha, trivialY a ha]
  · have haδ : a = δ := ha
    subst a
    exact he x

end Involutions

end ManuscriptIBAW

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
