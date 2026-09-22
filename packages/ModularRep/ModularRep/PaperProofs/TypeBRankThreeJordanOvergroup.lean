import ModularRep.StabilizerFactorizationTransport

/-!
# The ambient diagonal enlargement in the rank-three Jordan deduction

The existing equivariant-equivalence theorem transfers the Levi stabilizer
factorization to its Jordan correspondent for the Levi acting group. This
supporting deduction enlarges that group to the ambient regular embedding.
It uses the literal inclusion, the product Gtilde = G Ltilde, and triviality
of inner G on the ambient set of characters. No quotient action, stabilizer
or selected-character conclusion is supplied as an external source here.

The consumer must bind these actions and groups to the same modular Jordan
packets. This helper alone is not a manuscript-window endpoint.
-/

namespace ModularRep.PaperProofs.TypeBRankThreeJordanOvergroup

open ModularRep.ManuscriptVerification.StabilizerFactorizationTransport

variable {A H E X : Type*} [Group A] [Group H] [Group E]
variable [MulAction A X] [MulAction H X] [MulAction E X]

/-- A regular-embedding element acts as its Levi factor when the other
factor acts by inner automorphisms on this same set of characters. -/
theorem exists_levi_action
    (inclusion : H →* A) (inner : Subgroup A)
    (product : ∀ a : A, ∃ g : inner, ∃ h : H,
      a = (g : A) * inclusion h)
    (inner_trivial : ∀ (g : inner) (x : X), (g : A) • x = x)
    (inclusion_action : ∀ (h : H) (x : X), inclusion h • x = h • x)
    (a : A) : ∃ h : H, ∀ x : X, a • x = h • x := by
  obtain ⟨g, h, rfl⟩ := product a
  refine ⟨h, ?_⟩
  intro x
  rw [mul_smul, inner_trivial, inclusion_action]

/-- The manuscript's diagonal enlargement. The Levi factorization is a
preceding deduction; the product and action equations are group data. -/
theorem product_factorization_of_levi
    (inclusion : H →* A) (inner : Subgroup A)
    (product : ∀ a : A, ∃ g : inner, ∃ h : H,
      a = (g : A) * inclusion h)
    (inner_trivial : ∀ (g : inner) (x : X), (g : A) • x = x)
    (inclusion_action : ∀ (h : H) (x : X), inclusion h • x = h • x)
    (x : X)
    (levi_factorization : ProductStabilizerFactorization (D := H) (E := E) x) :
    ProductStabilizerFactorization (D := A) (E := E) x := by
  intro a e
  obtain ⟨h, action⟩ := exists_levi_action inclusion inner product
    inner_trivial inclusion_action a
  simpa only [action] using levi_factorization h e

/-- The same deduction for the actual compatible semidirect actions. -/
theorem semidirect_factorization_of_levi
    (inclusion : H →* A) (inner : Subgroup A)
    (product : ∀ a : A, ∃ g : inner, ∃ h : H,
      a = (g : A) * inclusion h)
    (inner_trivial : ∀ (g : inner) (x : X), (g : A) • x = x)
    (inclusion_action : ∀ (h : H) (x : X), inclusion h • x = h • x)
    (fieldA : E →* MulAut A) (fieldH : E →* MulAut H)
    (compatibleA : Formalisation.SemidirectActionCompatible (X := X) fieldA)
    (compatibleH : Formalisation.SemidirectActionCompatible (X := X) fieldH)
    (x : X)
    (levi_factorization :
      Formalisation.SemidirectStabilizerFactors fieldH compatibleH x) :
    Formalisation.SemidirectStabilizerFactors fieldA compatibleA x := by
  apply (semidirectStabilizerFactors_iff_productStabilizerFactorization
    fieldA compatibleA x).mpr
  exact product_factorization_of_levi inclusion inner product inner_trivial
    inclusion_action x
    ((semidirectStabilizerFactors_iff_productStabilizerFactorization
      fieldH compatibleH x).mp levi_factorization)

end ModularRep.PaperProofs.TypeBRankThreeJordanOvergroup


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
