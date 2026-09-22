import Mathlib.GroupTheory.OrderOfElement

/-!
# Squaring in groups of odd finite order

This file records the reusable group-theoretic fact that squaring is
bijective in a finite group of odd order.  Its use in the even-field
conformal argument still requires the concrete multiplicative group of the
finite field to be identified and shown to have odd cardinality.
-/

namespace ModularRep

/-- Squaring is bijective on a finite group of odd order. -/
theorem pow_two_bijective_of_odd_card
    {G : Type*} [Group G] [Finite G]
    (hOdd : Odd (Nat.card G)) :
    Function.Bijective (fun x : G ↦ x ^ 2) :=
  Nat.Coprime.pow_left_bijective hOdd.coprime_two_right

/-- Every element of a finite group of odd order has a unique square root. -/
theorem existsUnique_sq_eq_of_odd_card
    {G : Type*} [Group G] [Finite G]
    (hOdd : Odd (Nat.card G)) (a : G) :
    ∃! x : G, x ^ 2 = a := by
  let hBijective := pow_two_bijective_of_odd_card (G := G) hOdd
  obtain ⟨x, hx⟩ := hBijective.surjective a
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact hBijective.injective (hy.trans hx.symm)

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
