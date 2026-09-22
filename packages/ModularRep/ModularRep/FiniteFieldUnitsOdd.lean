import ModularRep.OddOrderPower
import Mathlib.FieldTheory.Finite.Basic

/-!
# Units of a finite field of characteristic two

This file isolates the finite field cardinality step used in the conformal
factorisation in manuscript Proposition 3.9.  The multiplicative group of a
finite field of characteristic two has odd order, so squaring on that group
is bijective and every nonzero field element has a unique square root.
-/

namespace ModularRep.ManuscriptVerification.FiniteFieldUnitsOdd

/-- The multiplicative group of a finite field of characteristic two has odd
cardinality. -/
theorem odd_natCard_units_of_char_two
    (k : Type*) [Field k] [Finite k] [CharP k 2] :
    Odd (Nat.card kˣ) := by
  classical
  let _ := Fintype.ofFinite k
  rw [Nat.card_units]
  apply Nat.Even.sub_odd Nat.card_pos
  · rw [Nat.even_iff]
    simpa [Nat.card_eq_fintype_card] using
      (FiniteField.even_card_of_char_two (F := k) (ringChar.eq k 2))
  · exact odd_one

/-- Squaring is a bijection on the multiplicative group of a finite field of
characteristic two. -/
theorem pow_two_bijective_units_of_char_two
    (k : Type*) [Field k] [Finite k] [CharP k 2] :
    Function.Bijective (fun x : kˣ ↦ x ^ 2) :=
  ModularRep.pow_two_bijective_of_odd_card
    (odd_natCard_units_of_char_two k)

/-- Every nonzero element of a finite field of characteristic two has a
unique square root in its multiplicative group. -/
theorem existsUnique_sq_eq_units_of_char_two
    (k : Type*) [Field k] [Finite k] [CharP k 2] (a : kˣ) :
    ∃! x : kˣ, x ^ 2 = a :=
  ModularRep.existsUnique_sq_eq_of_odd_card
    (odd_natCard_units_of_char_two k) a

end ModularRep.ManuscriptVerification.FiniteFieldUnitsOdd


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
