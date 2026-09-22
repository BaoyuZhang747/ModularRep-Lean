import Mathlib.Tactic

/-!
# Finite arithmetic in the GGGR argument

This module verifies two elementary but load-bearing deductions in the proof
of the type `B` GGGR proposition.  Scalar products are nonnegative integers.
If a transitive family of equal scalar products sums to one, it has one term.
If the two entries in a symmetric `2 × 2` fibre block sum to one, that
block is one of the two permutation matrices.

The character-theoretic assertions that the entries are nonnegative, equal
on the appropriate orbits, and have the displayed sums remain external.
-/

namespace Formalisation.GGGRFiniteCore

/-- A nonempty collection of `n` equal nonnegative integer entries can sum
to one only when it consists of the single entry one. -/
theorem equal_entries_sum_one {n a : ℕ} (h : n * a = 1) :
    n = 1 ∧ a = 1 := by
  constructor
  · exact Nat.dvd_one.mp ⟨a, h.symm⟩
  · exact Nat.dvd_one.mp ⟨n, by simpa [Nat.mul_comm] using h.symm⟩

/-- The two symmetric entries in the exceptional fibre give either the
identity matrix or the transposition matrix. -/
theorem symmetric_two_by_two_permutation_cases {a b : ℕ}
    (h : a + b = 1) :
    (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) := by
  omega

/-- In particular, the determinant of the corresponding integer matrix has
absolute value one.  We write it as `a²-b²` without introducing matrix
notation. -/
theorem symmetric_two_by_two_determinant_unit {a b : ℕ}
    (h : a + b = 1) :
    ((a : ℤ) * a - (b : ℤ) * b = 1) ∨
      ((a : ℤ) * a - (b : ℤ) * b = -1) := by
  rcases symmetric_two_by_two_permutation_cases h with h | h
  · rcases h with ⟨rfl, rfl⟩
    norm_num
  · rcases h with ⟨rfl, rfl⟩
    norm_num

end Formalisation.GGGRFiniteCore


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
