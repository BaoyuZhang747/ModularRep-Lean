import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-!
# Exhaustiveness of the symplectic case division

This file checks the logical case division at the end of the symplectic
section.  It assumes the elementary field description and, for
`Sp₆(2)`, the list of odd prime divisors supplied by the group-order
calculation.  It proves that every admissible parameter tuple belongs to one
of the eight cases listed in the manuscript.

The result does not prove the representation theoretic theorem assigned to
any case.
-/

namespace Formalisation

/-- The eight branches in the proof of the symplectic theorem. -/
inductive SymplecticCase (n q ell p f : ℕ) : Prop
  | rankTwo (hn : n = 2) (hq : 2 < q)
  | definingPrime (hn : 3 ≤ n) (hell : ell = p)
  | oddFieldAtTwo (hn : 3 ≤ n) (hq : Odd q) (hell : ell = 2)
  | oddFieldOddPrime (hn : 3 ≤ n) (hq : Odd q)
      (hndef : ell ≠ p) (hell : Odd ell)
  | sp6AtFiveOrSeven (hn : n = 3) (hq : q = 2)
      (hell : ell = 5 ∨ ell = 7)
  | sp6AtThree (hn : n = 3) (hq : q = 2) (hell : ell = 3)
  | evenFieldRankThree (hn : n = 3) (hp : p = 2)
      (hq : q = 2 ^ f) (hf : 2 ≤ f) (hell : Odd ell)
  | evenFieldHigherRank (hn : 4 ≤ n) (hp : p = 2)
      (hq : q = 2 ^ f) (hf : 0 < f) (hell : Odd ell)

/-- The eight cases in the manuscript exhaust the admissible parameters.

`hfield` is the parity dichotomy used by this finite case split.  Its right
branch records that an even field has characteristic two and order `2 ^ f`.
The prime-power interpretation of the odd branch is supplied separately by
the manuscript-specific semantic realisation.
`hsp6` is precisely the elementary order calculation that the odd
nondefining primes for `Sp₆(2)` are `3`, `5`, and `7`. -/
theorem symplectic_case_exhaustion
    (n q ell p f : ℕ)
    (hn : 2 ≤ n) (hq : 2 ≤ q)
    (hsimple : ¬ (n = 2 ∧ q = 2))
    (hellPrime : Nat.Prime ell)
    (hfield : Odd q ∨ (p = 2 ∧ q = 2 ^ f ∧ 0 < f))
    (hsp6 : n = 3 → q = 2 → ell ≠ p →
      ell = 3 ∨ ell = 5 ∨ ell = 7) :
    SymplecticCase n q ell p f := by
  by_cases hn2 : n = 2
  · apply SymplecticCase.rankTwo hn2
    omega
  have hn3 : 3 ≤ n := by omega
  by_cases hdef : ell = p
  · exact SymplecticCase.definingPrime hn3 hdef
  rcases hfield with hqOdd | ⟨hp, hqPow, hf⟩
  · rcases hellPrime.eq_two_or_odd' with hellTwo | hellOdd
    · exact SymplecticCase.oddFieldAtTwo hn3 hqOdd hellTwo
    · exact SymplecticCase.oddFieldOddPrime hn3 hqOdd hdef hellOdd
  · have hellNeTwo : ell ≠ 2 := by
      intro hellTwo
      apply hdef
      omega
    have hellOdd : Odd ell := hellPrime.odd_of_ne_two hellNeTwo
    by_cases hnEqThree : n = 3
    · by_cases hqTwo : q = 2
      · rcases hsp6 hnEqThree hqTwo hdef with hellThree | hellFive | hellSeven
        · exact SymplecticCase.sp6AtThree hnEqThree hqTwo hellThree
        · exact SymplecticCase.sp6AtFiveOrSeven hnEqThree hqTwo (Or.inl hellFive)
        · exact SymplecticCase.sp6AtFiveOrSeven hnEqThree hqTwo (Or.inr hellSeven)
      · have hfNeOne : f ≠ 1 := by
          intro hfOne
          subst f
          norm_num at hqPow
          exact hqTwo hqPow
        have hfTwo : 2 ≤ f := by omega
        exact SymplecticCase.evenFieldRankThree hnEqThree hp hqPow hfTwo hellOdd
    · have hnFour : 4 ≤ n := by omega
      exact SymplecticCase.evenFieldHigherRank hnFour hp hqPow hf hellOdd

end Formalisation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
