import ModularRep.Sp6DoubleCoverOrder
import Mathlib.Tactic

/-!
# Exhaustiveness of the case division in the type C theorem

The final proof of manuscript Theorem 3.1 divides the parameters by rank,
defining characteristic, parity of the field, and the exceptional group
`Sp₆(2)`.  This file checks that logical case division independently of the
dependency graph.  Each branch is a separately named external or previously
proved result.  Lean receives the conclusion for every branch as an input and
checks only that the branches exhaust the stated numerical parameters.  It
does not verify any branch theorem or the headline type C theorem.

The predicate `Verified` is intentionally abstract: instantiating it with
"the indicated universal `ell'`-cover satisfies iBAW" still requires the
group constructions and the cited branch theorems.  What is kernel checked
here is that those branches exhaust the parameters claimed in the manuscript.
-/

namespace ModularRep.ManuscriptVerification.TypeCCaseCoverage

/-- Exact branch inputs used by the proof of manuscript Theorem 3.1. -/
structure Inputs
    (Verified : Prop) (p q n ell : ℕ) where
  rankTwo : n = 2 → 2 < q → Verified
  definingPrime : 3 ≤ n → ell = p → Verified
  oddFieldAtTwo : 3 ≤ n → Odd q → ell = 2 → Verified
  oddFieldAtOddNondefining :
    3 ≤ n → Odd q → Odd ell → ell ≠ p → Verified
  sp6AtThree : n = 3 → q = 2 → ell = 3 → Verified
  sp6AtFiveOrSeven :
    n = 3 → q = 2 → (ell = 5 ∨ ell = 7) → Verified
  rankThreeLargerEvenField :
    n = 3 → Even q → q ≠ 2 → Odd ell → ell ≠ p → Verified
  rankAtLeastFourEvenField :
    4 ≤ n → Even q → Odd ell → ell ≠ p → Verified

/-- A positive power of a prime is at least two. -/
theorem two_le_prime_pow {p f : ℕ} (hp : p.Prime) (hf : 0 < f) :
    2 ≤ p ^ f := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hf)
  rw [pow_succ]
  have hpow : 0 < p ^ r := pow_pos hp.pos r
  nlinarith [hp.two_le]

/-- An even positive power of a prime has base prime two. -/
theorem prime_eq_two_of_even_pow
    {p f q : ℕ} (hp : p.Prime) (hq : q = p ^ f) (hqEven : Even q) :
    p = 2 := by
  rcases hp.eq_two_or_odd' with hpTwo | hpOdd
  · exact hpTwo
  · have hqOdd : Odd q := by
      rw [hq]
      exact hpOdd.pow
    exact ((Nat.not_even_iff_odd.mpr hqOdd) hqEven).elim

/-- The eight cases listed at the end of the type C section are exhaustive.

`hsp6Order` is the only place where the order of the concrete exceptional
cover enters this abstract coverage theorem.  Lean derives the possible
primes from the factored order in `Sp6DoubleCoverOrder`; all representation
theory remains in the eight individually named branch fields of `Inputs`. -/
theorem verified_of_case_inputs
    {Verified : Prop} {p q n ell f : ℕ}
    (hp : p.Prime) (hell : ell.Prime)
    (hf : 0 < f) (hq : q = p ^ f)
    (hn : 2 ≤ n) (hnotSmall : ¬ (n = 2 ∧ q = 2))
    (hsp6Order : n = 3 → q = 2 →
      ell ∣ Sp6DoubleCoverOrder.sp6DoubleCoverOrder)
    (D : Inputs Verified p q n ell) : Verified := by
  rcases show n = 2 ∨ n = 3 ∨ 4 ≤ n by omega with hnTwo | hnThree | hnFour
  · apply D.rankTwo hnTwo
    have hqTwo : 2 ≤ q := by
      rw [hq]
      exact two_le_prime_pow hp hf
    have hqNe : q ≠ 2 := fun h => hnotSmall ⟨hnTwo, h⟩
    omega
  · have hnAtLeastThree : 3 ≤ n := by omega
    by_cases hdef : ell = p
    · exact D.definingPrime hnAtLeastThree hdef
    · rcases Nat.even_or_odd q with hqEven | hqOdd
      · have hpTwo : p = 2 := prime_eq_two_of_even_pow hp hq hqEven
        have hellNeTwo : ell ≠ 2 := by simpa [hpTwo] using hdef
        have hellOdd : Odd ell := hell.odd_of_ne_two hellNeTwo
        by_cases hqTwo : q = 2
        · rcases Sp6DoubleCoverOrder.prime_dvd_sp6DoubleCoverOrder hell
            (hsp6Order hnThree hqTwo) with
            hellTwo | hellThree | hellFive | hellSeven
          · exact (hellNeTwo hellTwo).elim
          · exact D.sp6AtThree hnThree hqTwo hellThree
          · exact D.sp6AtFiveOrSeven hnThree hqTwo (Or.inl hellFive)
          · exact D.sp6AtFiveOrSeven hnThree hqTwo (Or.inr hellSeven)
        · exact D.rankThreeLargerEvenField
            hnThree hqEven hqTwo hellOdd hdef
      · by_cases hellTwo : ell = 2
        · exact D.oddFieldAtTwo hnAtLeastThree hqOdd hellTwo
        · exact D.oddFieldAtOddNondefining
            hnAtLeastThree hqOdd (hell.odd_of_ne_two hellTwo) hdef
  · have hnAtLeastThree : 3 ≤ n := by omega
    by_cases hdef : ell = p
    · exact D.definingPrime hnAtLeastThree hdef
    · rcases Nat.even_or_odd q with hqEven | hqOdd
      · have hpTwo : p = 2 := prime_eq_two_of_even_pow hp hq hqEven
        have hellNeTwo : ell ≠ 2 := by simpa [hpTwo] using hdef
        exact D.rankAtLeastFourEvenField
          hnFour hqEven (hell.odd_of_ne_two hellNeTwo) hdef
      · by_cases hellTwo : ell = 2
        · exact D.oddFieldAtTwo hnAtLeastThree hqOdd hellTwo
        · exact D.oddFieldAtOddNondefining
            hnAtLeastThree hqOdd (hell.odd_of_ne_two hellTwo) hdef

end ModularRep.ManuscriptVerification.TypeCCaseCoverage


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
