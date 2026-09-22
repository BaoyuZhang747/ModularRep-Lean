import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-!
# Exhaustiveness of the case division in the type B theorem

This file checks the final deduction of manuscript Theorem 4.1.  The
deep representation theoretic propositions remain four separately named
inputs, each already asserting the branch conclusion.  Lean proves only that
a prime is either the defining prime, an odd
nondefining prime, or the prime two, and that the last case is divided by
rank three versus rank at least four.
-/

namespace ModularRep.ManuscriptVerification.TypeBCaseCoverage

/-- The four branch results used in the proof of manuscript Theorem 4.1. -/
structure Inputs (Verified : Prop) (p n ell : ℕ) where
  definingPrime : ell = p → Verified
  oddNondefiningPrime : Odd ell → ell ≠ p → Verified
  twoRankThree : ell = 2 → n = 3 → Verified
  twoRankAtLeastFour : ell = 2 → 4 ≤ n → Verified

/-- The branch results exhaust all primes and all ranks `n ≥ 3` occurring in
the odd-characteristic type B theorem. -/
theorem verified_of_case_inputs
    {Verified : Prop} {p n ell : ℕ}
    (hell : ell.Prime) (hn : 3 ≤ n)
    (D : Inputs Verified p n ell) : Verified := by
  by_cases hdef : ell = p
  · exact D.definingPrime hdef
  · rcases hell.eq_two_or_odd' with hellTwo | hellOdd
    · rcases show n = 3 ∨ 4 ≤ n by omega with hnThree | hnFour
      · exact D.twoRankThree hellTwo hnThree
      · exact D.twoRankAtLeastFour hellTwo hnFour
    · exact D.oddNondefiningPrime hellOdd hdef

end ModularRep.ManuscriptVerification.TypeBCaseCoverage


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
