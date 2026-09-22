import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic

/-!
# Arithmetic in the even-field Condition 6.1 check

This file isolates the numerical clause used when applying
Feng--Malle--Zhang, Condition 6.1 in the proof of the even-field unipotent
proposition.  It does not verify the remaining algebraic-group, regular
embedding, or automorphism hypotheses of that condition.
-/

namespace ModularRep.ManuscriptVerification.EvenCondition61

/-- An odd prime does not divide a power of two. -/
theorem odd_prime_not_dvd_two_pow
    {ell exponent : ℕ} (hell : ell.Prime) (hOdd : Odd ell) :
    ¬ ell ∣ 2 ^ exponent := by
  intro hdiv
  have hCoprime : Nat.Coprime ell (2 ^ exponent) :=
    hOdd.coprime_two_right.pow_right exponent
  have hellOne : ell = 1 :=
    Nat.eq_one_of_dvd_coprimes hCoprime (dvd_refl ell) hdiv
  exact hell.ne_one hellOne

/-- If `q = 2 ^ a` and the finite fixed centre has cardinality one, then the
divisibility exclusion in Feng--Malle--Zhang, Condition 6.1 follows from
`ell` being an odd prime. -/
theorem condition61_not_dvd_two_q_centre
    {ell q centreCard a : ℕ}
    (hell : ell.Prime) (hOdd : Odd ell)
    (hq : q = 2 ^ a) (hcentre : centreCard = 1) :
    ¬ ell ∣ 2 * q * centreCard := by
  subst q
  subst centreCard
  simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    odd_prime_not_dvd_two_pow (ell := ell) (exponent := a + 1) hell hOdd

end ModularRep.ManuscriptVerification.EvenCondition61


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
