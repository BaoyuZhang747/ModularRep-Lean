import Mathlib.FieldTheory.Finite.Basic
import ModularRep.TypeCCaseCoverage
import ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation

/-!
# Actual finite-field numerical cases for Type C

The field order is always Nat.card F and the defining characteristic comes
from CharP F p. The helpers derive the precise prime, parity and exponent
guards used by the existing case endpoints. The selector returns numerical
proofs only, with defining characteristic tested first.

No branch conclusion or arbitrary Verified predicate is an input. The
original prime divisor of the simple-group order remains an application
premise; its transport through the actual Sp-to-PSp quotient is recorded
separately. The numerical Sp6(2) case does not assume an exceptional prime
list or replace the actual odd-prime double cover.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeCActualNumericalCases

open OddTwoConformalProjectiveRealisation (Sp PSp spProjection)

section FieldGuards

variable (F : Type) [Field F] [Finite F] (p : ℕ) [CharP F p]

include F in
/-- The prime is derived from the characteristic of the actual finite field. -/
theorem characteristic_prime : Nat.Prime p := CharP.char_is_prime F p

/-- The positive exponent belongs to the actual field cardinality. -/
theorem card_prime_power : ∃ a : ℕ, 0 < a ∧ Nat.card F = p ^ a := by
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨a, _, ha⟩ := FiniteField.card F p
  exact ⟨a, a.pos, by simpa only [Nat.card_eq_fintype_card] using ha⟩

theorem characteristic_dvd_card : p ∣ Nat.card F := by
  obtain ⟨a, ha, hcard⟩ := card_prime_power F p
  rw [hcard]
  exact dvd_pow_self p ha.ne'

/-- At a prime coefficient characteristic, numerical nondefining means
exactly the nondivisibility needed by the existing odd-prime endpoints. -/
theorem not_dvd_card_of_ne (ell : ℕ) (prime : Nat.Prime ell) (hne : ell ≠ p) :
    ¬ ell ∣ Nat.card F := by
  intro hdiv
  obtain ⟨a, _, hcard⟩ := card_prime_power F p
  rw [hcard] at hdiv
  have hbase : ell ∣ p := prime.dvd_of_dvd_pow hdiv
  exact hne ((Nat.prime_dvd_prime_iff_eq prime (characteristic_prime F p)).mp hbase)

theorem not_dvd_card_iff_ne (ell : ℕ) (prime : Nat.Prime ell) :
    (¬ ell ∣ Nat.card F) ↔ ell ≠ p := by
  constructor
  · intro h hEq
    subst ell
    exact h (characteristic_dvd_card F p)
  · exact not_dvd_card_of_ne F p ell prime

/-- The old numerical prime-power lemma is applied to this actual field. -/
theorem characteristic_eq_two_of_even (heven : Even (Nat.card F)) : p = 2 := by
  obtain ⟨a, _, hcard⟩ := card_prime_power F p
  exact ManuscriptVerification.TypeCCaseCoverage.prime_eq_two_of_even_pow
    (characteristic_prime F p) hcard heven

include p in
/-- A caller may install this derived instance for the even-field APIs. -/
theorem charP_two_of_even (heven : Even (Nat.card F)) : CharP F 2 := by
  have hp := characteristic_eq_two_of_even F p heven
  subst p
  infer_instance

theorem even_nondefining_prime (ell : ℕ) (prime : Nat.Prime ell)
    (heven : Even (Nat.card F)) (hne : ell ≠ p) :
    p = 2 ∧ ell ≠ 2 ∧ Odd ell := by
  have hp := characteristic_eq_two_of_even F p heven
  have hell : ell ≠ 2 := fun h => hne (h.trans hp.symm)
  exact ⟨hp, hell, prime.odd_of_ne_two hell⟩

include p in
/-- A positive actual even-field exponent is exposed without a chosen
finite-field presentation or any rank restriction. -/
theorem even_card_power (heven : Even (Nat.card F)) :
    ∃ a : ℕ, 0 < a ∧ Nat.card F = 2 ^ a := by
  have hp := characteristic_eq_two_of_even F p heven
  subst p
  exact card_prime_power F 2

include p in
/-- The exact a>=2 guard of the low-rank even-field source. -/
theorem even_card_power_at_least_two (heven : Even (Nat.card F))
    (hcard : 2 < Nat.card F) : ∃ a : ℕ, 2 ≤ a ∧ Nat.card F = 2 ^ a := by
  obtain ⟨a, ha, hpower⟩ := even_card_power F p heven
  refine ⟨a, ?_, hpower⟩
  by_contra h
  have hone : a = 1 := by omega
  rw [hone, pow_one] at hpower
  omega

end FieldGuards

section RankAndOrder

variable (F : Type) [Field F] [Finite F]

/-- The only small-rank exclusion gives the exact q>2 source guard. -/
theorem rank_two_card_gt_two (n : ℕ)
    (notSmall : ¬ (n = 2 ∧ Nat.card F = 2)) (hn : n = 2) :
    2 < Nat.card F := by
  have htwo : 2 ≤ Nat.card F := Finite.one_lt_card
  have hne : Nat.card F ≠ 2 := fun h => notSmall ⟨hn, h⟩
  omega

/-- The original simple-order divisor is carried through the actual
canonical projection, without an external order formula. -/
theorem dvd_matrix_order_of_dvd_simple_order (n ell : ℕ)
    (divides : ell ∣ Nat.card (PSp n F)) : ell ∣ Nat.card (Sp n F) :=
  divides.trans (Subgroup.card_dvd_of_surjective (spProjection n F)
    (QuotientGroup.mk'_surjective _))

end RankAndOrder

/-- Numerical applicability alternatives only. No character-theoretic
conclusion is present. All q coordinates are later instantiated by Nat.card F. -/
inductive NumericalCase (n p ell q : ℕ) : Type
  | defining (equal : ell = p)
  | oddTwo (fieldOdd : Odd q) (equal : ell = 2)
      (nondefining : ell ≠ p) (notDvd : ¬ ell ∣ q)
  | rankTwoEven (rank : n = 2) (characteristic : p = 2)
      (fieldEven : Even q) (fieldLarge : 2 < q) (primeOdd : Odd ell)
      (nondefining : ell ≠ p) (notDvd : ¬ ell ∣ q)
  | rankTwoOdd (rank : n = 2) (fieldOdd : Odd q) (primeOdd : Odd ell)
      (nondefining : ell ≠ p) (notDvd : ¬ ell ∣ q)
  | oddHigherRank (rank : 3 ≤ n) (fieldOdd : Odd q) (primeOdd : Odd ell)
      (nondefining : ell ≠ p) (notDvd : ¬ ell ∣ q)
  | sp6Two (rank : n = 3) (characteristic : p = 2) (fieldTwo : q = 2)
      (primeOdd : Odd ell) (nondefining : ell ≠ p) (notDvd : ¬ ell ∣ q)
  | rankThreeEven (rank : n = 3) (characteristic : p = 2)
      (fieldEven : Even q) (fieldLarge : 2 < q) (primeOdd : Odd ell)
      (nondefining : ell ≠ p) (notDvd : ¬ ell ∣ q)
  | evenHigherRank (rank : 4 ≤ n) (characteristic : p = 2)
      (fieldEven : Even q) (primeOdd : Odd ell)
      (nondefining : ell ≠ p) (notDvd : ¬ ell ∣ q)

/-- Defining-first selection on the actual finite-field parameters. The
simple-order divisor is not needed for numerical exhaustiveness and stays
unchanged in the later source call. The actual Sp6 source will derive 3/5/7. -/
def numericalCase (n p ell : ℕ) (F : Type) [Field F] [Finite F] [CharP F p]
    (prime : Nat.Prime ell) (rank : 2 ≤ n)
    (notSmall : ¬ (n = 2 ∧ Nat.card F = 2)) :
    NumericalCase n p ell (Nat.card F) := by
  classical
  by_cases hdef : ell = p
  · exact .defining hdef
  have hnotDvd := not_dvd_card_of_ne F p ell prime hdef
  by_cases hodd : Odd (Nat.card F)
  · by_cases htwo : ell = 2
    · exact .oddTwo hodd htwo hdef hnotDvd
    have hellOdd := prime.odd_of_ne_two htwo
    by_cases hn : n = 2
    · exact .rankTwoOdd hn hodd hellOdd hdef hnotDvd
    · exact .oddHigherRank (by omega) hodd hellOdd hdef hnotDvd
  · have heven : Even (Nat.card F) := (Nat.even_or_odd _).resolve_right hodd
    have hp : p = 2 := characteristic_eq_two_of_even F p heven
    have hellNe : ell ≠ 2 := fun h => hdef (h.trans hp.symm)
    have hellOdd := prime.odd_of_ne_two hellNe
    by_cases hnTwo : n = 2
    · exact .rankTwoEven hnTwo hp heven
        (rank_two_card_gt_two F n notSmall hnTwo) hellOdd hdef hnotDvd
    by_cases hnThree : n = 3
    · by_cases hqTwo : Nat.card F = 2
      · exact .sp6Two hnThree hp hqTwo hellOdd hdef hnotDvd
      · have hqLe : 2 ≤ Nat.card F := Finite.one_lt_card
        exact .rankThreeEven hnThree hp heven (by omega) hellOdd hdef hnotDvd
    · exact .evenHigherRank (by omega) hp heven hellOdd hdef hnotDvd

end ModularRep.PaperProofs.TypeCActualNumericalCases


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
