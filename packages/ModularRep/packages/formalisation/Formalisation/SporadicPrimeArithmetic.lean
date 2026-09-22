import Mathlib

/-!
# Prime support of the four boundary sporadic groups

The group orders below are written in their standard prime-factorised form.
Lean checks that, once these factorizations are accepted, the four prime
lists displayed in the manuscript are exactly their prime supports.  The
identification of these expressions with the orders of the named groups is
still an Atlas/table input, not a theorem proved here.
-/

namespace Formalisation.SporadicPrimeArithmetic

def j4Order : ℕ :=
  2 ^ 21 * 3 ^ 3 * 5 * 7 * 11 ^ 3 * 23 * 29 * 31 * 37 * 43

def fi24Order : ℕ :=
  2 ^ 21 * 3 ^ 16 * 5 ^ 2 * 7 ^ 3 * 11 * 13 * 17 * 23 * 29

def babyOrder : ℕ :=
  2 ^ 41 * 3 ^ 13 * 5 ^ 6 * 7 ^ 2 * 11 * 13 * 17 * 19 * 23 * 31 * 47

def monsterOrder : ℕ :=
  2 ^ 46 * 3 ^ 20 * 5 ^ 9 * 7 ^ 6 * 11 ^ 2 * 13 ^ 3 * 17 * 19 * 23 * 29 *
    31 * 41 * 47 * 59 * 71

def j4PrimeSupport : Finset ℕ := {2, 3, 5, 7, 11, 23, 29, 31, 37, 43}

def fi24PrimeSupport : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 23, 29}

def babyPrimeSupport : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23, 31, 47}

def monsterPrimeSupport : Finset ℕ :=
  {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71}

theorem j4Order_decimal : j4Order = 86775571046077562880 := by
  norm_num [j4Order]

theorem fi24Order_decimal : fi24Order = 1255205709190661721292800 := by
  norm_num [fi24Order]

theorem babyOrder_decimal : babyOrder = 4154781481226426191177580544000000 := by
  norm_num [babyOrder]

theorem monsterOrder_decimal :
    monsterOrder = 808017424794512875886459904961710757005754368000000000 := by
  norm_num [monsterOrder]

theorem prime_dvd_j4Order_iff {p : ℕ} (hp : p.Prime) :
    p ∣ j4Order ↔ p ∈ j4PrimeSupport := by
  unfold j4Order j4PrimeSupport
  simp only [Finset.mem_insert, Finset.mem_singleton, hp.dvd_mul,
    hp.prime.dvd_pow_iff_dvd (by norm_num : 21 ≠ 0),
    hp.prime.dvd_pow_iff_dvd (by norm_num : 3 ≠ 0)]
  norm_num [Nat.prime_dvd_prime_iff_eq hp]
  tauto

theorem prime_dvd_fi24Order_iff {p : ℕ} (hp : p.Prime) :
    p ∣ fi24Order ↔ p ∈ fi24PrimeSupport := by
  unfold fi24Order fi24PrimeSupport
  simp only [Finset.mem_insert, Finset.mem_singleton, hp.dvd_mul,
    hp.prime.dvd_pow_iff_dvd (by norm_num : 21 ≠ 0),
    hp.prime.dvd_pow_iff_dvd (by norm_num : 16 ≠ 0),
    hp.prime.dvd_pow_iff_dvd (by norm_num : 2 ≠ 0),
    hp.prime.dvd_pow_iff_dvd (by norm_num : 3 ≠ 0)]
  norm_num [Nat.prime_dvd_prime_iff_eq hp]
  tauto

theorem prime_dvd_babyOrder_iff {p : ℕ} (hp : p.Prime) :
    p ∣ babyOrder ↔ p ∈ babyPrimeSupport := by
  unfold babyOrder babyPrimeSupport
  simp only [Finset.mem_insert, Finset.mem_singleton, hp.dvd_mul,
    hp.prime.dvd_pow_iff_dvd (by norm_num : 41 ≠ 0),
    hp.prime.dvd_pow_iff_dvd (by norm_num : 13 ≠ 0),
    hp.prime.dvd_pow_iff_dvd (by norm_num : 6 ≠ 0),
    hp.prime.dvd_pow_iff_dvd (by norm_num : 2 ≠ 0)]
  norm_num [Nat.prime_dvd_prime_iff_eq hp]
  tauto

theorem prime_dvd_monsterOrder_iff {p : ℕ} (hp : p.Prime) :
    p ∣ monsterOrder ↔ p ∈ monsterPrimeSupport := by
  unfold monsterOrder monsterPrimeSupport
  simp only [Finset.mem_insert, Finset.mem_singleton, hp.dvd_mul,
    hp.prime.dvd_pow_iff_dvd (by norm_num : 46 ≠ 0),
    hp.prime.dvd_pow_iff_dvd (by norm_num : 20 ≠ 0),
    hp.prime.dvd_pow_iff_dvd (by norm_num : 9 ≠ 0),
    hp.prime.dvd_pow_iff_dvd (by norm_num : 6 ≠ 0),
    hp.prime.dvd_pow_iff_dvd (by norm_num : 2 ≠ 0),
    hp.prime.dvd_pow_iff_dvd (by norm_num : 3 ≠ 0)]
  norm_num [Nat.prime_dvd_prime_iff_eq hp]
  tauto

end Formalisation.SporadicPrimeArithmetic


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
