import ModularRep.PaperProofs.TypeBOrthogonalOmegaCarriers

/-!
# Prime cases for the actual finite Type B quotient

The finite-field calculation turns `ell ≠ p` into the nondefining guard
`¬ ell ∣ Nat.card F`. Every prime divisor of the independently defined
matrix Omega order is then classified into defining characteristic, an
odd nondefining prime, or prime two. The prime-two branch retains the
exact numerical exceptional-cover guard `(n, Nat.card F) = (3, 3)`.

All conclusions here are arithmetic or structural. No block condition,
character correspondence, selected cover or iBAW proposition is supplied.
The existing branch endpoints retain their own literal cover sources.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBCurrentPrimeCases

open TypeBCliffordCarriers

/-- The reusable arithmetic step needs only a genuine prime-power field
order, with positive exponent. -/
theorem prime_dvd_prime_power_iff {ell p f : ℕ}
    (prime : Nat.Prime ell) (definingPrime : Nat.Prime p) (positive : 0 < f) :
    ell ∣ p ^ f ↔ ell = p := by
  constructor
  · exact Nat.prime_eq_prime_of_dvd_pow prime definingPrime
  · rintro rfl
    exact dvd_pow_self _ (Nat.ne_of_gt positive)

variable {n p f ell : ℕ} {F : Type} [Field F] [Finite F] [CharP F p]
variable (parameters : OddFieldParameters F p f)

include parameters

/-- No independent nondefining-field premise is needed once the two
actual primes are known to differ. -/
theorem prime_not_dvd_card_iff_ne (prime : Nat.Prime ell) :
    ¬ ell ∣ Nat.card F ↔ ell ≠ p := by
  rw [parameters.cardinality,
    prime_dvd_prime_power_iff prime parameters.prime parameters.exponent_pos]

theorem nondefining_of_ne (prime : Nat.Prime ell) (different : ell ≠ p) :
    ¬ ell ∣ Nat.card F :=
  (prime_not_dvd_card_iff_ne parameters prime).mpr different

/-- The exceptional field-order equation pins both defining parameters. -/
theorem exceptional_parameters (exceptional : (n, Nat.card F) = (3, 3)) :
    n = 3 ∧ p = 3 ∧ f = 1 := by
  have cardinality : Nat.card F = 3 := congrArg Prod.snd exceptional
  have power : p ^ f = 3 := parameters.cardinality.symm.trans cardinality
  exact ⟨congrArg Prod.fst exceptional, (Nat.prime_three.pow_eq_iff.mp power)⟩

/-- Exhaustive arithmetic alternatives. Odd nondefining primes retain
both numerical cover alternatives, and the exceptional prime-two branch
records the field characteristic and exponent it actually forces. -/
inductive PrimeCase (n p f q ell : ℕ) : Type
  | defining (same : ell = p)
  | oddNondefining (odd : Odd ell) (different : ell ≠ p)
      (nondefining : ¬ ell ∣ q)
      (coverCases : (n, q) = (3, 3) ∨ (n, q) ≠ (3, 3))
      (exceptionalNondefining : (n, q) = (3, 3) → ell ≠ 3)
  | twoGeneric (same : ell = 2) (nondefining : ¬ ell ∣ q)
      (generic : (n, q) ≠ (3, 3))
  | twoExceptional (same : ell = 2) (nondefining : ¬ ell ∣ q)
      (exceptional : (n, q) = (3, 3)) (definingPrime : p = 3) (exponent : f = 1)

/-- The classifier is derived for every prime, so its later specialization
to the actual Omega order introduces no missing prime-divisor branch. -/
def classify (n : ℕ) (prime : Nat.Prime ell) :
    PrimeCase n p f (Nat.card F) ell := by
  classical
  by_cases defining : ell = p
  · exact .defining defining
  have nondefining := nondefining_of_ne parameters prime defining
  by_cases two : ell = 2
  · by_cases exceptional : (n, Nat.card F) = (3, 3)
    · obtain ⟨_, hp, hf⟩ := exceptional_parameters parameters exceptional
      exact .twoExceptional two nondefining exceptional hp hf
    · exact .twoGeneric two nondefining exceptional
  · exact .oddNondefining (prime.odd_of_ne_two two) defining nondefining
      (Classical.em _) (fun exceptional => by
        have hp := (exceptional_parameters parameters exceptional).2.1
        exact fun h => defining (h.trans hp.symm))

/-- This packet is indexed by the independently defined actual matrix
Omega group. The noncommutativity condition remains distinct from
simplicity; the divisor is not replaced by a supplied group order. -/
structure PrimeDivisorInput (n : ℕ) (F : Type) [Field F] (ell : ℕ) : Prop where
  prime : Nat.Prime ell
  divides : ell ∣ Nat.card (TypeBOrthogonalOmegaCarriers.Omega n F)
  simple : IsSimpleGroup (TypeBOrthogonalOmegaCarriers.Omega n F)
  nonabelian : ¬ IsMulCommutative (TypeBOrthogonalOmegaCarriers.Omega n F)

/-- The output retains the same actual divisor and structural source
facts alongside the proved prime/exceptional-cover case. -/
structure ClassifiedPrimeDivisor (n p f : ℕ) (F : Type) [Field F] (ell : ℕ) where
  actual : PrimeDivisorInput n F ell
  branch : PrimeCase n p f (Nat.card F) ell

/-- Case coverage on the original Omega order. No group property is
inferred from the numerical classifier. -/
def classify_prime_divisor (actual : PrimeDivisorInput n F ell) :
    ClassifiedPrimeDivisor n p f F ell where
  actual := actual
  branch := classify parameters n actual.prime

@[simp] theorem classify_prime_divisor_actual (actual : PrimeDivisorInput n F ell) :
    (classify_prime_divisor parameters actual).actual = actual := rfl

end ModularRep.PaperProofs.TypeBCurrentPrimeCases



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
