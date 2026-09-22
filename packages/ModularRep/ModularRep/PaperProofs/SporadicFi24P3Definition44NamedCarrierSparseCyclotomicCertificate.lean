import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Sparse rational cyclotomic certificates

Explicit polynomial identities express residuals using X^N - 1 and
short geometric sums. No dense cyclotomic polynomial is constructed.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSparseCyclotomicCertificate

universe u v

structure Term (N : ℕ) where
  exponent : Fin N
  numerator : ℤ
  denominator : ℕ
  denominator_pos : 0 < denominator

abbrev Scalar (N : ℕ) := List (Term N)

namespace Term

def toPolynomial {N : ℕ} (t : Term N) : ℚ[X] :=
  Polynomial.C ((t.numerator : ℚ) / (t.denominator : ℚ)) *
    Polynomial.X ^ t.exponent.1

def eval {N : ℕ} {K : Type u} [Field K] [CharZero K]
    (zeta : K) (t : Term N) : K :=
  ((t.numerator : K) / (t.denominator : K)) * zeta ^ t.exponent.1

end Term

namespace Scalar

def toPolynomial {N : ℕ} (s : Scalar N) : ℚ[X] := (s.map Term.toPolynomial).sum

def eval {N : ℕ} {K : Type u} [Field K] [CharZero K]
    (zeta : K) (s : Scalar N) : K := (s.map (Term.eval zeta)).sum

theorem eval_append {N : ℕ} {K : Type u}
    [Field K] [CharZero K] (zeta : K) (s t : Scalar N) :
    eval zeta (s ++ t) = eval zeta s + eval zeta t := by
  simp only [eval, List.map_append, List.sum_append]

end Scalar

section Evaluation

variable {K : Type u} [Field K] [CharZero K]

def ratEval (zeta : K) : ℚ[X] →+* K := Polynomial.eval₂RingHom (Rat.castHom K) zeta

@[simp]
theorem ratEval_X (zeta : K) : ratEval zeta (Polynomial.X : ℚ[X]) = zeta := by
  simp [ratEval]

@[simp]
theorem ratEval_C (zeta : K) (a : ℚ) : ratEval zeta (Polynomial.C a) = (a : K) := by
  simp [ratEval]

@[simp]
theorem ratEval_term {N : ℕ} (zeta : K) (t : Term N) :
    ratEval zeta t.toPolynomial = t.eval zeta := by
  simp [ratEval, Term.toPolynomial, Term.eval]

@[simp]
theorem ratEval_scalar {N : ℕ} (zeta : K) (s : Scalar N) :
    ratEval zeta s.toPolynomial = s.eval zeta := by
  induction s with
  | nil => exact map_zero (ratEval zeta)
  | cons t s ih =>
      change ratEval zeta (t.toPolynomial + Scalar.toPolynomial s) =
        t.eval zeta + Scalar.eval zeta s
      rw [map_add, ratEval_term, ih]

end Evaluation

def torsionPolynomial (N : ℕ) : ℚ[X] := Polynomial.X ^ N - 1

def geometricPolynomial (N q : ℕ) : ℚ[X] :=
  ∑ j ∈ Finset.range q, Polynomial.X ^ ((N / q) * j)

section Annihilation

variable {K : Type u} [Field K] [CharZero K]
variable {N q : ℕ} {zeta : K}

theorem ratEval_torsion_zero (hzeta : IsPrimitiveRoot zeta N) :
    ratEval zeta (torsionPolynomial N) = 0 := by
  simp only [torsionPolynomial, map_sub, map_pow, map_one,
    ratEval_X, hzeta.pow_eq_one, sub_self]

theorem ratEval_geometric_zero
    (hN : 0 < N) (hzeta : IsPrimitiveRoot zeta N) (hq : 1 < q) (hqN : q ∣ N) :
    ratEval zeta (geometricPolynomial N q) = 0 := by
  have hroot : IsPrimitiveRoot (zeta ^ (N / q)) q :=
    IsPrimitiveRoot.pow hN hzeta (Nat.div_mul_cancel hqN).symm
  calc
    ratEval zeta (geometricPolynomial N q) =
        ∑ j ∈ Finset.range q, (zeta ^ (N / q)) ^ j := by
      simp only [geometricPolynomial, map_sum, map_pow, ratEval_X, pow_mul]
    _ = 0 := hroot.geom_sum_eq_zero hq

end Annihilation

/-- Witness coefficients; their polynomial identity must be proved separately. -/
structure AnnihilatorData (N : ℕ) (I : Type v) where
  divisor : I → ℕ
  divisor_gt_one : ∀ i, 1 < divisor i
  divisor_dvd : ∀ i, divisor i ∣ N
  torsionQuotient : ℚ[X]
  geometricQuotient : I → ℚ[X]

namespace AnnihilatorData

variable {N : ℕ} {I : Type v} [Fintype I]

def combination (D : AnnihilatorData N I) : ℚ[X] :=
  torsionPolynomial N * D.torsionQuotient +
    ∑ i, geometricPolynomial N (D.divisor i) * D.geometricQuotient i

theorem ratEval_combination_zero
    {K : Type u} [Field K] [CharZero K]
    (D : AnnihilatorData N I)
    {zeta : K} (hN : 0 < N) (hzeta : IsPrimitiveRoot zeta N) :
    ratEval zeta D.combination = 0 := by
  calc
    ratEval zeta D.combination =
        ratEval zeta (torsionPolynomial N) * ratEval zeta D.torsionQuotient +
          ∑ i, ratEval zeta (geometricPolynomial N (D.divisor i)) *
            ratEval zeta (D.geometricQuotient i) := by
      simp only [combination, map_add, map_mul, map_sum]
    _ = 0 := by
      rw [ratEval_torsion_zero hzeta]
      simp only [zero_mul, zero_add]
      apply Finset.sum_eq_zero
      intro i hi
      rw [ratEval_geometric_zero hN hzeta (D.divisor_gt_one i) (D.divisor_dvd i)]
      exact zero_mul _

theorem ratEval_eq_zero_of_identity
    {K : Type u} [Field K] [CharZero K]
    (D : AnnihilatorData N I)
    {zeta : K} (hN : 0 < N) (hzeta : IsPrimitiveRoot zeta N)
    (P : ℚ[X]) (hidentity : P = D.combination) :
    ratEval zeta P = 0 := by
  rw [hidentity]
  exact D.ratEval_combination_zero hN hzeta

theorem ratEval_eq_of_sub_identity
    {K : Type u} [Field K] [CharZero K]
    (D : AnnihilatorData N I)
    {zeta : K} (hN : 0 < N) (hzeta : IsPrimitiveRoot zeta N)
    (P Q : ℚ[X]) (hidentity : P - Q = D.combination) :
    ratEval zeta P = ratEval zeta Q := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact D.ratEval_eq_zero_of_identity hN hzeta (P - Q) hidentity

theorem scalar_eval_eq_of_sub_identity
    {K : Type u} [Field K] [CharZero K]
    (D : AnnihilatorData N I)
    {zeta : K} (hN : 0 < N) (hzeta : IsPrimitiveRoot zeta N)
    (s t : Scalar N) (hidentity : s.toPolynomial - t.toPolynomial = D.combination) :
    s.eval zeta = t.eval zeta := by
  simpa only [ratEval_scalar] using
    D.ratEval_eq_of_sub_identity hN hzeta s.toPolynomial t.toPolynomial hidentity

end AnnihilatorData

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSparseCyclotomicCertificate


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
