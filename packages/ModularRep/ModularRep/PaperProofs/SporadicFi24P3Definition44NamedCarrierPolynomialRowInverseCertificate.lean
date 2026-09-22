import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialSums
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRowInverseCertificate

/-! Closed polynomial identities give a row inverse, preserving every coordinate root. -/

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPolynomialRowInverseCertificate

open SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open SporadicFi24P3Definition44NamedCarrierRowInverseCertificate

universe u v w
variable {K : Type u} [Field K] [CharZero K]
variable {Row : Type v} {Column : Type w} {n : ℕ}

def scaledPolynomialRowInverseCertificate
    (rows : Row → Column → ZPoly) (roots : Column → K)
    (basis : Fin n → Row) (pivot : Fin n → Column)
    (minor : Fin n → Fin n → ℤ)
    (pivotChecks : ∀ a j, checkEq (rows (basis a) (pivot j)) [minor a j] = true)
    (numerator : Fin n → Fin n → ℤ) (denominator : ℤ) (hdenominator : denominator ≠ 0)
    (inverseChecks : ∀ a b, (∑ j : Fin n, minor a j * numerator j b) =
      if a = b then denominator else 0)
    (coefficients : Row → Fin n → ℤ)
    (reconstructionChecks : ∀ r c, checkEq (rows r c)
      (sumFin fun a : Fin n => scale (coefficients r a) (rows (basis a) c)) = true) :
    RowInverseCertificate K (fun r c => eval (roots c) (rows r c)) n where
  basisPosition := basis
  pivotColumn := pivot
  inverse := fun j b => (numerator j b : K) / (denominator : K)
  right_inverse := by
    have hden : (denominator : K) ≠ 0 := Int.cast_ne_zero.mpr hdenominator
    have hpivot (a j : Fin n) :
        eval (roots (pivot j)) (rows (basis a) (pivot j)) = (minor a j : K) := by
      have h := checkEq_sound (roots (pivot j))
        (rows (basis a) (pivot j)) [minor a j] (pivotChecks a j)
      simpa only [eval, mul_zero, add_zero] using h
    ext a b
    change (∑ j : Fin n, eval (roots (pivot j)) (rows (basis a) (pivot j)) *
      ((numerator j b : K) / (denominator : K))) = if a = b then 1 else 0
    simp_rw [hpivot, div_eq_mul_inv, ← mul_assoc]
    rw [← Finset.sum_mul]
    have hsum : (∑ j : Fin n, (minor a j : K) * (numerator j b : K)) =
        if a = b then (denominator : K) else 0 := by
      exact_mod_cast inverseChecks a b
    rw [hsum]
    by_cases hab : a = b
    · simp only [if_pos hab, mul_inv_cancel₀ hden]
    · simp only [if_neg hab, zero_mul]
  coefficients := fun r a => (coefficients r a : K)
  reconstruct := by
    intro r
    funext c
    have h := checkEq_sound (roots c) (rows r c)
      (sumFin fun a : Fin n => scale (coefficients r a) (rows (basis a) c))
      (reconstructionChecks r c)
    simpa only [eval_sumFin, eval_scale, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPolynomialRowInverseCertificate


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
