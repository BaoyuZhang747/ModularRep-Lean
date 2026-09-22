import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRowInverseCertificate
import Mathlib.Tactic.NormNum

/-! Scaled integer identities produce a field row-inverse certificate. -/

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegralRowInverseCertificate

open SporadicFi24P3Definition44NamedCarrierRowInverseCertificate

universe u v w
variable {K : Type u} [Field K] [CharZero K]
variable {Row : Type v} {Column : Type w} {n : ℕ}

def scaledIntegerRowInverseCertificate
    (rows : Row → Column → ℤ) (basis : Fin n → Row) (pivot : Fin n → Column)
    (numerator : Fin n → Fin n → ℤ) (denominator : ℤ) (hdenominator : denominator ≠ 0)
    (inverseChecks : ∀ a b, (∑ j : Fin n, rows (basis a) (pivot j) * numerator j b) =
      if a = b then denominator else 0)
    (coefficients : Row → Fin n → ℤ)
    (reconstructionChecks : ∀ r c,
      rows r c = ∑ a : Fin n, coefficients r a * rows (basis a) c) :
    RowInverseCertificate K (fun r c => (rows r c : K)) n where
  basisPosition := basis
  pivotColumn := pivot
  inverse := fun j b => (numerator j b : K) / (denominator : K)
  right_inverse := by
    have hden : (denominator : K) ≠ 0 := Int.cast_ne_zero.mpr hdenominator
    ext a b
    change (∑ j : Fin n, (rows (basis a) (pivot j) : K) *
      ((numerator j b : K) / (denominator : K))) = if a = b then 1 else 0
    simp_rw [div_eq_mul_inv, ← mul_assoc]
    rw [← Finset.sum_mul]
    have hsum : (∑ j : Fin n, (rows (basis a) (pivot j) : K) * (numerator j b : K)) =
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
    have hcast : (rows r c : K) = ∑ a : Fin n, (coefficients r a : K) * (rows (basis a) c : K) := by
      exact_mod_cast reconstructionChecks r c
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hcast

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegralRowInverseCertificate


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
