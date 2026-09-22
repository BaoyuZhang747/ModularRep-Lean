import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
import Mathlib.Data.Nat.GCD.Basic

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck

def composeXPow (m : ℕ) : ZPoly → ZPoly
  | [] => []
  | a :: p => add [a] (mul (monomial m 1) (composeXPow m p))

theorem eval_composeXPow {K : Type*} [CommRing K]
    (x : K) (m : ℕ) (p : ZPoly) :
    eval x (composeXPow m p) = eval (x ^ m) p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
      simp only [composeXPow, eval_add, eval_mul, eval_monomial,
        Int.cast_one, one_mul, ih, eval, mul_zero, add_zero]

theorem rootPower_divisor {K : Type*} [Monoid K]
    (zeta : K) {N D d : ℕ} (hDN : D ∣ N) (hdD : d ∣ D) :
    (zeta ^ (N / D)) ^ (D / d) = zeta ^ (N / d) := by
  rw [← pow_mul, Nat.div_mul_div hDN hdD]

theorem rootPower_divisor_mul {K : Type*} [Monoid K]
    (zeta : K) {N D d : ℕ} (hDN : D ∣ N) (hdD : d ∣ D) (e : ℕ) :
    (zeta ^ (N / D)) ^ ((D / d) * e) = (zeta ^ (N / d)) ^ e := by
  rw [← pow_mul, ← mul_assoc, Nat.div_mul_div hDN hdD, pow_mul]

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
