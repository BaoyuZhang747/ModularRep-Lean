import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Integer polynomial identities, checked by kernel reduction, imply field equations. -/

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck

abbrev ZPoly := List ℤ

def add : ZPoly → ZPoly → ZPoly
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: add p q

def scale (a : ℤ) : ZPoly → ZPoly
  | [] => []
  | b :: p => (a * b) :: scale a p

def mul : ZPoly → ZPoly → ZPoly
  | [], _ => []
  | a :: p, q => add (scale a q) (0 :: mul p q)

def sub (p q : ZPoly) : ZPoly := add p (scale (-1) q)

def monomial : ℕ → ℤ → ZPoly
  | 0, a => [a]
  | n + 1, a => 0 :: monomial n a

def checkZero : ZPoly → Bool
  | [] => true
  | a :: p => decide (a = 0) && checkZero p

def checkEq (p q : ZPoly) : Bool := checkZero (sub p q)

section Evaluation
variable {K : Type*} [CommRing K]

def eval (x : K) : ZPoly → K
  | [] => 0
  | a :: p => (a : K) + x * eval x p

theorem eval_add (x : K) (p q : ZPoly) :
    eval x (add p q) = eval x p + eval x q := by
  induction p generalizing q with
  | nil => simp [add, eval]
  | cons a p ih =>
      cases q with
      | nil => simp [add, eval]
      | cons b q =>
          simp only [add, eval, Int.cast_add, ih]
          ring

theorem eval_scale (x : K) (a : ℤ) (p : ZPoly) :
    eval x (scale a p) = (a : K) * eval x p := by
  induction p with
  | nil => simp [scale, eval]
  | cons b p ih =>
      simp only [scale, eval, Int.cast_mul, ih]
      ring

theorem eval_mul (x : K) (p q : ZPoly) :
    eval x (mul p q) = eval x p * eval x q := by
  induction p with
  | nil => simp [mul, eval]
  | cons a p ih =>
      rw [mul, eval_add, eval_scale]
      simp only [eval, Int.cast_zero, zero_add, ih]
      ring

theorem eval_sub (x : K) (p q : ZPoly) :
    eval x (sub p q) = eval x p - eval x q := by
  simp [sub, eval_add, eval_scale, sub_eq_add_neg]

theorem eval_monomial (x : K) (n : ℕ) (a : ℤ) :
    eval x (monomial n a) = (a : K) * x ^ n := by
  induction n with
  | zero => simp [monomial, eval]
  | succ n ih =>
      simp only [monomial, eval, Int.cast_zero, zero_add, ih, pow_succ]
      ring

theorem checkZero_sound (x : K) (p : ZPoly) :
    checkZero p = true → eval x p = 0 := by
  induction p with
  | nil => intro h; rfl
  | cons a p ih =>
      intro h
      have ha : a = 0 ∧ checkZero p = true := by
        simpa [checkZero] using h
      simp only [eval, ha.1, Int.cast_zero, ih ha.2, mul_zero, add_zero]

theorem checkEq_sound (x : K) (p q : ZPoly)
    (h : checkEq p q = true) : eval x p = eval x q := by
  apply sub_eq_zero.mp
  rw [← eval_sub]
  exact checkZero_sound x _ h

theorem eval_eq_const_of_check (x : K) (p f q : ZPoly) (c : ℤ)
    (hf : eval x f = 0)
    (hcheck : checkEq p (add (mul f q) [c]) = true) :
    eval x p = (c : K) := by
  have h := checkEq_sound x p (add (mul f q) [c]) hcheck
  rw [eval_add, eval_mul, hf] at h
  simpa [eval] using h

end Evaluation
end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
