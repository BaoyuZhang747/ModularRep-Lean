import ModularRep.PaperProofs.TypeBLeviReturnPowerFixedPoints

/-!
# The return power as an automorphism of the same fixed-point group

For a positive defining exponent s, the r-th power of an endomorphism on
its s-th-power fixed points has explicit inverse of exponent r * (s - 1).
This construction requires neither global invertibility nor finiteness.
Its forward endomorphism is exactly the previously constructed fixedPowerEnd.

This is support for the simultaneous-return argument of the current Type B
manuscript, lines 932--956. It does not supply the specified component/model
identification, a field/graph classification or a factor selector.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBLeviReturnPowerAutomorphism

open TypeBRegularLeviRationalCarriers
open TypeBLeviReturnPowerFixedPoints

variable {B : Type*} [Group B]

/-- Positivity comes from the original defining exponent and component period. -/
theorem defining_multiplier_pos (h d u s : ℕ) (hpos : 0 < h) (dpos : 0 < d)
    (exponent : h * d = u * s) : 0 < s := by
  apply Nat.pos_of_ne_zero
  intro hs
  have hpositive : 0 < h * d := Nat.mul_pos hpos dpos
  rw [exponent, hs, Nat.mul_zero] at hpositive
  exact (Nat.lt_irrefl 0) hpositive

/-- Any multiple of the defining power fixes the same fixed-point element. -/
theorem multiple_power_fixed (Φ : Monoid.End B) (s n : ℕ)
    (x : fixedPoints (Φ ^ s)) : (Φ ^ (s * n)) x.1 = x.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Nat.mul_succ, pow_add]
      change (Φ ^ (s * n)) ((Φ ^ s) x.1) = x.1
      rw [show (Φ ^ s) x.1 = x.1 from x.2]
      exact ih

/-- The two displayed inverse exponents sum to a defining-power multiple. -/
theorem inverse_exponent (r s : ℕ) (hs : 0 < s) :
    r * (s - 1) + r = s * r := by
  rw [← Nat.mul_succ, Nat.succ_eq_add_one,
    Nat.sub_add_cancel (Nat.succ_le_of_lt hs), Nat.mul_comm]

/-- The canonical return automorphism, with its literal positive-power inverse. -/
def fixedPowerAut (Φ : Monoid.End B) (r s : ℕ) (hs : 0 < s) :
    MulAut (fixedPoints (Φ ^ s)) where
  toFun := fixedPowerEnd Φ r s
  invFun := fixedPowerEnd Φ (r * (s - 1)) s
  left_inv x := by
    apply Subtype.ext
    change (Φ ^ (r * (s - 1)) * Φ ^ r) x.1 = x.1
    rw [← pow_add, inverse_exponent r s hs]
    exact multiple_power_fixed Φ s r x
  right_inv x := by
    apply Subtype.ext
    change (Φ ^ r * Φ ^ (r * (s - 1))) x.1 = x.1
    rw [← pow_add, Nat.add_comm r (r * (s - 1)), inverse_exponent r s hs]
    exact multiple_power_fixed Φ s r x
  map_mul' x y := (fixedPowerEnd Φ r s).map_mul x y

@[simp] theorem fixedPowerAut_value (Φ : Monoid.End B) (r s : ℕ) (hs : 0 < s)
    (x : fixedPoints (Φ ^ s)) :
    (fixedPowerAut Φ r s hs x).1 = (Φ ^ r) x.1 := rfl

@[simp] theorem fixedPowerAut_symm_value (Φ : Monoid.End B) (r s : ℕ) (hs : 0 < s)
    (x : fixedPoints (Φ ^ s)) :
    ((fixedPowerAut Φ r s hs).symm x).1 = (Φ ^ (r * (s - 1))) x.1 := rfl

/-- The upgrade preserves the exact endomorphism used in the coordinate square. -/
@[simp] theorem fixedPowerAut_toMonoidHom (Φ : Monoid.End B) (r s : ℕ) (hs : 0 < s) :
    (fixedPowerAut Φ r s hs).toMonoidHom = fixedPowerEnd Φ r s := rfl

/-- Power values remain values of the same original endomorphism. -/
theorem fixedPowerAut_pow_value (Φ : Monoid.End B) (r s : ℕ) (hs : 0 < s)
    (n : ℕ) (x : fixedPoints (Φ ^ s)) :
    ((fixedPowerAut Φ r s hs ^ n) x).1 = (Φ ^ (r * n)) x.1 := by
  rw [pow_mul]
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [pow_succ']
      change (Φ ^ r) ((fixedPowerAut Φ r s hs ^ n) x).1 =
        (Φ ^ r) (((Φ ^ r) ^ n) x.1)
      exact congrArg (Φ ^ r) ih

/-- The return is literally a power of the restricted common Frobenius. -/
theorem fixedPowerAut_eq_generator_power (Φ : Monoid.End B) (r s : ℕ) (hs : 0 < s) :
    fixedPowerAut Φ r s hs = fixedPowerAut Φ 1 s hs ^ r := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  simpa only [Nat.one_mul, fixedPowerAut_value] using
    (fixedPowerAut_pow_value Φ 1 s hs r x).symm

/-- A derived ambient-value equation identifies an actual return automorphism. -/
theorem fixedPowerAut_eq_of_value (Φ : Monoid.End B) (r s : ℕ) (hs : 0 < s)
    (actual : MulAut (fixedPoints (Φ ^ s)))
    (values : ∀ x, (actual x).1 = (Φ ^ r) x.1) :
    actual = fixedPowerAut Φ r s hs := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  exact values x

end ModularRep.PaperProofs.TypeBLeviReturnPowerAutomorphism


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
