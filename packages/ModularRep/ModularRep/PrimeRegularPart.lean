import ModularRep.PrimeRegular
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Prime primary and prime regular parts of a group element

For an element `g` of a finite group and a prime `p`, this file constructs
the canonical commuting decomposition of `g` into its `p`-primary and
`p`-regular parts.  The regular part is selected by the Chinese remainder
exponent which is zero modulo the `p`-part of `orderOf g` and one modulo its
prime-to-`p` part.  Exact orders of both factors are proved.
-/

namespace ModularRep

noncomputable section

variable {G : Type*} [Group G] [Finite G]
variable {p : ℕ}

/-- The `p`-primary part of the order of `g`. -/
def primaryOrderPart (p : ℕ) (g : G) : ℕ :=
  ordProj[p] (orderOf g)

/-- The part of the order of `g` prime to `p`. -/
def regularOrderPart (p : ℕ) (g : G) : ℕ :=
  ordCompl[p] (orderOf g)

omit [Finite G] in
theorem primaryOrderPart_pos (p : ℕ) (g : G) :
    0 < primaryOrderPart p g := by
  exact Nat.ordProj_pos (orderOf g) p

theorem regularOrderPart_pos (p : ℕ) (g : G) :
    0 < regularOrderPart p g := by
  exact Nat.ordCompl_pos p (orderOf_pos g).ne'

omit [Finite G] in
theorem primaryOrderPart_mul_regularOrderPart (p : ℕ) (g : G) :
    primaryOrderPart p g * regularOrderPart p g = orderOf g := by
  exact Nat.ordProj_mul_ordCompl_eq_self (orderOf g) p

theorem primaryOrderPart_coprime_regularOrderPart
    (hp : p.Prime) (g : G) :
    (primaryOrderPart p g).Coprime (regularOrderPart p g) := by
  exact (Nat.coprime_ordCompl hp (orderOf_pos g).ne').pow_left _

/-- The least nonnegative CRT exponent which is zero modulo the `p`-part of
`orderOf g` and one modulo its prime-to-`p` part. -/
def primeRegularCRTExponent (hp : p.Prime) (g : G) : ℕ :=
  Nat.chineseRemainder
    (primaryOrderPart_coprime_regularOrderPart hp g) 0 1

theorem primeRegularCRTExponent_modEq_zero
    (hp : p.Prime) (g : G) :
    primeRegularCRTExponent hp g ≡ 0 [MOD primaryOrderPart p g] := by
  exact (Nat.chineseRemainder
    (primaryOrderPart_coprime_regularOrderPart hp g) 0 1).prop.1

theorem primeRegularCRTExponent_modEq_one
    (hp : p.Prime) (g : G) :
    primeRegularCRTExponent hp g ≡ 1 [MOD regularOrderPart p g] := by
  exact (Nat.chineseRemainder
    (primaryOrderPart_coprime_regularOrderPart hp g) 0 1).prop.2

theorem primeRegularCRTExponent_coprime_regularOrderPart
    (hp : p.Prime) (g : G) :
    (primeRegularCRTExponent hp g).Coprime (regularOrderPart p g) := by
  exact Nat.coprime_of_mul_modEq_one 1 (by
    simpa using primeRegularCRTExponent_modEq_one hp g)

theorem primaryOrderPart_dvd_primeRegularCRTExponent
    (hp : p.Prime) (g : G) :
    primaryOrderPart p g ∣ primeRegularCRTExponent hp g := by
  exact Nat.modEq_zero_iff_dvd.mp
    (primeRegularCRTExponent_modEq_zero hp g)

theorem gcd_orderOf_primeRegularCRTExponent
    (hp : p.Prime) (g : G) :
    Nat.gcd (orderOf g) (primeRegularCRTExponent hp g) =
      primaryOrderPart p g := by
  rw [← primaryOrderPart_mul_regularOrderPart p g, mul_comm]
  exact Nat.gcd_mul_of_coprime_of_dvd
    (primeRegularCRTExponent_coprime_regularOrderPart hp g).symm
    (primaryOrderPart_dvd_primeRegularCRTExponent hp g)

theorem primeRegularCRTExponent_lt_orderOf
    (hp : p.Prime) (g : G) :
    primeRegularCRTExponent hp g < orderOf g := by
  rw [← primaryOrderPart_mul_regularOrderPart p g]
  exact Nat.chineseRemainder_lt_mul
    (primaryOrderPart_coprime_regularOrderPart hp g) 0 1
    (primaryOrderPart_pos p g).ne' (regularOrderPart_pos p g).ne'

/-- The `p`-regular part of `g`, selected by the preceding CRT exponent. -/
def primeRegularPart (hp : p.Prime) (g : G) : G :=
  g ^ primeRegularCRTExponent hp g

/-- The complementary `p`-primary part of `g`. -/
def primePart (hp : p.Prime) (g : G) : G :=
  g * (primeRegularPart hp g)⁻¹

theorem primePart_mul_primeRegularPart (hp : p.Prime) (g : G) :
    primePart hp g * primeRegularPart hp g = g := by
  simp [primePart]

theorem commute_self_primeRegularPart (hp : p.Prime) (g : G) :
    Commute g (primeRegularPart hp g) := by
  exact Commute.self_pow g _

theorem commute_primePart_primeRegularPart (hp : p.Prime) (g : G) :
    Commute (primePart hp g) (primeRegularPart hp g) := by
  unfold primePart
  exact (commute_self_primeRegularPart hp g).mul_left
    (Commute.refl (primeRegularPart hp g)).inv_left

theorem orderOf_primeRegularPart_dvd (hp : p.Prime) (g : G) :
    orderOf (primeRegularPart hp g) ∣ regularOrderPart p g := by
  rw [orderOf_dvd_iff_pow_eq_one, primeRegularPart, ← pow_mul,
    ← orderOf_dvd_iff_pow_eq_one]
  rw [← primaryOrderPart_mul_regularOrderPart p g]
  exact Nat.mul_dvd_mul_right
    (primaryOrderPart_dvd_primeRegularCRTExponent hp g)
    (regularOrderPart p g)

theorem orderOf_primeRegularPart (hp : p.Prime) (g : G) :
    orderOf (primeRegularPart hp g) = regularOrderPart p g := by
  rw [primeRegularPart, orderOf_pow,
    gcd_orderOf_primeRegularCRTExponent hp g,
    ← primaryOrderPart_mul_regularOrderPart p g]
  rw [mul_comm]
  exact Nat.mul_div_left _ (primaryOrderPart_pos p g)

theorem primeRegular_primeRegularPart (hp : p.Prime) (g : G) :
    IsPrimeRegular p (primeRegularPart hp g) := by
  exact Nat.Coprime.of_dvd_left (orderOf_primeRegularPart_dvd hp g)
    (Nat.coprime_ordCompl hp (orderOf_pos g).ne').symm

theorem primeRegularCRTExponent_mul_primaryOrderPart_modEq
    (hp : p.Prime) (g : G) :
    primaryOrderPart p g * primeRegularCRTExponent hp g ≡
      primaryOrderPart p g [MOD orderOf g] := by
  rw [← primaryOrderPart_mul_regularOrderPart p g]
  simpa using
    (primeRegularCRTExponent_modEq_one hp g).mul_left'
      (primaryOrderPart p g)

theorem primeRegularPart_pow_primaryOrderPart
    (hp : p.Prime) (g : G) :
    (primeRegularPart hp g) ^ primaryOrderPart p g =
      g ^ primaryOrderPart p g := by
  rw [primeRegularPart, ← pow_mul, mul_comm]
  exact pow_eq_pow_of_modEq
    (primeRegularCRTExponent_mul_primaryOrderPart_modEq hp g)
    (pow_orderOf_eq_one g)

theorem primePart_pow_primaryOrderPart (hp : p.Prime) (g : G) :
    (primePart hp g) ^ primaryOrderPart p g = 1 := by
  rw [primePart, ((commute_self_primeRegularPart hp g).inv_right).mul_pow,
    inv_pow, primeRegularPart_pow_primaryOrderPart hp g, mul_inv_cancel]

theorem orderOf_primePart_dvd (hp : p.Prime) (g : G) :
    orderOf (primePart hp g) ∣ primaryOrderPart p g := by
  exact orderOf_dvd_of_pow_eq_one (primePart_pow_primaryOrderPart hp g)

theorem orderOf_primePart_dvd_primePower (hp : p.Prime) (g : G) :
    orderOf (primePart hp g) ∣ p ^ (orderOf g).factorization p := by
  exact orderOf_primePart_dvd hp g

theorem orderOf_primePart_coprime_orderOf_primeRegularPart
    (hp : p.Prime) (g : G) :
    (orderOf (primePart hp g)).Coprime
      (orderOf (primeRegularPart hp g)) := by
  exact Nat.Coprime.of_dvd_right (orderOf_primeRegularPart_dvd hp g)
    (Nat.Coprime.of_dvd_left (orderOf_primePart_dvd hp g)
      (primaryOrderPart_coprime_regularOrderPart hp g))

theorem orderOf_primePart (hp : p.Prime) (g : G) :
    orderOf (primePart hp g) = primaryOrderPart p g := by
  apply Nat.mul_right_cancel (regularOrderPart_pos p g)
  calc
    orderOf (primePart hp g) * regularOrderPart p g =
        orderOf (primePart hp g) * orderOf (primeRegularPart hp g) := by
      rw [orderOf_primeRegularPart]
    _ = orderOf (primePart hp g * primeRegularPart hp g) :=
      ((commute_primePart_primeRegularPart hp g).orderOf_mul_eq_mul_orderOf_of_coprime
        (orderOf_primePart_coprime_orderOf_primeRegularPart hp g)).symm
    _ = orderOf g := by rw [primePart_mul_primeRegularPart]
    _ = primaryOrderPart p g * regularOrderPart p g :=
      (primaryOrderPart_mul_regularOrderPart p g).symm

section Naturality

variable {H : Type*} [Group H] [Finite H]

omit [Finite G] [Finite H] in
@[simp]
theorem primaryOrderPart_map_mulEquiv
    (e : G ≃* H) (p : ℕ) (g : G) :
    primaryOrderPart p (e g) = primaryOrderPart p g := by
  simp [primaryOrderPart, MulEquiv.orderOf_eq]

omit [Finite G] [Finite H] in
@[simp]
theorem regularOrderPart_map_mulEquiv
    (e : G ≃* H) (p : ℕ) (g : G) :
    regularOrderPart p (e g) = regularOrderPart p g := by
  simp [regularOrderPart, MulEquiv.orderOf_eq]

@[simp]
theorem primeRegularCRTExponent_map_mulEquiv
    (e : G ≃* H) (hp : p.Prime) (g : G) :
    primeRegularCRTExponent hp (e g) = primeRegularCRTExponent hp g := by
  have hzero :
      primeRegularCRTExponent hp (e g) ≡
        primeRegularCRTExponent hp g [MOD primaryOrderPart p g] :=
    by
      have hleft :
          primeRegularCRTExponent hp (e g) ≡
            0 [MOD primaryOrderPart p g] := by
        simpa using primeRegularCRTExponent_modEq_zero hp (e g)
      exact hleft.trans (primeRegularCRTExponent_modEq_zero hp g).symm
  have hone :
      primeRegularCRTExponent hp (e g) ≡
        primeRegularCRTExponent hp g [MOD regularOrderPart p g] :=
    by
      have hleft :
          primeRegularCRTExponent hp (e g) ≡
            1 [MOD regularOrderPart p g] := by
        simpa using primeRegularCRTExponent_modEq_one hp (e g)
      exact hleft.trans (primeRegularCRTExponent_modEq_one hp g).symm
  have hmod := (Nat.modEq_and_modEq_iff_modEq_mul
    (primaryOrderPart_coprime_regularOrderPart hp g)).mp ⟨hzero, hone⟩
  apply hmod.eq_of_lt_of_lt
  · have h := primeRegularCRTExponent_lt_orderOf hp (e g)
    rw [← primaryOrderPart_mul_regularOrderPart p (e g)] at h
    simpa using h
  · have h := primeRegularCRTExponent_lt_orderOf hp g
    rwa [← primaryOrderPart_mul_regularOrderPart p g] at h

@[simp]
theorem primeRegularPart_map_mulEquiv
    (e : G ≃* H) (hp : p.Prime) (g : G) :
    primeRegularPart hp (e g) = e (primeRegularPart hp g) := by
  simp [primeRegularPart]

@[simp]
theorem primePart_map_mulEquiv
    (e : G ≃* H) (hp : p.Prime) (g : G) :
    primePart hp (e g) = e (primePart hp g) := by
  simp [primePart]

end Naturality

end

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
