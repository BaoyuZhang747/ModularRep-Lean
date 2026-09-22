import ModularRep.PaperProofs.TypeBFLZPolynomialClassification

/-!
# Algebraic duality for the literal FLZ polynomial components

The xi-dual is the normalized reversed polynomial with roots scaled by
the actual unit xi, as in FLZ, J. Algebra 604 (2022), Section 3.2, p. 542.
This supplement proves multiplicativity, involution on monic polynomials
with nonzero constant coefficient, and preservation of monic irreducible
polynomials other than X. All claims follow from the same coefficient
formula and polynomial factorization; there is no external input.

Even degree for the F1 components and the interpretation of polynomial
divisor multiplicities as actual primary centralizer multiplicities are
separate obligations. No finite-field classification is used here.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBFLZPolynomialDuality

open Polynomial TypeBFLZPolynomialComponents TypeBFLZPolynomialClassification

universe u

variable {F : Type u} [Field F]

theorem xiDual_one (xi : Fˣ) : xiDual xi (1 : Polynomial F) = 1 := by
  apply (xiDual_monic xi (1 : Polynomial F) (by simp)).natDegree_eq_zero.mp
  rw [xiDual_natDegree xi (1 : Polynomial F) (by simp), natDegree_one]

/-- Multiplication uses the actual normalized reverse/scaleRoots formula,
including polynomials whose constant coefficient is zero. -/
theorem xiDual_mul (xi : Fˣ) (f g : Polynomial F) :
    xiDual xi (f * g) = xiDual xi f * xiDual xi g := by
  simp only [xiDual, mul_coeff_zero, mul_inv_rev, C_mul,
    reverse_mul_of_domain, mul_scaleRoots_of_noZeroDivisors]
  ring

/-- Double duality requires monicity: the normalization otherwise discards
the original leading coefficient. -/
theorem xiDual_involutive (xi : Fˣ) (f : Polynomial F)
    (hm : f.Monic) (h0 : f.coeff 0 ≠ 0) : xiDual xi (xiDual xi f) = f := by
  have hd0 := xiDual_coeff_zero_ne xi f hm h0
  have hd := xiDual_natDegree xi f h0
  have hdd := (xiDual_natDegree xi (xiDual xi f) hd0).trans hd
  apply Polynomial.ext
  intro i
  by_cases hi : i ≤ f.natDegree
  · rw [xiDual_coeff xi (xiDual xi f) hd0 i (by simpa only [hd] using hi), hd,
      xiDual_coeff xi f h0 (f.natDegree - i) (Nat.sub_le _ _),
      Nat.sub_sub_self hi, xiDual_coeff_zero xi f hm h0]
    have hpow : (xi : F) ^ i * (xi : F) ^ (f.natDegree - i) =
        (xi : F) ^ f.natDegree := by
      rw [← pow_add, Nat.add_sub_of_le hi]
    calc
      _ = ((f.coeff 0)⁻¹ * (xi : F) ^ f.natDegree)⁻¹ *
          ((f.coeff 0)⁻¹ * ((xi : F) ^ i * (xi : F) ^ (f.natDegree - i))) *
          f.coeff i := by ring
      _ = f.coeff i := by
        rw [hpow, inv_mul_cancel₀ (mul_ne_zero (inv_ne_zero h0)
          (pow_ne_zero _ xi.ne_zero)), one_mul]
  · have hlt : f.natDegree < i := Nat.lt_of_not_ge hi
    rw [coeff_eq_zero_of_natDegree_lt (p := xiDual xi (xiDual xi f))
        (by simpa only [hdd] using hlt), coeff_eq_zero_of_natDegree_lt hlt]

theorem xiDual_eq_iff (xi : Fˣ) (f g : Polynomial F)
    (hmf : f.Monic) (hmg : g.Monic) (h0f : f.coeff 0 ≠ 0) (h0g : g.coeff 0 ≠ 0) :
    xiDual xi f = xiDual xi g ↔ f = g := by
  constructor
  · intro h
    have hh := congrArg (xiDual xi) h
    simpa only [xiDual_involutive xi f hmf h0f,
      xiDual_involutive xi g hmg h0g] using hh
  · rintro rfl
    rfl

/-- Monic factorization of the dual is transported back by the same
involution; no trace, character, or classification certificate is used. -/
theorem xiDual_irreducible (xi : Fˣ) (f : Polynomial F)
    (hm : f.Monic) (hi : Irreducible f) (h0 : f.coeff 0 ≠ 0) :
    Irreducible (xiDual xi f) := by
  have hdm := xiDual_monic xi f h0
  have hd0 := xiDual_coeff_zero_ne xi f hm h0
  have hd1 : xiDual xi f ≠ 1 := by
    intro h
    apply hi.ne_one
    have hh := congrArg (xiDual xi) h
    simpa only [xiDual_involutive xi f hm h0, xiDual_one] using hh
  apply (irreducible_of_monic hdm hd1).mpr
  intro g h hgm hhm hgh
  have hgh0 : g.coeff 0 * h.coeff 0 ≠ 0 := by
    simpa only [← mul_coeff_zero, hgh] using hd0
  have hg0 : g.coeff 0 ≠ 0 := (mul_ne_zero_iff.mp hgh0).1
  have hh0 : h.coeff 0 ≠ 0 := (mul_ne_zero_iff.mp hgh0).2
  have hdual : xiDual xi g * xiDual xi h = f := by
    rw [← xiDual_mul, hgh, xiDual_involutive xi f hm h0]
  obtain hg | hh := (irreducible_of_monic hm hi.ne_one).mp hi
    (xiDual xi g) (xiDual xi h) (xiDual_monic xi g hg0) (xiDual_monic xi h hh0) hdual
  · left
    have hgg := congrArg (xiDual xi) hg
    simpa only [xiDual_involutive xi g hgm hg0, xiDual_one] using hgg
  · right
    have hhh := congrArg (xiDual xi) hh
    simpa only [xiDual_involutive xi h hhm hh0, xiDual_one] using hhh

theorem xiDual_ne_X (xi : Fˣ) (f : Polynomial F)
    (hm : f.Monic) (h0 : f.coeff 0 ≠ 0) : xiDual xi f ≠ X := by
  intro h
  apply xiDual_coeff_zero_ne xi f hm h0
  rw [h]
  simp

/-- The literal irreducible carrier used in the FLZ F0/F1/F2 definitions
is preserved by the actual polynomial operation. -/
theorem xiDual_preserves_irreducible_carrier (xi : Fˣ) (f : Polynomial F)
    (hm : f.Monic) (hi : Irreducible f) (hx : f ≠ X) :
    (xiDual xi f).Monic ∧ Irreducible (xiDual xi f) ∧ xiDual xi f ≠ X := by
  have h0 := coeff_zero_ne_of_monic_irreducible hm hi hx
  exact ⟨xiDual_monic xi f h0, xiDual_irreducible xi f hm hi h0,
    xiDual_ne_X xi f hm h0⟩

end ModularRep.PaperProofs.TypeBFLZPolynomialDuality


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
