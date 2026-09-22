import ModularRep.PaperProofs.TypeBFLZPolynomialComponents
import Mathlib.FieldTheory.KummerPolynomial

/-!
# Elementary classification of the FLZ polynomial components

This supplement identifies the literal F0 divisor predicate with the two
printed cases in FLZ, J. Algebra 604 (2022), Section 3.2, p. 542. Squares
are squares of actual field units, as in the source. The proof works over
any field; the actual finite odd-field application is a specialization.
It also proves even degree for actual F2 product polynomials, nonunitness
of all components, and the constant coefficient of the normalized dual.

No polynomial classification or duality certificate is assumed. The only
additional library import supplies irreducibility of `X^p - C a` for a
prime p. Dual involution/irreducibility, F1 parity, and identification with
primary centralizer multiplicities are outside this supplement.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBFLZPolynomialClassification

open Polynomial TypeBFLZPolynomialComponents

universe u

variable {F : Type u} [Field F]

/-- Nonzero field squares and unit squares are the same literal condition. -/
theorem unit_square_iff_field_square (xi : Fˣ) :
    (∃ r : Fˣ, r ^ 2 = xi) ↔ ∃ r : F, r ^ 2 = (xi : F) := by
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨(r : F), by simpa only [Units.val_pow_eq_pow_val] using congrArg Units.val hr⟩
  · rintro ⟨r, hr⟩
    have hn : r ≠ 0 := by
      intro h
      apply xi.ne_zero
      simpa only [h, zero_pow (by decide : 2 ≠ 0)] using hr.symm
    refine ⟨Units.mk0 r hn, ?_⟩
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, Units.val_mk0] using hr

/-- The same unit square gives the literal two linear factors. -/
theorem quadratic_factor_of_square (xi r : Fˣ) (hr : r ^ 2 = xi) :
    X ^ 2 - C (xi : F) = (X - C (r : F)) * (X + C (r : F)) := by
  have hv : (r : F) ^ 2 = (xi : F) := by
    simpa only [Units.val_pow_eq_pow_val] using congrArg Units.val hr
  rw [← hv, C_pow]
  ring

/-- The square case of FLZ F0, with the chosen actual square-root unit. -/
theorem isF0_iff_of_square (xi r : Fˣ) (hr : r ^ 2 = xi) (f : Polynomial F) :
    IsF0 xi f ↔ f = X - C (r : F) ∨ f = X + C (r : F) := by
  have hplus : Irreducible (X + C (r : F)) := by
    simpa only [map_neg, sub_neg_eq_add] using irreducible_X_sub_C (-(r : F))
  constructor
  · rintro ⟨hm, hi, hd⟩
    rw [quadratic_factor_of_square xi r hr] at hd
    rcases hi.prime.dvd_or_dvd hd with h | h
    · exact Or.inl (eq_of_monic_of_associated hm (monic_X_sub_C _)
        (hi.associated_of_dvd (irreducible_X_sub_C _) h))
    · exact Or.inr (eq_of_monic_of_associated hm (monic_X_add_C _)
        (hi.associated_of_dvd hplus h))
  · rintro (rfl | rfl)
    · refine ⟨monic_X_sub_C _, irreducible_X_sub_C _, ?_⟩
      rw [quadratic_factor_of_square xi r hr]
      exact dvd_mul_right _ _
    · refine ⟨monic_X_add_C _, hplus, ?_⟩
      rw [quadratic_factor_of_square xi r hr]
      exact dvd_mul_left _ _

/-- A nonsquare unit gives an irreducible quadratic by the existing prime-degree
Kummer-polynomial theorem, with p literally equal to 2. -/
theorem quadratic_irreducible_of_nonsquare (xi : Fˣ)
    (hxi : ¬∃ r : Fˣ, r ^ 2 = xi) : Irreducible (X ^ 2 - C (xi : F)) := by
  apply (X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two).mpr
  intro r hr
  exact hxi ((unit_square_iff_field_square xi).mpr ⟨r, hr⟩)

/-- The nonsquare case of FLZ F0 is the singleton containing the actual quadratic. -/
theorem isF0_iff_of_nonsquare (xi : Fˣ) (hxi : ¬∃ r : Fˣ, r ^ 2 = xi)
    (f : Polynomial F) : IsF0 xi f ↔ f = X ^ 2 - C (xi : F) := by
  have hm : (X ^ 2 - C (xi : F)).Monic := monic_X_pow_sub_C _ (by decide)
  have hi := quadratic_irreducible_of_nonsquare xi hxi
  constructor
  · rintro ⟨hfm, hfi, hd⟩
    exact eq_of_monic_of_associated hfm hm (hfi.associated_of_dvd hi hd)
  · rintro rfl
    exact ⟨hm, hi, dvd_rfl⟩

theorem isF0_natDegree_of_square (xi r : Fˣ) (hr : r ^ 2 = xi)
    (f : Polynomial F) (hf : IsF0 xi f) : f.natDegree = 1 := by
  rcases (isF0_iff_of_square xi r hr f).mp hf with rfl | rfl
  · exact natDegree_X_sub_C _
  · exact natDegree_X_add_C _

theorem isF0_natDegree_of_nonsquare (xi : Fˣ) (hxi : ¬∃ r : Fˣ, r ^ 2 = xi)
    (f : Polynomial F) (hf : IsF0 xi f) : f.natDegree = 2 := by
  rw [(isF0_iff_of_nonsquare xi hxi f).mp hf]
  exact natDegree_X_pow_sub_C

/-- The paired component has twice the degree of either chosen first factor. -/
theorem paired_natDegree (xi : Fˣ) (delta : Polynomial F) (hm : delta.Monic)
    (hi : Irreducible delta) (hx : delta ≠ X) :
    (delta * xiDual xi delta).natDegree = 2 * delta.natDegree := by
  have h0 := coeff_zero_ne_of_monic_irreducible hm hi hx
  rw [natDegree_mul hm.ne_zero (xiDual_monic xi delta h0).ne_zero,
    xiDual_natDegree xi delta h0, two_mul]

/-- This parity statement is about the actual F2 product, not an irreducible factor. -/
theorem isF2_even_natDegree (xi : Fˣ) (f : Polynomial F) (hf : IsF2 xi f) :
    Even f.natDegree := by
  obtain ⟨delta, hm, hi, hx, _, _, heq⟩ := hf
  refine ⟨delta.natDegree, ?_⟩
  rw [heq, paired_natDegree xi delta hm hi hx, two_mul]

theorem component_not_isUnit {xi : Fˣ} (Gamma : Component xi) :
    ¬IsUnit Gamma.val :=
  not_isUnit_of_degree_pos _ (component_degree_pos Gamma)

/-- For a monic f, the dual's constant coefficient is literally a_0^-1 xi^d. -/
theorem xiDual_coeff_zero (xi : Fˣ) (f : Polynomial F) (hm : f.Monic)
    (h0 : f.coeff 0 ≠ 0) :
    (xiDual xi f).coeff 0 = (f.coeff 0)⁻¹ * (xi : F) ^ f.natDegree := by
  simpa only [Nat.sub_zero, hm.coeff_natDegree, one_mul] using
    xiDual_coeff xi f h0 0 (Nat.zero_le _)

theorem xiDual_coeff_zero_ne (xi : Fˣ) (f : Polynomial F) (hm : f.Monic)
    (h0 : f.coeff 0 ≠ 0) : (xiDual xi f).coeff 0 ≠ 0 := by
  rw [xiDual_coeff_zero xi f hm h0]
  exact mul_ne_zero (inv_ne_zero h0) (pow_ne_zero _ xi.ne_zero)

end ModularRep.PaperProofs.TypeBFLZPolynomialClassification


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
