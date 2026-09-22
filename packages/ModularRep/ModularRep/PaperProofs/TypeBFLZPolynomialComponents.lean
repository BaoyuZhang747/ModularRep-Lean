import ModularRep.PaperProofs.TypeBFLZCoreProfileConjugacy
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Monic

/-!
# Literal polynomial components of an FLZ multiplier profile

FLZ, J. Algebra 604 (2022), Section 3.2, p. 542, defines the xi-dual by
the roots `xi / alpha`. Here it is the actual normalized, reversed and
root-scaled polynomial. The three component predicates use this formula;
in particular an F2 component is the polynomial product, not a choice of
one of its irreducible factors.

The F0 predicate uses monic irreducible divisors of `X^2 - C xi`. Its
identification with the printed square/nonsquare cases, the even-degree
claims, primary-decomposition multiplicity interpretation and all
partition/symbol/core model identifications are separate obligations.
The multiplicity below is polynomial-divisor multiplicity in the same
profile characteristic polynomial. Finiteness is proved before the
guarded natural-number version is exposed. No external input is added.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBFLZPolynomialComponents

open Polynomial TypeBConformalDualCarriers TypeBFLZLabelSource
open TypeBFLZCoreProfileConjugacy TypeBFLZCentralizerConjugacy

universe u v

variable {F : Type u} [Field F] {p ell n : ℕ}

/-- The constant-coefficient normalization of the actual reversed polynomial,
followed by scaling its roots by the actual multiplier. -/
def xiDual (xi : Fˣ) (f : Polynomial F) : Polynomial F :=
  C (f.coeff 0)⁻¹ * f.reverse.scaleRoots (xi : F)

theorem reverse_natDegree_of_coeff_zero_ne {f : Polynomial F} (h : f.coeff 0 ≠ 0) :
    f.reverse.natDegree = f.natDegree := by
  rw [reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr h), Nat.sub_zero]

/-- For `i <= deg f`, the literal coefficient is
`a_0^-1 * a_(d-i) * xi^(d-i)`. -/
theorem xiDual_coeff (xi : Fˣ) (f : Polynomial F) (h : f.coeff 0 ≠ 0)
    (i : ℕ) (hi : i ≤ f.natDegree) :
    (xiDual xi f).coeff i =
      (f.coeff 0)⁻¹ * (f.coeff (f.natDegree - i) * (xi : F) ^ (f.natDegree - i)) := by
  rw [xiDual, coeff_C_mul, coeff_scaleRoots, coeff_reverse,
    reverse_natDegree_of_coeff_zero_ne h, revAt_le hi]

theorem xiDual_monic (xi : Fˣ) (f : Polynomial F) (h : f.coeff 0 ≠ 0) :
    (xiDual xi f).Monic := by
  change (xiDual xi f).leadingCoeff = 1
  rw [xiDual, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_scaleRoots,
    reverse_leadingCoeff, trailingCoeff_eq_coeff_zero h, inv_mul_cancel₀ h]

theorem xiDual_natDegree (xi : Fˣ) (f : Polynomial F) (h : f.coeff 0 ≠ 0) :
    (xiDual xi f).natDegree = f.natDegree := by
  rw [xiDual, natDegree_C_mul (inv_ne_zero h), natDegree_scaleRoots,
    reverse_natDegree_of_coeff_zero_ne h]

/-- The actual root transformation in any field receiving the coefficients.
No algebraic closure or unspecified dual operation is used. -/
theorem xiDual_eval₂_root {E : Type v} [Field E] (iota : F →+* E)
    (xi : Fˣ) (f : Polynomial F) (alpha : E) (ha : alpha ≠ 0)
    (hroot : f.eval₂ iota alpha = 0) :
    (xiDual xi f).eval₂ iota (iota (xi : F) * alpha⁻¹) = 0 := by
  letI : Invertible alpha := invertibleOfNonzero ha
  have hr : f.reverse.eval₂ iota alpha⁻¹ = 0 := by
    simpa only [invOf_eq_inv] using (eval₂_reverse_eq_zero_iff iota alpha f).mpr hroot
  simp only [xiDual, eval₂_mul, eval₂_C, scaleRoots_eval₂_mul, hr, mul_zero]

/-- A monic irreducible polynomial other than X has nonzero constant term. -/
theorem coeff_zero_ne_of_monic_irreducible {f : Polynomial F}
    (hm : f.Monic) (hi : Irreducible f) (hx : f ≠ X) : f.coeff 0 ≠ 0 := by
  intro h
  apply hx
  exact eq_of_monic_of_associated hm monic_X
    ((irreducible_X.associated_of_dvd hi (X_dvd_iff.mpr h)).symm)

/-- A uniform polynomial predicate; comparison with the printed two cases
requires the finite odd-field quadratic factorization argument. -/
def IsF0 (xi : Fˣ) (f : Polynomial F) : Prop :=
  f.Monic ∧ Irreducible f ∧ f ∣ X ^ 2 - C (xi : F)

def IsF1 (xi : Fˣ) (f : Polynomial F) : Prop :=
  f.Monic ∧ Irreducible f ∧ f ≠ X ∧ f = xiDual xi f ∧
    ¬f ∣ X ^ 2 - C (xi : F)

/-- The witness is an irreducible factor, but the component is its product
with the actual xi-dual. Equal products give the same component. -/
def IsF2 (xi : Fˣ) (f : Polynomial F) : Prop :=
  ∃ delta : Polynomial F, delta.Monic ∧ Irreducible delta ∧ delta ≠ X ∧
    delta ≠ xiDual xi delta ∧ ¬delta ∣ X ^ 2 - C (xi : F) ∧
    f = delta * xiDual xi delta

def IsComponent (xi : Fˣ) (f : Polynomial F) : Prop :=
  IsF0 xi f ∨ IsF1 xi f ∨ IsF2 xi f

/-- The literal polynomial union, without redundant factor-choice data. -/
def Component (xi : Fˣ) := {f : Polynomial F // IsComponent xi f}

theorem component_monic {xi : Fˣ} (Gamma : Component xi) : Gamma.val.Monic := by
  rcases Gamma.property with h | h | h
  · exact h.1
  · exact h.1
  · obtain ⟨delta, hm, hi, hx, _, _, heq⟩ := h
    rw [heq]
    exact hm.mul (xiDual_monic xi delta (coeff_zero_ne_of_monic_irreducible hm hi hx))

theorem component_degree_pos {xi : Fˣ} (Gamma : Component xi) :
    0 < Gamma.val.degree := by
  rcases Gamma.property with h | h | h
  · exact degree_pos_of_irreducible h.2.1
  · exact degree_pos_of_irreducible h.2.1
  · obtain ⟨delta, hm, hi, hx, _, _, heq⟩ := h
    have hd := xiDual_monic xi delta (coeff_zero_ne_of_monic_irreducible hm hi hx)
    apply natDegree_pos_iff_degree_pos.mp
    rw [heq, natDegree_mul hm.ne_zero hd.ne_zero]
    exact Nat.add_pos_left (natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hi)) _

theorem component_ne_zero {xi : Fˣ} (Gamma : Component xi) : Gamma.val ≠ 0 :=
  (component_monic Gamma).ne_zero

theorem component_finiteMultiplicity {xi : Fˣ} (Gamma : Component xi)
    (f : Polynomial F) (hf : f ≠ 0) : FiniteMultiplicity Gamma.val f :=
  finiteMultiplicity_of_degree_pos_of_monic (component_degree_pos Gamma)
    (component_monic Gamma) hf

/-- The component carrier depends on the actual multiplier in the profile. -/
abbrev ProfileComponent (P : Profile F) := Component P.1

/-- The exponent of this polynomial divisor in the full profile polynomial.
Infinity remains visible on arbitrary profiles. -/
def componentMultiplicity (P : Profile F) (Gamma : ProfileComponent P) : ℕ∞ :=
  emultiplicity Gamma.val P.2

theorem componentMultiplicity_ne_top (P : Profile F) (hP : P.2 ≠ 0)
    (Gamma : ProfileComponent P) : componentMultiplicity P Gamma ≠ ⊤ :=
  finiteMultiplicity_iff_emultiplicity_ne_top.mp (component_finiteMultiplicity Gamma P.2 hP)

/-- The proof guard prevents use of the library's default for infinite multiplicity. -/
def natComponentMultiplicity (P : Profile F) (_hP : P.2 ≠ 0)
    (Gamma : ProfileComponent P) : ℕ := multiplicity Gamma.val P.2

theorem componentMultiplicity_eq_nat (P : Profile F) (hP : P.2 ≠ 0)
    (Gamma : ProfileComponent P) :
    componentMultiplicity P Gamma = (natComponentMultiplicity P hP Gamma : ℕ∞) :=
  (component_finiteMultiplicity Gamma P.2 hP).emultiplicity_eq_multiplicity

theorem componentMultiplicity_pos_iff (P : Profile F) (Gamma : ProfileComponent P) :
    0 < componentMultiplicity P Gamma ↔ Gamma.val ∣ P.2 :=
  dvd_iff_emultiplicity_pos

/-- A component that actually occurs in the profile polynomial. -/
def OccurringComponent (P : Profile F) :=
  {Gamma : ProfileComponent P // 0 < componentMultiplicity P Gamma}

/-- Equality transports only membership proofs and leaves the polynomial fixed. -/
def transportComponent {P Q : Profile F} (h : P = Q) :
    ProfileComponent P ≃ ProfileComponent Q := by
  subst Q
  exact Equiv.refl _

@[simp]
theorem transportComponent_val {P Q : Profile F} (h : P = Q) (Gamma : ProfileComponent P) :
    (transportComponent h Gamma).val = Gamma.val := by
  subst Q
  rfl

@[simp]
theorem componentMultiplicity_transport {P Q : Profile F} (h : P = Q)
    (Gamma : ProfileComponent P) :
    componentMultiplicity Q (transportComponent h Gamma) = componentMultiplicity P Gamma := by
  subst Q
  rfl

theorem characteristicPolynomial_ne_zero (s : CSp F n) :
    characteristicPolynomial s ≠ 0 :=
  (LinearMap.charpoly_monic (linearPart F n s).toLinearMap).ne_zero

theorem semisimpleProfile_polynomial_ne_zero (s : SemisimpleParameter F p n) :
    (semisimpleProfile s).2 ≠ 0 := characteristicPolynomial_ne_zero s.val

theorem admissibleProfile_polynomial_ne_zero (s : AdmissibleParameter F p ell n) :
    (admissibleProfile s).2 ≠ 0 := characteristicPolynomial_ne_zero s.val

def semisimpleConjComponent (g : CSp F n) (s : SemisimpleParameter F p n) :
    ProfileComponent (semisimpleProfile s) ≃
      ProfileComponent (semisimpleProfile (semisimpleConj g s)) :=
  transportComponent (semisimpleProfile_conj g s).symm

@[simp]
theorem semisimpleConjComponent_val (g : CSp F n) (s : SemisimpleParameter F p n)
    (Gamma : ProfileComponent (semisimpleProfile s)) :
    (semisimpleConjComponent g s Gamma).val = Gamma.val :=
  transportComponent_val _ _

theorem semisimpleConjComponent_multiplicity (g : CSp F n) (s : SemisimpleParameter F p n)
    (Gamma : ProfileComponent (semisimpleProfile s)) :
    componentMultiplicity (semisimpleProfile (semisimpleConj g s))
      (semisimpleConjComponent g s Gamma) = componentMultiplicity (semisimpleProfile s) Gamma :=
  componentMultiplicity_transport _ _

def admissibleConjComponent (g : CSp F n) (s : AdmissibleParameter F p ell n) :
    ProfileComponent (admissibleProfile s) ≃
      ProfileComponent (admissibleProfile (admissibleConj g s)) :=
  transportComponent (admissibleProfile_conj g s).symm

@[simp]
theorem admissibleConjComponent_val (g : CSp F n) (s : AdmissibleParameter F p ell n)
    (Gamma : ProfileComponent (admissibleProfile s)) :
    (admissibleConjComponent g s Gamma).val = Gamma.val :=
  transportComponent_val _ _

theorem admissibleConjComponent_multiplicity (g : CSp F n) (s : AdmissibleParameter F p ell n)
    (Gamma : ProfileComponent (admissibleProfile s)) :
    componentMultiplicity (admissibleProfile (admissibleConj g s))
      (admissibleConjComponent g s Gamma) = componentMultiplicity (admissibleProfile s) Gamma :=
  componentMultiplicity_transport _ _

end ModularRep.PaperProofs.TypeBFLZPolynomialComponents


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
