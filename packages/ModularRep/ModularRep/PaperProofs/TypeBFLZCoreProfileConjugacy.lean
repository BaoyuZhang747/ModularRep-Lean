import ModularRep.PaperProofs.TypeBFLZCentralizerConjugacy
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Actual multiplier and characteristic-polynomial profiles for FLZ parameters

The polynomial here is the characteristic polynomial of the actual linear
part on `(Fin n → F) × (Fin n → F)`. Its finite-dimensionality is derived
from this fixed carrier. Conjugacy invariance is a checked consequence of
linear conjugation, independent of any character, block or core source.

FLZ, J. Algebra 604 (2022), Sections 3.2--3.3, pp. 542--543, describe the
semisimple primary components by multiplier, polynomial and multiplicity.
The identification of the published combinatorial core family with a family
depending on this profile remains a separate model obligation. No converse
conjugacy classification, core-family definition or source covariance is
assumed or proved here. The construction works over any field, and hence
over the actual finite field used by the Type B source.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBFLZCoreProfileConjugacy

open TypeBConformalDualCarriers TypeBFLZLabelSource
open TypeBFLZCentralizerConjugacy

universe u

variable {F : Type u} [Field F] {p ell n : ℕ}

/-- Both components are literal invariants of the actual conformal map. -/
abbrev Profile (F : Type u) [Field F] := Fˣ × Polynomial F

/-- The polynomial of the actual endomorphism on the fixed symplectic space. -/
def characteristicPolynomial (s : CSp F n) : Polynomial F :=
  (linearPart F n s).toLinearMap.charpoly

/-- Group conjugation is exactly linear conjugation on the underlying map. -/
theorem linearPart_conj (g s : CSp F n) :
    (linearPart F n (g * s * g⁻¹)).toLinearMap =
      (linearPart F n g).conj (linearPart F n s).toLinearMap := by
  apply LinearMap.ext
  intro v
  rfl

/-- Characteristic-polynomial invariance needs no external source equation. -/
@[simp]
theorem characteristicPolynomial_conj (g s : CSp F n) :
    characteristicPolynomial (g * s * g⁻¹) = characteristicPolynomial s := by
  unfold characteristicPolynomial
  rw [linearPart_conj]
  exact (linearPart F n g).charpoly_conj (linearPart F n s).toLinearMap

theorem characteristicPolynomial_eq_of_isConj {s t : CSp F n}
    (h : IsConj s t) : characteristicPolynomial s = characteristicPolynomial t := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  exact (characteristicPolynomial_conj g s).symm

/-- The actual multiplier and full characteristic polynomial, including multiplicities. -/
def profile (s : CSp F n) : Profile F :=
  (multiplier F n s, characteristicPolynomial s)

@[simp]
theorem profile_multiplier (s : CSp F n) : (profile s).1 = multiplier F n s := rfl

@[simp]
theorem profile_characteristicPolynomial (s : CSp F n) :
    (profile s).2 = (linearPart F n s).toLinearMap.charpoly := rfl

/-- The direction is the actual conjugated parameter back to its original profile. -/
@[simp]
theorem profile_conj (g s : CSp F n) : profile (g * s * g⁻¹) = profile s := by
  apply Prod.ext
  · exact (multiplier_eq_of_isConj F n (isConj_iff.mpr ⟨g, rfl⟩)).symm
  · exact characteristicPolynomial_conj g s

theorem profile_eq_of_isConj {s t : CSp F n} (h : IsConj s t) :
    profile s = profile t := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  exact (profile_conj g s).symm

/-- Restriction to the existing defining-prime order guard. -/
def semisimpleProfile (s : SemisimpleParameter F p n) : Profile F := profile s.val

/-- Restriction to both existing defining- and modular-prime order guards. -/
def admissibleProfile (s : AdmissibleParameter F p ell n) : Profile F := profile s.val

@[simp]
theorem semisimpleProfile_conj (g : CSp F n) (s : SemisimpleParameter F p n) :
    semisimpleProfile (semisimpleConj g s) = semisimpleProfile s :=
  profile_conj g s.val

@[simp]
theorem admissibleProfile_conj (g : CSp F n) (s : AdmissibleParameter F p ell n) :
    admissibleProfile (admissibleConj g s) = admissibleProfile s :=
  profile_conj g s.val

theorem semisimpleProfile_eq_of_isConj {s t : SemisimpleParameter F p n}
    (h : IsConj s.val t.val) : semisimpleProfile s = semisimpleProfile t :=
  profile_eq_of_isConj h

theorem admissibleProfile_eq_of_isConj {s t : AdmissibleParameter F p ell n}
    (h : IsConj s.val t.val) : admissibleProfile s = admissibleProfile t :=
  profile_eq_of_isConj h

/-- Forgetting the modular-prime guard changes neither component of the profile. -/
@[simp]
theorem admissibleProfile_toSemisimple (s : AdmissibleParameter F p ell n) :
    semisimpleProfile (admissibleToSemisimple F p ell n s) = admissibleProfile s := rfl

/-- Equal actual rational conjugacy indices have equal actual profiles. -/
theorem admissibleProfile_eq_of_parameterIndex_eq (s t : AdmissibleParameter F p ell n)
    (h : parameterIndex F p ell n s = parameterIndex F p ell n t) :
    admissibleProfile s = admissibleProfile t :=
  admissibleProfile_eq_of_isConj ((parameterIndex_eq_iff F p ell n s t).mp h)

/-- Actual conjugacy class descent, justified only by the proved invariant. -/
def conjugacyClassProfile : ConjClasses (CSp F n) → Profile F :=
  Quotient.lift profile (fun _ _ h => profile_eq_of_isConj h)

@[simp]
theorem conjugacyClassProfile_mk (s : CSp F n) :
    conjugacyClassProfile (ConjClasses.mk s) = profile s := rfl

/-- The profile of the actual rational index, with its two existing order guards. -/
def classProfile (i : SourceIndex F p ell n) : Profile F :=
  conjugacyClassProfile i.val

/-- The quotient index has exactly the profile of its literal representative. -/
@[simp]
theorem classProfile_parameterIndex (s : AdmissibleParameter F p ell n) :
    classProfile (parameterIndex F p ell n s) = admissibleProfile s := rfl

end ModularRep.PaperProofs.TypeBFLZCoreProfileConjugacy


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
