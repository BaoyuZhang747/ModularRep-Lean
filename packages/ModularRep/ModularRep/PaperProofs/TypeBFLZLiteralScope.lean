import ModularRep.PaperProofs.TypeBFLZLiteralProfileModel
import ModularRep.PaperProofs.TypeBCliffordCarriers
import Mathlib.Data.Nat.Prime.Basic

/-!
# Literal core extraction under the existing FLZ field hypotheses

The actual field parameters and FLZ applicability already imply that the
modular prime does not divide the cardinality of the field. They also
provide its prime instance. This file derives those guards and closes the
literal core operator over them, so the Conlon consumer need not supply
independent arithmetic assumptions. No representation theoretic source
or new classification field is introduced.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBFLZLiteralScope

open TypeBCliffordCarriers TypeBFLZLabelSource
open TypeBFLZCoreProfileConjugacy TypeBFLZPolynomialComponents

universe u

variable {F : Type u} [Field F] [Finite F]
variable {p ell f n : ℕ} [CharP F p]
variable (parameters : OddFieldParameters F p f) (scope : Applicability p ell n)

include parameters in
theorem field_card_ne_zero : Nat.card F ≠ 0 := by
  rw [parameters.cardinality]
  exact pow_ne_zero _ parameters.prime.ne_zero

include parameters in
theorem field_card_odd : Odd (Nat.card F) := by
  rw [parameters.cardinality]
  exact parameters.odd.pow

include parameters scope in
theorem modular_coprime_card : ell.Coprime (Nat.card F) := by
  rw [parameters.cardinality]
  exact ((Nat.coprime_primes scope.modular_prime parameters.prime).mpr
    scope.nondefining).pow_right f

include parameters scope in
/-- The literal nondefining-cardinality guard is a consequence, not a
separate external input to the component-core construction. -/
theorem nondefining_card : ¬ ell ∣ Nat.card F := by
  intro h
  rw [parameters.cardinality] at h
  exact scope.nondefining (Nat.prime_eq_prime_of_dvd_pow
    scope.modular_prime parameters.prime h)

include scope in
theorem modularPrimeFact : Fact ell.Prime := ⟨scope.modular_prime⟩

include parameters scope in
theorem symbolLength_pos (P : Profile F) (Gamma : ProfileComponent P) :
    0 < TypeBFLZComponentCoreParameters.symbolLength ell P Gamma := by
  letI : Fact ell.Prime := modularPrimeFact scope
  exact TypeBFLZComponentCoreParameters.symbolLength_pos ell
    (nondefining_card parameters scope) P Gamma

include parameters scope in
theorem partitionLength_pos (P : Profile F) (Gamma : ProfileComponent P) :
    0 < TypeBFLZComponentCoreParameters.partitionLength ell P Gamma := by
  letI : Fact ell.Prime := modularPrimeFact scope
  exact TypeBFLZComponentCoreParameters.partitionLength_pos ell
    (nondefining_card parameters scope) P Gamma

/-- The SAME literal component operator, with both arithmetic guards
derived from the SAME source field parameters and applicability. -/
def takeCore (inputs : TypeBFLZLiteralProfileModel.RemovalInputs)
    (P : Profile F) (mu : TypeBFLZLiteralProfileModel.Psi P) :
    TypeBFLZLiteralProfileModel.RawCore P := by
  letI : Fact ell.Prime := modularPrimeFact scope
  exact TypeBFLZLiteralProfileModel.takeCore ell
    (nondefining_card parameters scope) inputs P mu

theorem takeCore_component_spec (inputs : TypeBFLZLiteralProfileModel.RemovalInputs)
    (P : Profile F) (mu : TypeBFLZLiteralProfileModel.Psi P)
    (Gamma : ProfileComponent P) :
    TypeBFLZLiteralProfileModel.ComponentTerminalCore ell P mu.1 Gamma (mu.2 Gamma)
      (takeCore parameters scope inputs P mu Gamma) := by
  letI : Fact ell.Prime := modularPrimeFact scope
  exact TypeBFLZLiteralProfileModel.takeCore_component_spec ell
    (nondefining_card parameters scope) inputs P mu Gamma

end ModularRep.PaperProofs.TypeBFLZLiteralScope


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
