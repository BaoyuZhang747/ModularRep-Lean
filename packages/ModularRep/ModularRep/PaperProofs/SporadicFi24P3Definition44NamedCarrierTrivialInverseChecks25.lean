import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
open scoped BigOperators
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialInverseChecks25

theorem inverse_row_25 : ∀ b : Fin 41, ∀ d : Fin 7,
    checkEq (inverseGroup 25 b d)
      (add (mul (modulus d) (inverseQuotient 25 b d)) [inverseConstant 25 b d]) = true := by decide

theorem constant_row_25 : ∀ b : Fin 41,
    (∑ d : Fin 7, inverseConstant 25 b d) =
      if (25 : Fin 41) = b then inverseDenominator else 0 := by decide

theorem inverse_row_26 : ∀ b : Fin 41, ∀ d : Fin 7,
    checkEq (inverseGroup 26 b d)
      (add (mul (modulus d) (inverseQuotient 26 b d)) [inverseConstant 26 b d]) = true := by decide

theorem constant_row_26 : ∀ b : Fin 41,
    (∑ d : Fin 7, inverseConstant 26 b d) =
      if (26 : Fin 41) = b then inverseDenominator else 0 := by decide

theorem inverse_row_27 : ∀ b : Fin 41, ∀ d : Fin 7,
    checkEq (inverseGroup 27 b d)
      (add (mul (modulus d) (inverseQuotient 27 b d)) [inverseConstant 27 b d]) = true := by decide

theorem constant_row_27 : ∀ b : Fin 41,
    (∑ d : Fin 7, inverseConstant 27 b d) =
      if (27 : Fin 41) = b then inverseDenominator else 0 := by decide

theorem inverse_row_28 : ∀ b : Fin 41, ∀ d : Fin 7,
    checkEq (inverseGroup 28 b d)
      (add (mul (modulus d) (inverseQuotient 28 b d)) [inverseConstant 28 b d]) = true := by decide

theorem constant_row_28 : ∀ b : Fin 41,
    (∑ d : Fin 7, inverseConstant 28 b d) =
      if (28 : Fin 41) = b then inverseDenominator else 0 := by decide

theorem inverse_row_29 : ∀ b : Fin 41, ∀ d : Fin 7,
    checkEq (inverseGroup 29 b d)
      (add (mul (modulus d) (inverseQuotient 29 b d)) [inverseConstant 29 b d]) = true := by decide

theorem constant_row_29 : ∀ b : Fin 41,
    (∑ d : Fin 7, inverseConstant 29 b d) =
      if (29 : Fin 41) = b then inverseDenominator else 0 := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialInverseChecks25


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
