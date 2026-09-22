import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
open scoped BigOperators
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialInverseChecks35

theorem inverse_row_35 : ∀ b : Fin 41, ∀ d : Fin 7,
    checkEq (inverseGroup 35 b d)
      (add (mul (modulus d) (inverseQuotient 35 b d)) [inverseConstant 35 b d]) = true := by decide

theorem constant_row_35 : ∀ b : Fin 41,
    (∑ d : Fin 7, inverseConstant 35 b d) =
      if (35 : Fin 41) = b then inverseDenominator else 0 := by decide

theorem inverse_row_36 : ∀ b : Fin 41, ∀ d : Fin 7,
    checkEq (inverseGroup 36 b d)
      (add (mul (modulus d) (inverseQuotient 36 b d)) [inverseConstant 36 b d]) = true := by decide

theorem constant_row_36 : ∀ b : Fin 41,
    (∑ d : Fin 7, inverseConstant 36 b d) =
      if (36 : Fin 41) = b then inverseDenominator else 0 := by decide

theorem inverse_row_37 : ∀ b : Fin 41, ∀ d : Fin 7,
    checkEq (inverseGroup 37 b d)
      (add (mul (modulus d) (inverseQuotient 37 b d)) [inverseConstant 37 b d]) = true := by decide

theorem constant_row_37 : ∀ b : Fin 41,
    (∑ d : Fin 7, inverseConstant 37 b d) =
      if (37 : Fin 41) = b then inverseDenominator else 0 := by decide

theorem inverse_row_38 : ∀ b : Fin 41, ∀ d : Fin 7,
    checkEq (inverseGroup 38 b d)
      (add (mul (modulus d) (inverseQuotient 38 b d)) [inverseConstant 38 b d]) = true := by decide

theorem constant_row_38 : ∀ b : Fin 41,
    (∑ d : Fin 7, inverseConstant 38 b d) =
      if (38 : Fin 41) = b then inverseDenominator else 0 := by decide

theorem inverse_row_39 : ∀ b : Fin 41, ∀ d : Fin 7,
    checkEq (inverseGroup 39 b d)
      (add (mul (modulus d) (inverseQuotient 39 b d)) [inverseConstant 39 b d]) = true := by decide

theorem constant_row_39 : ∀ b : Fin 41,
    (∑ d : Fin 7, inverseConstant 39 b d) =
      if (39 : Fin 41) = b then inverseDenominator else 0 := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialInverseChecks35


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
