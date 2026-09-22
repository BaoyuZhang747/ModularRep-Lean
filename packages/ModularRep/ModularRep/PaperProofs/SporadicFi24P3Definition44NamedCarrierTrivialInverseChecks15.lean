import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
open scoped BigOperators
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialInverseChecks15

theorem inverse_row_15 : ∀ b : Fin 41, ∀ d : Fin 7,
    checkEq (inverseGroup 15 b d)
      (add (mul (modulus d) (inverseQuotient 15 b d)) [inverseConstant 15 b d]) = true := by decide

theorem constant_row_15 : ∀ b : Fin 41,
    (∑ d : Fin 7, inverseConstant 15 b d) =
      if (15 : Fin 41) = b then inverseDenominator else 0 := by decide

theorem inverse_row_16 : ∀ b : Fin 41, ∀ d : Fin 7,
    checkEq (inverseGroup 16 b d)
      (add (mul (modulus d) (inverseQuotient 16 b d)) [inverseConstant 16 b d]) = true := by decide

theorem constant_row_16 : ∀ b : Fin 41,
    (∑ d : Fin 7, inverseConstant 16 b d) =
      if (16 : Fin 41) = b then inverseDenominator else 0 := by decide

theorem inverse_row_17 : ∀ b : Fin 41, ∀ d : Fin 7,
    checkEq (inverseGroup 17 b d)
      (add (mul (modulus d) (inverseQuotient 17 b d)) [inverseConstant 17 b d]) = true := by decide

theorem constant_row_17 : ∀ b : Fin 41,
    (∑ d : Fin 7, inverseConstant 17 b d) =
      if (17 : Fin 41) = b then inverseDenominator else 0 := by decide

theorem inverse_row_18 : ∀ b : Fin 41, ∀ d : Fin 7,
    checkEq (inverseGroup 18 b d)
      (add (mul (modulus d) (inverseQuotient 18 b d)) [inverseConstant 18 b d]) = true := by decide

theorem constant_row_18 : ∀ b : Fin 41,
    (∑ d : Fin 7, inverseConstant 18 b d) =
      if (18 : Fin 41) = b then inverseDenominator else 0 := by decide

theorem inverse_row_19 : ∀ b : Fin 41, ∀ d : Fin 7,
    checkEq (inverseGroup 19 b d)
      (add (mul (modulus d) (inverseQuotient 19 b d)) [inverseConstant 19 b d]) = true := by decide

theorem constant_row_19 : ∀ b : Fin 41,
    (∑ d : Fin 7, inverseConstant 19 b d) =
      if (19 : Fin 41) = b then inverseDenominator else 0 := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialInverseChecks15


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
