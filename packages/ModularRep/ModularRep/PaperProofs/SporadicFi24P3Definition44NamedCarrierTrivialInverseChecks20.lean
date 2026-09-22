import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
open scoped BigOperators
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialInverseChecks20

theorem inverse_row_20 : ∀ b : Fin 41, ∀ d : Fin 7,
    checkEq (inverseGroup 20 b d)
      (add (mul (modulus d) (inverseQuotient 20 b d)) [inverseConstant 20 b d]) = true := by decide

theorem constant_row_20 : ∀ b : Fin 41,
    (∑ d : Fin 7, inverseConstant 20 b d) =
      if (20 : Fin 41) = b then inverseDenominator else 0 := by decide

theorem inverse_row_21 : ∀ b : Fin 41, ∀ d : Fin 7,
    checkEq (inverseGroup 21 b d)
      (add (mul (modulus d) (inverseQuotient 21 b d)) [inverseConstant 21 b d]) = true := by decide

theorem constant_row_21 : ∀ b : Fin 41,
    (∑ d : Fin 7, inverseConstant 21 b d) =
      if (21 : Fin 41) = b then inverseDenominator else 0 := by decide

theorem inverse_row_22 : ∀ b : Fin 41, ∀ d : Fin 7,
    checkEq (inverseGroup 22 b d)
      (add (mul (modulus d) (inverseQuotient 22 b d)) [inverseConstant 22 b d]) = true := by decide

theorem constant_row_22 : ∀ b : Fin 41,
    (∑ d : Fin 7, inverseConstant 22 b d) =
      if (22 : Fin 41) = b then inverseDenominator else 0 := by decide

theorem inverse_row_23 : ∀ b : Fin 41, ∀ d : Fin 7,
    checkEq (inverseGroup 23 b d)
      (add (mul (modulus d) (inverseQuotient 23 b d)) [inverseConstant 23 b d]) = true := by decide

theorem constant_row_23 : ∀ b : Fin 41,
    (∑ d : Fin 7, inverseConstant 23 b d) =
      if (23 : Fin 41) = b then inverseDenominator else 0 := by decide

theorem inverse_row_24 : ∀ b : Fin 41, ∀ d : Fin 7,
    checkEq (inverseGroup 24 b d)
      (add (mul (modulus d) (inverseQuotient 24 b d)) [inverseConstant 24 b d]) = true := by decide

theorem constant_row_24 : ∀ b : Fin 41,
    (∑ d : Fin 7, inverseConstant 24 b d) =
      if (24 : Fin 41) = b then inverseDenominator else 0 := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialInverseChecks20


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
