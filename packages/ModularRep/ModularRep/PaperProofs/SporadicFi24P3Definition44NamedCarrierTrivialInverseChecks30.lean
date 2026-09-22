import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
open scoped BigOperators
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialInverseChecks30

theorem inverse_row_30 : ∀ b : Fin 41, ∀ d : Fin 7,
    checkEq (inverseGroup 30 b d)
      (add (mul (modulus d) (inverseQuotient 30 b d)) [inverseConstant 30 b d]) = true := by decide

theorem constant_row_30 : ∀ b : Fin 41,
    (∑ d : Fin 7, inverseConstant 30 b d) =
      if (30 : Fin 41) = b then inverseDenominator else 0 := by decide

theorem inverse_row_31 : ∀ b : Fin 41, ∀ d : Fin 7,
    checkEq (inverseGroup 31 b d)
      (add (mul (modulus d) (inverseQuotient 31 b d)) [inverseConstant 31 b d]) = true := by decide

theorem constant_row_31 : ∀ b : Fin 41,
    (∑ d : Fin 7, inverseConstant 31 b d) =
      if (31 : Fin 41) = b then inverseDenominator else 0 := by decide

theorem inverse_row_32 : ∀ b : Fin 41, ∀ d : Fin 7,
    checkEq (inverseGroup 32 b d)
      (add (mul (modulus d) (inverseQuotient 32 b d)) [inverseConstant 32 b d]) = true := by decide

theorem constant_row_32 : ∀ b : Fin 41,
    (∑ d : Fin 7, inverseConstant 32 b d) =
      if (32 : Fin 41) = b then inverseDenominator else 0 := by decide

theorem inverse_row_33 : ∀ b : Fin 41, ∀ d : Fin 7,
    checkEq (inverseGroup 33 b d)
      (add (mul (modulus d) (inverseQuotient 33 b d)) [inverseConstant 33 b d]) = true := by decide

theorem constant_row_33 : ∀ b : Fin 41,
    (∑ d : Fin 7, inverseConstant 33 b d) =
      if (33 : Fin 41) = b then inverseDenominator else 0 := by decide

theorem inverse_row_34 : ∀ b : Fin 41, ∀ d : Fin 7,
    checkEq (inverseGroup 34 b d)
      (add (mul (modulus d) (inverseQuotient 34 b d)) [inverseConstant 34 b d]) = true := by decide

theorem constant_row_34 : ∀ b : Fin 41,
    (∑ d : Fin 7, inverseConstant 34 b d) =
      if (34 : Fin 41) = b then inverseDenominator else 0 := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialInverseChecks30


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
