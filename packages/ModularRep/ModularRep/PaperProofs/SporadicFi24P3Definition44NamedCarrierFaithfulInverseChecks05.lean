import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerWitnesses
open scoped BigOperators
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerWitnesses
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulInverseChecks05

theorem inverse_row_5 : ∀ b : Fin 25, ∀ d : Fin 6,
    checkEq (inverseGroup 5 b d)
      (add (mul (modulus d) (inverseQuotient 5 b d)) [inverseConstant 5 b d]) = true := by decide

theorem constant_row_5 : ∀ b : Fin 25,
    (∑ d : Fin 6, inverseConstant 5 b d) =
      if (5 : Fin 25) = b then inverseDenominator else 0 := by decide

theorem inverse_row_6 : ∀ b : Fin 25, ∀ d : Fin 6,
    checkEq (inverseGroup 6 b d)
      (add (mul (modulus d) (inverseQuotient 6 b d)) [inverseConstant 6 b d]) = true := by decide

theorem constant_row_6 : ∀ b : Fin 25,
    (∑ d : Fin 6, inverseConstant 6 b d) =
      if (6 : Fin 25) = b then inverseDenominator else 0 := by decide

theorem inverse_row_7 : ∀ b : Fin 25, ∀ d : Fin 6,
    checkEq (inverseGroup 7 b d)
      (add (mul (modulus d) (inverseQuotient 7 b d)) [inverseConstant 7 b d]) = true := by decide

theorem constant_row_7 : ∀ b : Fin 25,
    (∑ d : Fin 6, inverseConstant 7 b d) =
      if (7 : Fin 25) = b then inverseDenominator else 0 := by decide

theorem inverse_row_8 : ∀ b : Fin 25, ∀ d : Fin 6,
    checkEq (inverseGroup 8 b d)
      (add (mul (modulus d) (inverseQuotient 8 b d)) [inverseConstant 8 b d]) = true := by decide

theorem constant_row_8 : ∀ b : Fin 25,
    (∑ d : Fin 6, inverseConstant 8 b d) =
      if (8 : Fin 25) = b then inverseDenominator else 0 := by decide

theorem inverse_row_9 : ∀ b : Fin 25, ∀ d : Fin 6,
    checkEq (inverseGroup 9 b d)
      (add (mul (modulus d) (inverseQuotient 9 b d)) [inverseConstant 9 b d]) = true := by decide

theorem constant_row_9 : ∀ b : Fin 25,
    (∑ d : Fin 6, inverseConstant 9 b d) =
      if (9 : Fin 25) = b then inverseDenominator else 0 := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulInverseChecks05


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
