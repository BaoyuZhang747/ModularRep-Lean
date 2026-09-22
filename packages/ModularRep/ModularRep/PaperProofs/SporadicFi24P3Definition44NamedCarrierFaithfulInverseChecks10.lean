import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerWitnesses
open scoped BigOperators
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerWitnesses
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulInverseChecks10

theorem inverse_row_10 : ∀ b : Fin 25, ∀ d : Fin 6,
    checkEq (inverseGroup 10 b d)
      (add (mul (modulus d) (inverseQuotient 10 b d)) [inverseConstant 10 b d]) = true := by decide

theorem constant_row_10 : ∀ b : Fin 25,
    (∑ d : Fin 6, inverseConstant 10 b d) =
      if (10 : Fin 25) = b then inverseDenominator else 0 := by decide

theorem inverse_row_11 : ∀ b : Fin 25, ∀ d : Fin 6,
    checkEq (inverseGroup 11 b d)
      (add (mul (modulus d) (inverseQuotient 11 b d)) [inverseConstant 11 b d]) = true := by decide

theorem constant_row_11 : ∀ b : Fin 25,
    (∑ d : Fin 6, inverseConstant 11 b d) =
      if (11 : Fin 25) = b then inverseDenominator else 0 := by decide

theorem inverse_row_12 : ∀ b : Fin 25, ∀ d : Fin 6,
    checkEq (inverseGroup 12 b d)
      (add (mul (modulus d) (inverseQuotient 12 b d)) [inverseConstant 12 b d]) = true := by decide

theorem constant_row_12 : ∀ b : Fin 25,
    (∑ d : Fin 6, inverseConstant 12 b d) =
      if (12 : Fin 25) = b then inverseDenominator else 0 := by decide

theorem inverse_row_13 : ∀ b : Fin 25, ∀ d : Fin 6,
    checkEq (inverseGroup 13 b d)
      (add (mul (modulus d) (inverseQuotient 13 b d)) [inverseConstant 13 b d]) = true := by decide

theorem constant_row_13 : ∀ b : Fin 25,
    (∑ d : Fin 6, inverseConstant 13 b d) =
      if (13 : Fin 25) = b then inverseDenominator else 0 := by decide

theorem inverse_row_14 : ∀ b : Fin 25, ∀ d : Fin 6,
    checkEq (inverseGroup 14 b d)
      (add (mul (modulus d) (inverseQuotient 14 b d)) [inverseConstant 14 b d]) = true := by decide

theorem constant_row_14 : ∀ b : Fin 25,
    (∑ d : Fin 6, inverseConstant 14 b d) =
      if (14 : Fin 25) = b then inverseDenominator else 0 := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulInverseChecks10


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
