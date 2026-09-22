import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerWitnesses
open scoped BigOperators
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerWitnesses
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulInverseChecks00

theorem inverse_row_0 : ∀ b : Fin 25, ∀ d : Fin 6,
    checkEq (inverseGroup 0 b d)
      (add (mul (modulus d) (inverseQuotient 0 b d)) [inverseConstant 0 b d]) = true := by decide

theorem constant_row_0 : ∀ b : Fin 25,
    (∑ d : Fin 6, inverseConstant 0 b d) =
      if (0 : Fin 25) = b then inverseDenominator else 0 := by decide

theorem inverse_row_1 : ∀ b : Fin 25, ∀ d : Fin 6,
    checkEq (inverseGroup 1 b d)
      (add (mul (modulus d) (inverseQuotient 1 b d)) [inverseConstant 1 b d]) = true := by decide

theorem constant_row_1 : ∀ b : Fin 25,
    (∑ d : Fin 6, inverseConstant 1 b d) =
      if (1 : Fin 25) = b then inverseDenominator else 0 := by decide

theorem inverse_row_2 : ∀ b : Fin 25, ∀ d : Fin 6,
    checkEq (inverseGroup 2 b d)
      (add (mul (modulus d) (inverseQuotient 2 b d)) [inverseConstant 2 b d]) = true := by decide

theorem constant_row_2 : ∀ b : Fin 25,
    (∑ d : Fin 6, inverseConstant 2 b d) =
      if (2 : Fin 25) = b then inverseDenominator else 0 := by decide

theorem inverse_row_3 : ∀ b : Fin 25, ∀ d : Fin 6,
    checkEq (inverseGroup 3 b d)
      (add (mul (modulus d) (inverseQuotient 3 b d)) [inverseConstant 3 b d]) = true := by decide

theorem constant_row_3 : ∀ b : Fin 25,
    (∑ d : Fin 6, inverseConstant 3 b d) =
      if (3 : Fin 25) = b then inverseDenominator else 0 := by decide

theorem inverse_row_4 : ∀ b : Fin 25, ∀ d : Fin 6,
    checkEq (inverseGroup 4 b d)
      (add (mul (modulus d) (inverseQuotient 4 b d)) [inverseConstant 4 b d]) = true := by decide

theorem constant_row_4 : ∀ b : Fin 25,
    (∑ d : Fin 6, inverseConstant 4 b d) =
      if (4 : Fin 25) = b then inverseDenominator else 0 := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulInverseChecks00


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
