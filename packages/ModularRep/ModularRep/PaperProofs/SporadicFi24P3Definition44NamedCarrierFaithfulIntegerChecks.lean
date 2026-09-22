import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerWitnesses
open scoped BigOperators
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerChecks
open SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open SporadicFi24P3Definition44NamedCarrierFaithfulIntegerData
open SporadicFi24P3Definition44NamedCarrierFaithfulIntegerWitnesses
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem inverse_check_0_0_0 :
    checkEq (inverseGroup 0 0 0)
      (add (mul (modulus 0) (inverseQuotient 0 0 0)) [inverseConstant 0 0 0]) = true := by decide

theorem inverse_check_0_0_4 :
    checkEq (inverseGroup 0 0 4)
      (add (mul (modulus 4) (inverseQuotient 0 0 4)) [inverseConstant 0 0 4]) = true := by decide

theorem inverse_check_2_2_2 :
    checkEq (inverseGroup 2 2 2)
      (add (mul (modulus 2) (inverseQuotient 2 2 2)) [inverseConstant 2 2 2]) = true := by decide

theorem inverse_check_9_9_5 :
    checkEq (inverseGroup 9 9 5)
      (add (mul (modulus 5) (inverseQuotient 9 9 5)) [inverseConstant 9 9 5]) = true := by decide

theorem inverse_check_23_23_0 :
    checkEq (inverseGroup 23 23 0)
      (add (mul (modulus 0) (inverseQuotient 23 23 0)) [inverseConstant 23 23 0]) = true := by decide

theorem inverse_check_24_24_5 :
    checkEq (inverseGroup 24 24 5)
      (add (mul (modulus 5) (inverseQuotient 24 24 5)) [inverseConstant 24 24 5]) = true := by decide

theorem reconstruction_check_0_0 :
    checkEq (reconstructionResidual 0 0)
      (mul (modulus (columnTag 0)) (reconstructionQuotient 0 0)) = true := by decide

theorem reconstruction_check_3_3 :
    checkEq (reconstructionResidual 3 3)
      (mul (modulus (columnTag 3)) (reconstructionQuotient 3 3)) = true := by decide

theorem reconstruction_check_25_4 :
    checkEq (reconstructionResidual 25 4)
      (mul (modulus (columnTag 4)) (reconstructionQuotient 25 4)) = true := by decide

theorem reconstruction_check_73_24 :
    checkEq (reconstructionResidual 73 24)
      (mul (modulus (columnTag 24)) (reconstructionQuotient 73 24)) = true := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerChecks


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
