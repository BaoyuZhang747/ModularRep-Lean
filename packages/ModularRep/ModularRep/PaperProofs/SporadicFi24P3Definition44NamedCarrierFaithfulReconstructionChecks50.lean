import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerWitnesses
open scoped BigOperators
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerWitnesses
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulReconstructionChecks50

theorem reconstruction_row_50 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 50 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 50 j)) = true := by decide

theorem reconstruction_row_51 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 51 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 51 j)) = true := by decide

theorem reconstruction_row_52 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 52 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 52 j)) = true := by decide

theorem reconstruction_row_53 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 53 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 53 j)) = true := by decide

theorem reconstruction_row_54 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 54 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 54 j)) = true := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulReconstructionChecks50


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
