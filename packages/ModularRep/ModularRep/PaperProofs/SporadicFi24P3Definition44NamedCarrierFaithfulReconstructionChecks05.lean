import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerWitnesses
open scoped BigOperators
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerWitnesses
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulReconstructionChecks05

theorem reconstruction_row_5 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 5 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 5 j)) = true := by decide

theorem reconstruction_row_6 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 6 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 6 j)) = true := by decide

theorem reconstruction_row_7 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 7 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 7 j)) = true := by decide

theorem reconstruction_row_8 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 8 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 8 j)) = true := by decide

theorem reconstruction_row_9 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 9 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 9 j)) = true := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulReconstructionChecks05


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
