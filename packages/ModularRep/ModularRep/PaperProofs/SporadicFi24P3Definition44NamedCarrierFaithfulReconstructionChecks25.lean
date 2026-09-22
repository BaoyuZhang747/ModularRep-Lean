import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerWitnesses
open scoped BigOperators
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerWitnesses
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulReconstructionChecks25

theorem reconstruction_row_25 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 25 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 25 j)) = true := by decide

theorem reconstruction_row_26 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 26 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 26 j)) = true := by decide

theorem reconstruction_row_27 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 27 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 27 j)) = true := by decide

theorem reconstruction_row_28 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 28 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 28 j)) = true := by decide

theorem reconstruction_row_29 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 29 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 29 j)) = true := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulReconstructionChecks25


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
