import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerWitnesses
open scoped BigOperators
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerWitnesses
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulReconstructionChecks55

theorem reconstruction_row_55 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 55 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 55 j)) = true := by decide

theorem reconstruction_row_56 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 56 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 56 j)) = true := by decide

theorem reconstruction_row_57 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 57 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 57 j)) = true := by decide

theorem reconstruction_row_58 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 58 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 58 j)) = true := by decide

theorem reconstruction_row_59 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 59 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 59 j)) = true := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulReconstructionChecks55


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
