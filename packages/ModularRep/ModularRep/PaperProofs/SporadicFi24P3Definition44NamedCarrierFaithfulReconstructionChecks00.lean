import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerWitnesses
open scoped BigOperators
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerWitnesses
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulReconstructionChecks00

theorem reconstruction_row_0 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 0 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 0 j)) = true := by decide

theorem reconstruction_row_1 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 1 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 1 j)) = true := by decide

theorem reconstruction_row_2 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 2 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 2 j)) = true := by decide

theorem reconstruction_row_3 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 3 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 3 j)) = true := by decide

theorem reconstruction_row_4 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 4 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 4 j)) = true := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulReconstructionChecks00


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
