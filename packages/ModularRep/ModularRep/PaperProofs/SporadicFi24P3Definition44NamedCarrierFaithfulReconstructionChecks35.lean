import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerWitnesses
open scoped BigOperators
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerWitnesses
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulReconstructionChecks35

theorem reconstruction_row_35 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 35 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 35 j)) = true := by decide

theorem reconstruction_row_36 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 36 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 36 j)) = true := by decide

theorem reconstruction_row_37 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 37 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 37 j)) = true := by decide

theorem reconstruction_row_38 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 38 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 38 j)) = true := by decide

theorem reconstruction_row_39 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 39 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 39 j)) = true := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulReconstructionChecks35


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
