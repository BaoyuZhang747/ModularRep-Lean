import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerWitnesses
open scoped BigOperators
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerWitnesses
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulReconstructionChecks10

theorem reconstruction_row_10 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 10 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 10 j)) = true := by decide

theorem reconstruction_row_11 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 11 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 11 j)) = true := by decide

theorem reconstruction_row_12 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 12 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 12 j)) = true := by decide

theorem reconstruction_row_13 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 13 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 13 j)) = true := by decide

theorem reconstruction_row_14 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 14 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 14 j)) = true := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulReconstructionChecks10


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
