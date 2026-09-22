import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerWitnesses
open scoped BigOperators
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerWitnesses
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulReconstructionChecks20

theorem reconstruction_row_20 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 20 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 20 j)) = true := by decide

theorem reconstruction_row_21 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 21 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 21 j)) = true := by decide

theorem reconstruction_row_22 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 22 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 22 j)) = true := by decide

theorem reconstruction_row_23 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 23 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 23 j)) = true := by decide

theorem reconstruction_row_24 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 24 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 24 j)) = true := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulReconstructionChecks20


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
