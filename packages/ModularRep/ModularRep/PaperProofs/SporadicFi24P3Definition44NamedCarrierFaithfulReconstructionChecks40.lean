import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerWitnesses
open scoped BigOperators
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerWitnesses
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulReconstructionChecks40

theorem reconstruction_row_40 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 40 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 40 j)) = true := by decide

theorem reconstruction_row_41 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 41 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 41 j)) = true := by decide

theorem reconstruction_row_42 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 42 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 42 j)) = true := by decide

theorem reconstruction_row_43 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 43 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 43 j)) = true := by decide

theorem reconstruction_row_44 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 44 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 44 j)) = true := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulReconstructionChecks40


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
