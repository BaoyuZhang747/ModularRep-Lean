import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerWitnesses
open scoped BigOperators
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerWitnesses
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulReconstructionChecks70

theorem reconstruction_row_70 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 70 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 70 j)) = true := by decide

theorem reconstruction_row_71 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 71 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 71 j)) = true := by decide

theorem reconstruction_row_72 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 72 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 72 j)) = true := by decide

theorem reconstruction_row_73 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 73 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 73 j)) = true := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulReconstructionChecks70


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
