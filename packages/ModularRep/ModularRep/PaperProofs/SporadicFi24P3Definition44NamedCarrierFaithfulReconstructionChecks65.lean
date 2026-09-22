import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerWitnesses
open scoped BigOperators
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerWitnesses
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulReconstructionChecks65

theorem reconstruction_row_65 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 65 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 65 j)) = true := by decide

theorem reconstruction_row_66 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 66 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 66 j)) = true := by decide

theorem reconstruction_row_67 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 67 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 67 j)) = true := by decide

theorem reconstruction_row_68 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 68 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 68 j)) = true := by decide

theorem reconstruction_row_69 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 69 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 69 j)) = true := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulReconstructionChecks65


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
