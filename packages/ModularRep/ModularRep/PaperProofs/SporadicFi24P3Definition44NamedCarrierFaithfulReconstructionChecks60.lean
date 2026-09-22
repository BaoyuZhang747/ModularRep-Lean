import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerWitnesses
open scoped BigOperators
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerWitnesses
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulReconstructionChecks60

theorem reconstruction_row_60 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 60 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 60 j)) = true := by decide

theorem reconstruction_row_61 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 61 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 61 j)) = true := by decide

theorem reconstruction_row_62 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 62 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 62 j)) = true := by decide

theorem reconstruction_row_63 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 63 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 63 j)) = true := by decide

theorem reconstruction_row_64 : ∀ j : Fin 25,
    checkEq (reconstructionResidual 64 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 64 j)) = true := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulReconstructionChecks60


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
