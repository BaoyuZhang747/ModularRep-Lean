import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
open scoped BigOperators
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialRowChecks025

theorem reconstruction_row_25 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 25 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 25 j)) = true := by decide

theorem duplicate_row_25 : ∀ c : Fin 91,
    rawRow 25 c = row 25 (columnLabel c) := by decide

theorem reconstruction_row_26 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 26 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 26 j)) = true := by decide

theorem duplicate_row_26 : ∀ c : Fin 91,
    rawRow 26 c = row 26 (columnLabel c) := by decide

theorem reconstruction_row_27 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 27 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 27 j)) = true := by decide

theorem duplicate_row_27 : ∀ c : Fin 91,
    rawRow 27 c = row 27 (columnLabel c) := by decide

theorem reconstruction_row_28 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 28 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 28 j)) = true := by decide

theorem duplicate_row_28 : ∀ c : Fin 91,
    rawRow 28 c = row 28 (columnLabel c) := by decide

theorem reconstruction_row_29 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 29 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 29 j)) = true := by decide

theorem duplicate_row_29 : ∀ c : Fin 91,
    rawRow 29 c = row 29 (columnLabel c) := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialRowChecks025


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
