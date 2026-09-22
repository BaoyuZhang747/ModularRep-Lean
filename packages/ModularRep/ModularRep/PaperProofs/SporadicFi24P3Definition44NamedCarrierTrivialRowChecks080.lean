import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
open scoped BigOperators
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialRowChecks080

theorem reconstruction_row_80 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 80 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 80 j)) = true := by decide

theorem duplicate_row_80 : ∀ c : Fin 91,
    rawRow 80 c = row 80 (columnLabel c) := by decide

theorem reconstruction_row_81 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 81 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 81 j)) = true := by decide

theorem duplicate_row_81 : ∀ c : Fin 91,
    rawRow 81 c = row 81 (columnLabel c) := by decide

theorem reconstruction_row_82 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 82 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 82 j)) = true := by decide

theorem duplicate_row_82 : ∀ c : Fin 91,
    rawRow 82 c = row 82 (columnLabel c) := by decide

theorem reconstruction_row_83 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 83 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 83 j)) = true := by decide

theorem duplicate_row_83 : ∀ c : Fin 91,
    rawRow 83 c = row 83 (columnLabel c) := by decide

theorem reconstruction_row_84 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 84 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 84 j)) = true := by decide

theorem duplicate_row_84 : ∀ c : Fin 91,
    rawRow 84 c = row 84 (columnLabel c) := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialRowChecks080


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
