import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
open scoped BigOperators
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialRowChecks095

theorem reconstruction_row_95 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 95 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 95 j)) = true := by decide

theorem duplicate_row_95 : ∀ c : Fin 91,
    rawRow 95 c = row 95 (columnLabel c) := by decide

theorem reconstruction_row_96 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 96 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 96 j)) = true := by decide

theorem duplicate_row_96 : ∀ c : Fin 91,
    rawRow 96 c = row 96 (columnLabel c) := by decide

theorem reconstruction_row_97 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 97 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 97 j)) = true := by decide

theorem duplicate_row_97 : ∀ c : Fin 91,
    rawRow 97 c = row 97 (columnLabel c) := by decide

theorem reconstruction_row_98 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 98 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 98 j)) = true := by decide

theorem duplicate_row_98 : ∀ c : Fin 91,
    rawRow 98 c = row 98 (columnLabel c) := by decide

theorem reconstruction_row_99 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 99 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 99 j)) = true := by decide

theorem duplicate_row_99 : ∀ c : Fin 91,
    rawRow 99 c = row 99 (columnLabel c) := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialRowChecks095


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
