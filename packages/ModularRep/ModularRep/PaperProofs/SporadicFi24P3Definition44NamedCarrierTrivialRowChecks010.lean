import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
open scoped BigOperators
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialRowChecks010

theorem reconstruction_row_10 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 10 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 10 j)) = true := by decide

theorem duplicate_row_10 : ∀ c : Fin 91,
    rawRow 10 c = row 10 (columnLabel c) := by decide

theorem reconstruction_row_11 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 11 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 11 j)) = true := by decide

theorem duplicate_row_11 : ∀ c : Fin 91,
    rawRow 11 c = row 11 (columnLabel c) := by decide

theorem reconstruction_row_12 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 12 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 12 j)) = true := by decide

theorem duplicate_row_12 : ∀ c : Fin 91,
    rawRow 12 c = row 12 (columnLabel c) := by decide

theorem reconstruction_row_13 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 13 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 13 j)) = true := by decide

theorem duplicate_row_13 : ∀ c : Fin 91,
    rawRow 13 c = row 13 (columnLabel c) := by decide

theorem reconstruction_row_14 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 14 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 14 j)) = true := by decide

theorem duplicate_row_14 : ∀ c : Fin 91,
    rawRow 14 c = row 14 (columnLabel c) := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialRowChecks010


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
