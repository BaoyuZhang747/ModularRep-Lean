import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
open scoped BigOperators
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialRowChecks015

theorem reconstruction_row_15 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 15 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 15 j)) = true := by decide

theorem duplicate_row_15 : ∀ c : Fin 91,
    rawRow 15 c = row 15 (columnLabel c) := by decide

theorem reconstruction_row_16 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 16 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 16 j)) = true := by decide

theorem duplicate_row_16 : ∀ c : Fin 91,
    rawRow 16 c = row 16 (columnLabel c) := by decide

theorem reconstruction_row_17 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 17 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 17 j)) = true := by decide

theorem duplicate_row_17 : ∀ c : Fin 91,
    rawRow 17 c = row 17 (columnLabel c) := by decide

theorem reconstruction_row_18 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 18 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 18 j)) = true := by decide

theorem duplicate_row_18 : ∀ c : Fin 91,
    rawRow 18 c = row 18 (columnLabel c) := by decide

theorem reconstruction_row_19 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 19 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 19 j)) = true := by decide

theorem duplicate_row_19 : ∀ c : Fin 91,
    rawRow 19 c = row 19 (columnLabel c) := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialRowChecks015


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
