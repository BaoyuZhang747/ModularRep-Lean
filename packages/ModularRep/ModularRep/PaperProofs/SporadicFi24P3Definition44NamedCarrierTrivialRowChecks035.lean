import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
open scoped BigOperators
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialRowChecks035

theorem reconstruction_row_35 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 35 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 35 j)) = true := by decide

theorem duplicate_row_35 : ∀ c : Fin 91,
    rawRow 35 c = row 35 (columnLabel c) := by decide

theorem reconstruction_row_36 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 36 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 36 j)) = true := by decide

theorem duplicate_row_36 : ∀ c : Fin 91,
    rawRow 36 c = row 36 (columnLabel c) := by decide

theorem reconstruction_row_37 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 37 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 37 j)) = true := by decide

theorem duplicate_row_37 : ∀ c : Fin 91,
    rawRow 37 c = row 37 (columnLabel c) := by decide

theorem reconstruction_row_38 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 38 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 38 j)) = true := by decide

theorem duplicate_row_38 : ∀ c : Fin 91,
    rawRow 38 c = row 38 (columnLabel c) := by decide

theorem reconstruction_row_39 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 39 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 39 j)) = true := by decide

theorem duplicate_row_39 : ∀ c : Fin 91,
    rawRow 39 c = row 39 (columnLabel c) := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialRowChecks035


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
