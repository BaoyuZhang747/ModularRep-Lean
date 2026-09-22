import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
open scoped BigOperators
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialRowChecks030

theorem reconstruction_row_30 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 30 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 30 j)) = true := by decide

theorem duplicate_row_30 : ∀ c : Fin 91,
    rawRow 30 c = row 30 (columnLabel c) := by decide

theorem reconstruction_row_31 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 31 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 31 j)) = true := by decide

theorem duplicate_row_31 : ∀ c : Fin 91,
    rawRow 31 c = row 31 (columnLabel c) := by decide

theorem reconstruction_row_32 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 32 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 32 j)) = true := by decide

theorem duplicate_row_32 : ∀ c : Fin 91,
    rawRow 32 c = row 32 (columnLabel c) := by decide

theorem reconstruction_row_33 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 33 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 33 j)) = true := by decide

theorem duplicate_row_33 : ∀ c : Fin 91,
    rawRow 33 c = row 33 (columnLabel c) := by decide

theorem reconstruction_row_34 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 34 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 34 j)) = true := by decide

theorem duplicate_row_34 : ∀ c : Fin 91,
    rawRow 34 c = row 34 (columnLabel c) := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialRowChecks030


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
