import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
open scoped BigOperators
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialRowChecks000

theorem reconstruction_row_0 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 0 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 0 j)) = true := by decide

theorem duplicate_row_0 : ∀ c : Fin 91,
    rawRow 0 c = row 0 (columnLabel c) := by decide

theorem reconstruction_row_1 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 1 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 1 j)) = true := by decide

theorem duplicate_row_1 : ∀ c : Fin 91,
    rawRow 1 c = row 1 (columnLabel c) := by decide

theorem reconstruction_row_2 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 2 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 2 j)) = true := by decide

theorem duplicate_row_2 : ∀ c : Fin 91,
    rawRow 2 c = row 2 (columnLabel c) := by decide

theorem reconstruction_row_3 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 3 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 3 j)) = true := by decide

theorem duplicate_row_3 : ∀ c : Fin 91,
    rawRow 3 c = row 3 (columnLabel c) := by decide

theorem reconstruction_row_4 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 4 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 4 j)) = true := by decide

theorem duplicate_row_4 : ∀ c : Fin 91,
    rawRow 4 c = row 4 (columnLabel c) := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialRowChecks000


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
