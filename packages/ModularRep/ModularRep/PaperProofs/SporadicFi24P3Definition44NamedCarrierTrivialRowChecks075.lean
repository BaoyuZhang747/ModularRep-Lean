import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
open scoped BigOperators
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialRowChecks075

theorem reconstruction_row_75 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 75 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 75 j)) = true := by decide

theorem duplicate_row_75 : ∀ c : Fin 91,
    rawRow 75 c = row 75 (columnLabel c) := by decide

theorem reconstruction_row_76 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 76 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 76 j)) = true := by decide

theorem duplicate_row_76 : ∀ c : Fin 91,
    rawRow 76 c = row 76 (columnLabel c) := by decide

theorem reconstruction_row_77 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 77 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 77 j)) = true := by decide

theorem duplicate_row_77 : ∀ c : Fin 91,
    rawRow 77 c = row 77 (columnLabel c) := by decide

theorem reconstruction_row_78 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 78 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 78 j)) = true := by decide

theorem duplicate_row_78 : ∀ c : Fin 91,
    rawRow 78 c = row 78 (columnLabel c) := by decide

theorem reconstruction_row_79 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 79 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 79 j)) = true := by decide

theorem duplicate_row_79 : ∀ c : Fin 91,
    rawRow 79 c = row 79 (columnLabel c) := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialRowChecks075


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
