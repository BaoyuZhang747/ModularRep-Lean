import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
open scoped BigOperators
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialRowChecks040

theorem reconstruction_row_40 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 40 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 40 j)) = true := by decide

theorem duplicate_row_40 : ∀ c : Fin 91,
    rawRow 40 c = row 40 (columnLabel c) := by decide

theorem reconstruction_row_41 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 41 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 41 j)) = true := by decide

theorem duplicate_row_41 : ∀ c : Fin 91,
    rawRow 41 c = row 41 (columnLabel c) := by decide

theorem reconstruction_row_42 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 42 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 42 j)) = true := by decide

theorem duplicate_row_42 : ∀ c : Fin 91,
    rawRow 42 c = row 42 (columnLabel c) := by decide

theorem reconstruction_row_43 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 43 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 43 j)) = true := by decide

theorem duplicate_row_43 : ∀ c : Fin 91,
    rawRow 43 c = row 43 (columnLabel c) := by decide

theorem reconstruction_row_44 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 44 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 44 j)) = true := by decide

theorem duplicate_row_44 : ∀ c : Fin 91,
    rawRow 44 c = row 44 (columnLabel c) := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialRowChecks040


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
