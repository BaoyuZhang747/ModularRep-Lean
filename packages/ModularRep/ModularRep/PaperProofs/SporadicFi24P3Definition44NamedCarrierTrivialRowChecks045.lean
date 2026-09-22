import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
open scoped BigOperators
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialRowChecks045

theorem reconstruction_row_45 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 45 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 45 j)) = true := by decide

theorem duplicate_row_45 : ∀ c : Fin 91,
    rawRow 45 c = row 45 (columnLabel c) := by decide

theorem reconstruction_row_46 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 46 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 46 j)) = true := by decide

theorem duplicate_row_46 : ∀ c : Fin 91,
    rawRow 46 c = row 46 (columnLabel c) := by decide

theorem reconstruction_row_47 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 47 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 47 j)) = true := by decide

theorem duplicate_row_47 : ∀ c : Fin 91,
    rawRow 47 c = row 47 (columnLabel c) := by decide

theorem reconstruction_row_48 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 48 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 48 j)) = true := by decide

theorem duplicate_row_48 : ∀ c : Fin 91,
    rawRow 48 c = row 48 (columnLabel c) := by decide

theorem reconstruction_row_49 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 49 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 49 j)) = true := by decide

theorem duplicate_row_49 : ∀ c : Fin 91,
    rawRow 49 c = row 49 (columnLabel c) := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialRowChecks045


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
