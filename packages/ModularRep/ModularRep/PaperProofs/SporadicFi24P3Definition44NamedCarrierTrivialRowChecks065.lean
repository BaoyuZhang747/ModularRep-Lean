import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
open scoped BigOperators
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialRowChecks065

theorem reconstruction_row_65 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 65 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 65 j)) = true := by decide

theorem duplicate_row_65 : ∀ c : Fin 91,
    rawRow 65 c = row 65 (columnLabel c) := by decide

theorem reconstruction_row_66 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 66 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 66 j)) = true := by decide

theorem duplicate_row_66 : ∀ c : Fin 91,
    rawRow 66 c = row 66 (columnLabel c) := by decide

theorem reconstruction_row_67 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 67 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 67 j)) = true := by decide

theorem duplicate_row_67 : ∀ c : Fin 91,
    rawRow 67 c = row 67 (columnLabel c) := by decide

theorem reconstruction_row_68 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 68 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 68 j)) = true := by decide

theorem duplicate_row_68 : ∀ c : Fin 91,
    rawRow 68 c = row 68 (columnLabel c) := by decide

theorem reconstruction_row_69 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 69 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 69 j)) = true := by decide

theorem duplicate_row_69 : ∀ c : Fin 91,
    rawRow 69 c = row 69 (columnLabel c) := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialRowChecks065


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
