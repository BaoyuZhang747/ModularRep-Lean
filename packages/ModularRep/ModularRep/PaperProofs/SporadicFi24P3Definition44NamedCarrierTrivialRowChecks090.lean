import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
open scoped BigOperators
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialRowChecks090

theorem reconstruction_row_90 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 90 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 90 j)) = true := by decide

theorem duplicate_row_90 : ∀ c : Fin 91,
    rawRow 90 c = row 90 (columnLabel c) := by decide

theorem reconstruction_row_91 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 91 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 91 j)) = true := by decide

theorem duplicate_row_91 : ∀ c : Fin 91,
    rawRow 91 c = row 91 (columnLabel c) := by decide

theorem reconstruction_row_92 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 92 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 92 j)) = true := by decide

theorem duplicate_row_92 : ∀ c : Fin 91,
    rawRow 92 c = row 92 (columnLabel c) := by decide

theorem reconstruction_row_93 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 93 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 93 j)) = true := by decide

theorem duplicate_row_93 : ∀ c : Fin 91,
    rawRow 93 c = row 93 (columnLabel c) := by decide

theorem reconstruction_row_94 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 94 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 94 j)) = true := by decide

theorem duplicate_row_94 : ∀ c : Fin 91,
    rawRow 94 c = row 94 (columnLabel c) := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialRowChecks090


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
