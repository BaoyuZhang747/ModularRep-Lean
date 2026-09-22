import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
open scoped BigOperators
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialRowChecks060

theorem reconstruction_row_60 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 60 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 60 j)) = true := by decide

theorem duplicate_row_60 : ∀ c : Fin 91,
    rawRow 60 c = row 60 (columnLabel c) := by decide

theorem reconstruction_row_61 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 61 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 61 j)) = true := by decide

theorem duplicate_row_61 : ∀ c : Fin 91,
    rawRow 61 c = row 61 (columnLabel c) := by decide

theorem reconstruction_row_62 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 62 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 62 j)) = true := by decide

theorem duplicate_row_62 : ∀ c : Fin 91,
    rawRow 62 c = row 62 (columnLabel c) := by decide

theorem reconstruction_row_63 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 63 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 63 j)) = true := by decide

theorem duplicate_row_63 : ∀ c : Fin 91,
    rawRow 63 c = row 63 (columnLabel c) := by decide

theorem reconstruction_row_64 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 64 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 64 j)) = true := by decide

theorem duplicate_row_64 : ∀ c : Fin 91,
    rawRow 64 c = row 64 (columnLabel c) := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialRowChecks060


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
