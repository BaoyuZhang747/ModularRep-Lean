import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
open scoped BigOperators
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialRowChecks070

theorem reconstruction_row_70 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 70 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 70 j)) = true := by decide

theorem duplicate_row_70 : ∀ c : Fin 91,
    rawRow 70 c = row 70 (columnLabel c) := by decide

theorem reconstruction_row_71 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 71 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 71 j)) = true := by decide

theorem duplicate_row_71 : ∀ c : Fin 91,
    rawRow 71 c = row 71 (columnLabel c) := by decide

theorem reconstruction_row_72 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 72 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 72 j)) = true := by decide

theorem duplicate_row_72 : ∀ c : Fin 91,
    rawRow 72 c = row 72 (columnLabel c) := by decide

theorem reconstruction_row_73 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 73 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 73 j)) = true := by decide

theorem duplicate_row_73 : ∀ c : Fin 91,
    rawRow 73 c = row 73 (columnLabel c) := by decide

theorem reconstruction_row_74 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 74 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 74 j)) = true := by decide

theorem duplicate_row_74 : ∀ c : Fin 91,
    rawRow 74 c = row 74 (columnLabel c) := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialRowChecks070


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
