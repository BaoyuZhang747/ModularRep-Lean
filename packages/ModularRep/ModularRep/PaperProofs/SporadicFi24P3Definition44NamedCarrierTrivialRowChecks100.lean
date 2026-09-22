import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
open scoped BigOperators
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialRowChecks100

theorem reconstruction_row_100 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 100 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 100 j)) = true := by decide

theorem duplicate_row_100 : ∀ c : Fin 91,
    rawRow 100 c = row 100 (columnLabel c) := by decide

theorem reconstruction_row_101 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 101 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 101 j)) = true := by decide

theorem duplicate_row_101 : ∀ c : Fin 91,
    rawRow 101 c = row 101 (columnLabel c) := by decide

theorem reconstruction_row_102 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 102 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 102 j)) = true := by decide

theorem duplicate_row_102 : ∀ c : Fin 91,
    rawRow 102 c = row 102 (columnLabel c) := by decide

theorem reconstruction_row_103 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 103 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 103 j)) = true := by decide

theorem duplicate_row_103 : ∀ c : Fin 91,
    rawRow 103 c = row 103 (columnLabel c) := by decide

theorem reconstruction_row_104 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 104 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 104 j)) = true := by decide

theorem duplicate_row_104 : ∀ c : Fin 91,
    rawRow 104 c = row 104 (columnLabel c) := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialRowChecks100


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
