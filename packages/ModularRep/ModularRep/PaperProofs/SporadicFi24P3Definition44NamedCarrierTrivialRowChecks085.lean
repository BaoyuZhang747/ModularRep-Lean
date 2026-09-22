import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
open scoped BigOperators
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialRowChecks085

theorem reconstruction_row_85 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 85 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 85 j)) = true := by decide

theorem duplicate_row_85 : ∀ c : Fin 91,
    rawRow 85 c = row 85 (columnLabel c) := by decide

theorem reconstruction_row_86 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 86 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 86 j)) = true := by decide

theorem duplicate_row_86 : ∀ c : Fin 91,
    rawRow 86 c = row 86 (columnLabel c) := by decide

theorem reconstruction_row_87 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 87 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 87 j)) = true := by decide

theorem duplicate_row_87 : ∀ c : Fin 91,
    rawRow 87 c = row 87 (columnLabel c) := by decide

theorem reconstruction_row_88 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 88 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 88 j)) = true := by decide

theorem duplicate_row_88 : ∀ c : Fin 91,
    rawRow 88 c = row 88 (columnLabel c) := by decide

theorem reconstruction_row_89 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 89 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 89 j)) = true := by decide

theorem duplicate_row_89 : ∀ c : Fin 91,
    rawRow 89 c = row 89 (columnLabel c) := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialRowChecks085


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
