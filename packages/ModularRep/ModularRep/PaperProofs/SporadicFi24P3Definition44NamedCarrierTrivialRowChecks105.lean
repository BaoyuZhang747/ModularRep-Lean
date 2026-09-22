import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
open scoped BigOperators
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialIntegerWitnesses
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialColumnData
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialRowChecks105

theorem reconstruction_row_105 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 105 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 105 j)) = true := by decide

theorem duplicate_row_105 : ∀ c : Fin 91,
    rawRow 105 c = row 105 (columnLabel c) := by decide

theorem reconstruction_row_106 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 106 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 106 j)) = true := by decide

theorem duplicate_row_106 : ∀ c : Fin 91,
    rawRow 106 c = row 106 (columnLabel c) := by decide

theorem reconstruction_row_107 : ∀ j : Fin 41,
    checkEq (reconstructionResidual 107 j)
      (mul (modulus (columnTag j)) (reconstructionQuotient 107 j)) = true := by decide

theorem duplicate_row_107 : ∀ c : Fin 91,
    rawRow 107 c = row 107 (columnLabel c) := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialRowChecks105


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
