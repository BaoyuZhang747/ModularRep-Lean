import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnData
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulColumnChecks70
open SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnData
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem column_row_70 : ∀ c : Fin 91,
    checkEq (sub (rawRow 70 c) (expandedPolynomial 70 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 70 c)) = true := by decide

theorem column_row_71 : ∀ c : Fin 91,
    checkEq (sub (rawRow 71 c) (expandedPolynomial 71 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 71 c)) = true := by decide

theorem column_row_72 : ∀ c : Fin 91,
    checkEq (sub (rawRow 72 c) (expandedPolynomial 72 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 72 c)) = true := by decide

theorem column_row_73 : ∀ c : Fin 91,
    checkEq (sub (rawRow 73 c) (expandedPolynomial 73 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 73 c)) = true := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulColumnChecks70


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
