import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnData
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulColumnChecks25
open SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnData
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem column_row_25 : ∀ c : Fin 91,
    checkEq (sub (rawRow 25 c) (expandedPolynomial 25 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 25 c)) = true := by decide

theorem column_row_26 : ∀ c : Fin 91,
    checkEq (sub (rawRow 26 c) (expandedPolynomial 26 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 26 c)) = true := by decide

theorem column_row_27 : ∀ c : Fin 91,
    checkEq (sub (rawRow 27 c) (expandedPolynomial 27 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 27 c)) = true := by decide

theorem column_row_28 : ∀ c : Fin 91,
    checkEq (sub (rawRow 28 c) (expandedPolynomial 28 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 28 c)) = true := by decide

theorem column_row_29 : ∀ c : Fin 91,
    checkEq (sub (rawRow 29 c) (expandedPolynomial 29 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 29 c)) = true := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulColumnChecks25


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
