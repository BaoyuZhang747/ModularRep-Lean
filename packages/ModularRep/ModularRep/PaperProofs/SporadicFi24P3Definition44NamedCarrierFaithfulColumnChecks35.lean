import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnData
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulColumnChecks35
open SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnData
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem column_row_35 : ∀ c : Fin 91,
    checkEq (sub (rawRow 35 c) (expandedPolynomial 35 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 35 c)) = true := by decide

theorem column_row_36 : ∀ c : Fin 91,
    checkEq (sub (rawRow 36 c) (expandedPolynomial 36 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 36 c)) = true := by decide

theorem column_row_37 : ∀ c : Fin 91,
    checkEq (sub (rawRow 37 c) (expandedPolynomial 37 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 37 c)) = true := by decide

theorem column_row_38 : ∀ c : Fin 91,
    checkEq (sub (rawRow 38 c) (expandedPolynomial 38 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 38 c)) = true := by decide

theorem column_row_39 : ∀ c : Fin 91,
    checkEq (sub (rawRow 39 c) (expandedPolynomial 39 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 39 c)) = true := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulColumnChecks35


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
