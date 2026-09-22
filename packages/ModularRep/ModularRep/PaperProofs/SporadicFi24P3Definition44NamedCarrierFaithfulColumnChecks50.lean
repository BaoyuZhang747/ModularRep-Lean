import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnData
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulColumnChecks50
open SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnData
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem column_row_50 : ∀ c : Fin 91,
    checkEq (sub (rawRow 50 c) (expandedPolynomial 50 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 50 c)) = true := by decide

theorem column_row_51 : ∀ c : Fin 91,
    checkEq (sub (rawRow 51 c) (expandedPolynomial 51 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 51 c)) = true := by decide

theorem column_row_52 : ∀ c : Fin 91,
    checkEq (sub (rawRow 52 c) (expandedPolynomial 52 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 52 c)) = true := by decide

theorem column_row_53 : ∀ c : Fin 91,
    checkEq (sub (rawRow 53 c) (expandedPolynomial 53 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 53 c)) = true := by decide

theorem column_row_54 : ∀ c : Fin 91,
    checkEq (sub (rawRow 54 c) (expandedPolynomial 54 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 54 c)) = true := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulColumnChecks50


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
