import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnData
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulColumnChecks10
open SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnData
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem column_row_10 : ∀ c : Fin 91,
    checkEq (sub (rawRow 10 c) (expandedPolynomial 10 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 10 c)) = true := by decide

theorem column_row_11 : ∀ c : Fin 91,
    checkEq (sub (rawRow 11 c) (expandedPolynomial 11 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 11 c)) = true := by decide

theorem column_row_12 : ∀ c : Fin 91,
    checkEq (sub (rawRow 12 c) (expandedPolynomial 12 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 12 c)) = true := by decide

theorem column_row_13 : ∀ c : Fin 91,
    checkEq (sub (rawRow 13 c) (expandedPolynomial 13 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 13 c)) = true := by decide

theorem column_row_14 : ∀ c : Fin 91,
    checkEq (sub (rawRow 14 c) (expandedPolynomial 14 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 14 c)) = true := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulColumnChecks10


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
