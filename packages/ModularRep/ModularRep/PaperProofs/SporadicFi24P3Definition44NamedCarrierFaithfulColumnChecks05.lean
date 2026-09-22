import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnData
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulColumnChecks05
open SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnData
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem column_row_5 : ∀ c : Fin 91,
    checkEq (sub (rawRow 5 c) (expandedPolynomial 5 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 5 c)) = true := by decide

theorem column_row_6 : ∀ c : Fin 91,
    checkEq (sub (rawRow 6 c) (expandedPolynomial 6 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 6 c)) = true := by decide

theorem column_row_7 : ∀ c : Fin 91,
    checkEq (sub (rawRow 7 c) (expandedPolynomial 7 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 7 c)) = true := by decide

theorem column_row_8 : ∀ c : Fin 91,
    checkEq (sub (rawRow 8 c) (expandedPolynomial 8 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 8 c)) = true := by decide

theorem column_row_9 : ∀ c : Fin 91,
    checkEq (sub (rawRow 9 c) (expandedPolynomial 9 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 9 c)) = true := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulColumnChecks05


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
