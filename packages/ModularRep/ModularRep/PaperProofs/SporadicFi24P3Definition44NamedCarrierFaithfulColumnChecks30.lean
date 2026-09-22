import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnData
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulColumnChecks30
open SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnData
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem column_row_30 : ∀ c : Fin 91,
    checkEq (sub (rawRow 30 c) (expandedPolynomial 30 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 30 c)) = true := by decide

theorem column_row_31 : ∀ c : Fin 91,
    checkEq (sub (rawRow 31 c) (expandedPolynomial 31 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 31 c)) = true := by decide

theorem column_row_32 : ∀ c : Fin 91,
    checkEq (sub (rawRow 32 c) (expandedPolynomial 32 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 32 c)) = true := by decide

theorem column_row_33 : ∀ c : Fin 91,
    checkEq (sub (rawRow 33 c) (expandedPolynomial 33 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 33 c)) = true := by decide

theorem column_row_34 : ∀ c : Fin 91,
    checkEq (sub (rawRow 34 c) (expandedPolynomial 34 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 34 c)) = true := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulColumnChecks30


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
