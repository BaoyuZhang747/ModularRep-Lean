import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnData
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulColumnChecks15
open SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnData
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem column_row_15 : ∀ c : Fin 91,
    checkEq (sub (rawRow 15 c) (expandedPolynomial 15 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 15 c)) = true := by decide

theorem column_row_16 : ∀ c : Fin 91,
    checkEq (sub (rawRow 16 c) (expandedPolynomial 16 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 16 c)) = true := by decide

theorem column_row_17 : ∀ c : Fin 91,
    checkEq (sub (rawRow 17 c) (expandedPolynomial 17 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 17 c)) = true := by decide

theorem column_row_18 : ∀ c : Fin 91,
    checkEq (sub (rawRow 18 c) (expandedPolynomial 18 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 18 c)) = true := by decide

theorem column_row_19 : ∀ c : Fin 91,
    checkEq (sub (rawRow 19 c) (expandedPolynomial 19 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 19 c)) = true := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulColumnChecks15


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
