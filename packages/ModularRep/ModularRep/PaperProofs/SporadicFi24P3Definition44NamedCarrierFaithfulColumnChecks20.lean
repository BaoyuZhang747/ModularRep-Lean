import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnData
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulColumnChecks20
open SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnData
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem column_row_20 : ∀ c : Fin 91,
    checkEq (sub (rawRow 20 c) (expandedPolynomial 20 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 20 c)) = true := by decide

theorem column_row_21 : ∀ c : Fin 91,
    checkEq (sub (rawRow 21 c) (expandedPolynomial 21 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 21 c)) = true := by decide

theorem column_row_22 : ∀ c : Fin 91,
    checkEq (sub (rawRow 22 c) (expandedPolynomial 22 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 22 c)) = true := by decide

theorem column_row_23 : ∀ c : Fin 91,
    checkEq (sub (rawRow 23 c) (expandedPolynomial 23 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 23 c)) = true := by decide

theorem column_row_24 : ∀ c : Fin 91,
    checkEq (sub (rawRow 24 c) (expandedPolynomial 24 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 24 c)) = true := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulColumnChecks20


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
