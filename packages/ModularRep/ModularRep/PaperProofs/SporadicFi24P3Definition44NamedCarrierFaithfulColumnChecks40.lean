import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnData
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulColumnChecks40
open SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnData
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem column_row_40 : ∀ c : Fin 91,
    checkEq (sub (rawRow 40 c) (expandedPolynomial 40 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 40 c)) = true := by decide

theorem column_row_41 : ∀ c : Fin 91,
    checkEq (sub (rawRow 41 c) (expandedPolynomial 41 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 41 c)) = true := by decide

theorem column_row_42 : ∀ c : Fin 91,
    checkEq (sub (rawRow 42 c) (expandedPolynomial 42 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 42 c)) = true := by decide

theorem column_row_43 : ∀ c : Fin 91,
    checkEq (sub (rawRow 43 c) (expandedPolynomial 43 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 43 c)) = true := by decide

theorem column_row_44 : ∀ c : Fin 91,
    checkEq (sub (rawRow 44 c) (expandedPolynomial 44 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 44 c)) = true := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulColumnChecks40


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
