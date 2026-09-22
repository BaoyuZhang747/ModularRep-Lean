import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnData
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulColumnChecks55
open SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnData
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem column_row_55 : ∀ c : Fin 91,
    checkEq (sub (rawRow 55 c) (expandedPolynomial 55 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 55 c)) = true := by decide

theorem column_row_56 : ∀ c : Fin 91,
    checkEq (sub (rawRow 56 c) (expandedPolynomial 56 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 56 c)) = true := by decide

theorem column_row_57 : ∀ c : Fin 91,
    checkEq (sub (rawRow 57 c) (expandedPolynomial 57 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 57 c)) = true := by decide

theorem column_row_58 : ∀ c : Fin 91,
    checkEq (sub (rawRow 58 c) (expandedPolynomial 58 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 58 c)) = true := by decide

theorem column_row_59 : ∀ c : Fin 91,
    checkEq (sub (rawRow 59 c) (expandedPolynomial 59 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 59 c)) = true := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulColumnChecks55


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
