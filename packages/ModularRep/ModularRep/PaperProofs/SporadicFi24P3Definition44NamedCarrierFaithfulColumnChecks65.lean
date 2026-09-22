import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnData
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulColumnChecks65
open SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnData
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem column_row_65 : ∀ c : Fin 91,
    checkEq (sub (rawRow 65 c) (expandedPolynomial 65 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 65 c)) = true := by decide

theorem column_row_66 : ∀ c : Fin 91,
    checkEq (sub (rawRow 66 c) (expandedPolynomial 66 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 66 c)) = true := by decide

theorem column_row_67 : ∀ c : Fin 91,
    checkEq (sub (rawRow 67 c) (expandedPolynomial 67 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 67 c)) = true := by decide

theorem column_row_68 : ∀ c : Fin 91,
    checkEq (sub (rawRow 68 c) (expandedPolynomial 68 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 68 c)) = true := by decide

theorem column_row_69 : ∀ c : Fin 91,
    checkEq (sub (rawRow 69 c) (expandedPolynomial 69 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 69 c)) = true := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulColumnChecks65


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
