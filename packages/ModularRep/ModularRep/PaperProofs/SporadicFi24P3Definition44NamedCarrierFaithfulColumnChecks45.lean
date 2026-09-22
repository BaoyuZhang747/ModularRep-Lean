import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnData
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulColumnChecks45
open SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnData
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem column_row_45 : ∀ c : Fin 91,
    checkEq (sub (rawRow 45 c) (expandedPolynomial 45 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 45 c)) = true := by decide

theorem column_row_46 : ∀ c : Fin 91,
    checkEq (sub (rawRow 46 c) (expandedPolynomial 46 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 46 c)) = true := by decide

theorem column_row_47 : ∀ c : Fin 91,
    checkEq (sub (rawRow 47 c) (expandedPolynomial 47 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 47 c)) = true := by decide

theorem column_row_48 : ∀ c : Fin 91,
    checkEq (sub (rawRow 48 c) (expandedPolynomial 48 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 48 c)) = true := by decide

theorem column_row_49 : ∀ c : Fin 91,
    checkEq (sub (rawRow 49 c) (expandedPolynomial 49 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 49 c)) = true := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulColumnChecks45


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
