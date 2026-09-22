import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnData
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulColumnChecks60
open SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnData
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem column_row_60 : ∀ c : Fin 91,
    checkEq (sub (rawRow 60 c) (expandedPolynomial 60 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 60 c)) = true := by decide

theorem column_row_61 : ∀ c : Fin 91,
    checkEq (sub (rawRow 61 c) (expandedPolynomial 61 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 61 c)) = true := by decide

theorem column_row_62 : ∀ c : Fin 91,
    checkEq (sub (rawRow 62 c) (expandedPolynomial 62 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 62 c)) = true := by decide

theorem column_row_63 : ∀ c : Fin 91,
    checkEq (sub (rawRow 63 c) (expandedPolynomial 63 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 63 c)) = true := by decide

theorem column_row_64 : ∀ c : Fin 91,
    checkEq (sub (rawRow 64 c) (expandedPolynomial 64 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 64 c)) = true := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulColumnChecks60


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
