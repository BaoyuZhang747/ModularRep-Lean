import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnData
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulColumnChecks00
open SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnData
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem column_row_0 : ∀ c : Fin 91,
    checkEq (sub (rawRow 0 c) (expandedPolynomial 0 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 0 c)) = true := by decide

theorem column_row_1 : ∀ c : Fin 91,
    checkEq (sub (rawRow 1 c) (expandedPolynomial 1 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 1 c)) = true := by decide

theorem column_row_2 : ∀ c : Fin 91,
    checkEq (sub (rawRow 2 c) (expandedPolynomial 2 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 2 c)) = true := by decide

theorem column_row_3 : ∀ c : Fin 91,
    checkEq (sub (rawRow 3 c) (expandedPolynomial 3 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 3 c)) = true := by decide

theorem column_row_4 : ∀ c : Fin 91,
    checkEq (sub (rawRow 4 c) (expandedPolynomial 4 c))
      (mul (fullModulus (fullTag c)) (fullQuotient 4 c)) = true := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulColumnChecks00


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
