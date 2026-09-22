import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulRootEvaluation
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerEvaluation
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierScalarColumnExpansion

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnEvaluation

open SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open SporadicFi24P3Definition44NamedCarrierFaithfulIntegerData
open SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnData
open SporadicFi24P3Definition44NamedCarrierFaithfulIntegerEvaluation
open SporadicFi24P3Definition44NamedCarrierFaithfulRootEvaluation
open SporadicFi24P3Definition44NamedCarrierScalarColumnExpansion

variable {K : Type*} [Field K] [CharZero K]

def rawEvaluatedRows (zeta : K) (r : Fin 74) (c : Fin 91) : K :=
  eval (fullRoots zeta (fullTag c)) (rawRow r c)

def evaluatedDescriptor (zeta : K) (c : Fin 91) : Option (Fin 25 × K) :=
  (columnDescription c).map fun je => (je.1, (zeta ^ 256795) ^ je.2.val)

omit [CharZero K] in
theorem evaluatedDescriptor_pivot (zeta : K) (j : Fin 25) :
    evaluatedDescriptor zeta (pivotColumn j) = some (j, 1) := by
  simp only [evaluatedDescriptor, columnDescription_pivot, Option.map_some,
    Fin.val_zero, pow_zero]

theorem rawEvaluatedRows_eq_expansion
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 770385)
    (hchecks : ColumnChecks) (r : Fin 74) :
    rawEvaluatedRows zeta r =
      columnExpansion (evaluatedDescriptor zeta) (evaluatedRows (localRoots zeta) r) := by
  funext c
  have h := checkEq_sound (fullRoots zeta (fullTag c))
    (sub (rawRow r c) (expandedPolynomial r c))
    (mul (fullModulus (fullTag c)) (fullQuotient r c)) (hchecks r c)
  rw [eval_mul, full_modulus_zero hzeta, zero_mul, eval_sub] at h
  have heq := sub_eq_zero.mp h
  change eval (fullRoots zeta (fullTag c)) (rawRow r c) = _
  rw [heq]
  cases hc : columnDescription c with
  | none =>
      have hd : evaluatedDescriptor zeta c = none := by
        simp only [evaluatedDescriptor, hc, Option.map_none]
      rw [columnExpansion_apply_none _ _ hd]
      simp only [expandedPolynomial, hc, eval]
  | some je =>
      rcases je with ⟨j, e⟩
      have hd : evaluatedDescriptor zeta c = some (j, (zeta ^ 256795) ^ e.val) := by
        simp only [evaluatedDescriptor, hc, Option.map_some]
      rw [columnExpansion_apply_some _ _ hd]
      have hdiv := descriptor_divisors c
      rw [hc] at hdiv
      change 3 ∣ fullConductor (fullTag c) ∧
        conductor (columnTag j) ∣ fullConductor (fullTag c) at hdiv
      simp only [expandedPolynomial, hc, eval_mul, eval_monomial,
        Int.cast_one, one_mul, eval_composeXPow]
      have hlocal :
          (fullRoots zeta (fullTag c)) ^
            (fullConductor (fullTag c) / conductor (columnTag j)) =
            localRoots zeta (columnTag j) :=
        rootPower_divisor zeta (fullConductor_dvd (fullTag c)) hdiv.2
      have hcentral :
          (fullRoots zeta (fullTag c)) ^
            ((fullConductor (fullTag c) / 3) * e.val) =
            (zeta ^ 256795) ^ e.val :=
        rootPower_divisor_mul zeta (fullConductor_dvd (fullTag c)) hdiv.1 e.val
      rw [hlocal, hcentral]
      rfl

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnEvaluation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
