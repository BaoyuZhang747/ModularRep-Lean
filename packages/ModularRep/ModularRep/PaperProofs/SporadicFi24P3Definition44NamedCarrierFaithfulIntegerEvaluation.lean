import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerWitnesses
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierGroupedDotProduct
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRowInverseCertificate

/-! Literal integer coefficient checks give the representative matrix certificate. -/

noncomputable section
open scoped BigOperators

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerEvaluation

open SporadicFi24P3Definition44NamedCarrierIntegerPolynomialCheck
open SporadicFi24P3Definition44NamedCarrierFaithfulIntegerData
open SporadicFi24P3Definition44NamedCarrierFaithfulIntegerWitnesses
open SporadicFi24P3Definition44NamedCarrierGroupedDotProduct
open SporadicFi24P3Definition44NamedCarrierRowInverseCertificate

variable {K : Type*} [Field K] [CharZero K]

def evaluatedRows (w : Fin 6 → K) (r : Fin 74) (j : Fin 25) : K :=
  eval (w (columnTag j)) (row r j)

def inverseNumerator (w : Fin 6 → K) (j b : Fin 25) : K :=
  eval (w (columnTag j)) (inverse j b)

def InverseChecks : Prop := ∀ a b d,
  checkEq (inverseGroup a b d)
    (add (mul (modulus d) (inverseQuotient a b d)) [inverseConstant a b d]) = true

def ConstantChecks : Prop := ∀ a b : Fin 25,
  (∑ d : Fin 6, inverseConstant a b d) = if a = b then inverseDenominator else 0

def ReconstructionChecks : Prop := ∀ r j,
  checkEq (reconstructionResidual r j)
    (mul (modulus (columnTag j)) (reconstructionQuotient r j)) = true

omit [CharZero K] in
theorem evaluated_scaled_dot
    (w : Fin 6 → K) (hmod : ∀ d, eval (w d) (modulus d) = 0)
    (hInverse : InverseChecks) (hConstant : ConstantChecks) (a b : Fin 25) :
    (∑ j : Fin 25, evaluatedRows w (basisPosition a) j * inverseNumerator w j b) =
      (inverseDenominator : K) * (if a = b then 1 else 0) := by
  apply dot_eq_scaled_delta_of_grouped_residuals columnTag
    (fun j => evaluatedRows w (basisPosition a) j)
    (fun j => inverseNumerator w j b)
    (fun d j => eval (w d) (row (basisPosition a) j) * eval (w d) (inverse j b))
    (inverseConstant a b) inverseDenominator a b
  · intro d j hj
    subst d
    rfl
  · intro d
    apply sub_eq_zero.mpr
    have h := eval_eq_const_of_check (w d) (inverseGroup a b d)
      (modulus d) (inverseQuotient a b d) (inverseConstant a b d)
      (hmod d) (hInverse a b d)
    simpa only [inverseGroup, eval_sumFin, apply_ite, eval_mul, eval] using h
  · exact hConstant a b

theorem evaluated_reconstruction
    (w : Fin 6 → K) (hmod : ∀ d, eval (w d) (modulus d) = 0)
    (hReconstruction : ReconstructionChecks) (r : Fin 74) :
    evaluatedRows w r = ∑ a : Fin 25,
      ((coefficient r a : K) / 2) • evaluatedRows w (basisPosition a) := by
  funext j
  have h := checkEq_sound (w (columnTag j)) (reconstructionResidual r j)
    (mul (modulus (columnTag j)) (reconstructionQuotient r j)) (hReconstruction r j)
  rw [eval_mul, hmod, zero_mul] at h
  simp only [reconstructionResidual, eval_sub, eval_scale, eval_sumFin,
    Int.cast_ofNat] at h
  have heq : (2 : K) * evaluatedRows w r j =
      ∑ a : Fin 25, (coefficient r a : K) * evaluatedRows w (basisPosition a) j :=
    sub_eq_zero.mp h
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc
    evaluatedRows w r j =
        (∑ a : Fin 25, (coefficient r a : K) * evaluatedRows w (basisPosition a) j) / 2 := by
      rw [← heq]
      rw [mul_comm (2 : K), mul_div_cancel_right₀ _ (by norm_num : (2 : K) ≠ 0)]
    _ = ∑ a : Fin 25,
        ((coefficient r a : K) / 2) * evaluatedRows w (basisPosition a) j := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      ring

def representativeRowInverseCertificate
    (w : Fin 6 → K) (hmod : ∀ d, eval (w d) (modulus d) = 0)
    (hInverse : InverseChecks) (hConstant : ConstantChecks)
    (hReconstruction : ReconstructionChecks) :
    RowInverseCertificate K (evaluatedRows w) 25 where
  basisPosition := basisPosition
  pivotColumn := id
  inverse := Matrix.of fun j b => inverseNumerator w j b / (inverseDenominator : K)
  right_inverse := by
    have hL : (inverseDenominator : K) ≠ 0 :=
      Int.cast_ne_zero.mpr (ne_of_gt inverseDenominator_pos)
    ext a b
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, id_eq]
    calc
      (∑ j : Fin 25, evaluatedRows w (basisPosition a) j *
          (inverseNumerator w j b / (inverseDenominator : K))) =
          (∑ j : Fin 25, evaluatedRows w (basisPosition a) j * inverseNumerator w j b) /
            (inverseDenominator : K) := by
        simp only [div_eq_mul_inv, Finset.sum_mul, mul_assoc]
      _ = (inverseDenominator : K) * (if a = b then 1 else 0) /
          (inverseDenominator : K) := by
        rw [evaluated_scaled_dot w hmod hInverse hConstant]
      _ = if a = b then 1 else 0 := by
        rw [mul_comm, mul_div_cancel_right₀ _ hL]
  coefficients := fun r a => (coefficient r a : K) / 2
  reconstruct := evaluated_reconstruction w hmod hReconstruction

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulIntegerEvaluation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
