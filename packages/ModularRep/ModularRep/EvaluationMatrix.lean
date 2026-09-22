import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Nonsingular evaluation matrices

A finite linearly independent family of scalar-valued functions admits a
choice of evaluation points for which the square evaluation matrix has
nonzero determinant.  The evaluation domain need not be finite.  This is the
linear-algebra step used when passing from independence of modular trace
functions to an evaluation determinant in the proof of linear independence
of Brauer characters.
-/

open scoped Matrix

namespace ModularRep.EvaluationMatrix

theorem pi_basisFun_toDualEquiv_apply {K ι : Type*}
    [Field K] [Fintype ι] [DecidableEq ι]
    (c y : ι → K) :
    (Pi.basisFun K ι).toDualEquiv c y = ∑ i, c i * y i := by
  let b := Pi.basisFun K ι
  change b.toDual c y = _
  conv_lhs => rw [← b.sum_equivFun c]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul, b.toDual_apply_right, Module.Basis.equivFun_apply]
  simp [b]

theorem exists_evaluation_linearIndependent
    {K ι Ω : Type*} [Field K] [Finite ι]
    (f : ι → Ω → K) (hf : LinearIndependent K f) :
    ∃ x : ι → Ω, LinearIndependent K (fun j i ↦ f i (x j)) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let v : Ω → (ι → K) := fun x i ↦ f i x
  have hspan : Submodule.span K (Set.range v) = ⊤ := by
    rw [← Submodule.dualAnnihilator_eq_bot_iff]
    apply le_antisymm
    · intro phi hphi
      rw [Submodule.mem_bot]
      let b := Pi.basisFun K ι
      let c : ι → K := b.toDualEquiv.symm phi
      have hbc : b.toDualEquiv c = phi := b.toDualEquiv.apply_symm_apply phi
      have hcomb : Fintype.linearCombination K f c = 0 := by
        ext x
        have hx : phi (v x) = 0 :=
          (Submodule.mem_dualAnnihilator phi).mp hphi (v x)
            (Submodule.subset_span (Set.mem_range_self x))
        rw [← hbc, pi_basisFun_toDualEquiv_apply] at hx
        simpa [Fintype.linearCombination_apply, v, smul_eq_mul] using hx
      have hc : c = 0 := hf.fintypeLinearCombination_injective (by simpa using hcomb)
      rw [← hbc, hc, map_zero]
    · exact bot_le
  obtain ⟨κ, a, _ha, hspan', hcols⟩ := exists_linearIndependent' K v
  let _ : Finite κ := hcols.finite
  let _ : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = Fintype.card ι := by
    calc
      Fintype.card κ = Set.finrank K (Set.range (v ∘ a)) :=
        linearIndependent_iff_card_eq_finrank_span.mp hcols
      _ = Module.finrank K ↥(Submodule.span K (Set.range (v ∘ a))) := rfl
      _ = Module.finrank K ↥(Submodule.span K (Set.range v)) := by rw [hspan']
      _ = Module.finrank K ↥(⊤ : Submodule K (ι → K)) := by rw [hspan]
      _ = Module.finrank K (ι → K) := by simp
      _ = Fintype.card ι := Module.finrank_fintype_fun_eq_card K
  let e : ι ≃ κ := Fintype.equivOfCardEq hcard.symm
  let x : ι → Ω := fun i ↦ a (e i)
  refine ⟨x, ?_⟩
  have h := hcols.comp e e.injective
  simpa [x, v, Function.comp_def] using h

theorem exists_evaluation_det_ne_zero
    {K ι Ω : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (f : ι → Ω → K) (hf : LinearIndependent K f) :
    ∃ x : ι → Ω, Matrix.det (fun i j ↦ f i (x j)) ≠ 0 := by
  classical
  obtain ⟨x, hx⟩ := exists_evaluation_linearIndependent f hf
  refine ⟨x, ?_⟩
  let M : Matrix ι ι K := fun i j ↦ f i (x j)
  have hMcols : LinearIndependent K M.col := by
    have heq : M.col = fun j i ↦ f i (x j) := by
      funext j i
      rfl
    rw [heq]
    exact hx
  have hMunit : IsUnit M := Matrix.linearIndependent_cols_iff_isUnit.mp hMcols
  exact ((Matrix.isUnit_iff_isUnit_det M).mp hMunit).ne_zero

end ModularRep.EvaluationMatrix


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
