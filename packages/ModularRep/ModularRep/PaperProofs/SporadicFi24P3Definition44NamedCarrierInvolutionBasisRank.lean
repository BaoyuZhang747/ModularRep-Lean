import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Trace
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

/-!
# Fixed basis indices from the rank of an involutive symmetrization

The finite basis permutation determines its trace. The projection
(1 + T) / 2 relates that trace to the rank of 1 + T.
No character, block, table or correspondence source occurs here.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierInvolutionBasisRank

universe u v w
variable {K : Type u} [Field K]

theorem trace_eq_cast_natCard_fixedPoints_of_basis_action
    {I : Type v} {V : Type w} [Fintype I] [DecidableEq I]
    [AddCommGroup V] [Module K V]
    (b : Module.Basis I K V) (T : V →ₗ[K] V) (sigma : Equiv.Perm I)
    (hT : ∀ i, T (b i) = b (sigma i)) :
    LinearMap.trace K V T =
      (Nat.card (Function.fixedPoints sigma) : K) := by
  have hmatrix :
      LinearMap.toMatrix b b T = (sigma.permMatrix K).transpose := by
    ext i j
    rw [LinearMap.toMatrix_apply, hT j]
    simp [Matrix.transpose_apply, Equiv.Perm.permMatrix,
      PEquiv.toMatrix_apply, Finsupp.single_apply, eq_comm]
  rw [LinearMap.trace_eq_matrix_trace K b T, hmatrix,
    Matrix.trace_transpose, Matrix.trace_permutation, Nat.card_coe_set_eq]

theorem trace_eq_two_mul_finrank_range_id_add_sub_finrank
    [CharZero K]
    {I : Type v} {V : Type w} [Fintype I] [DecidableEq I]
    [AddCommGroup V] [Module K V]
    (b : Module.Basis I K V) (T : V →ₗ[K] V) (sigma : Equiv.Perm I)
    (hT : ∀ i, T (b i) = b (sigma i))
    (hsigma : Function.Involutive sigma) :
    LinearMap.trace K V T =
      (2 : K) *
          (Module.finrank K (LinearMap.range (LinearMap.id + T)) : K) -
        (Module.finrank K V : K) := by
  let _ : FiniteDimensional K V := b.finiteDimensional_of_finite
  have hT_sq : T * T = 1 := by
    apply b.ext
    intro i
    change T (T (b i)) = b i
    rw [hT i, hT (sigma i), hsigma i]
  let A : V →ₗ[K] V := LinearMap.id + T
  let P : V →ₗ[K] V := (2 : K)⁻¹ • A
  have htwo : (2 : K) ≠ 0 := by norm_num
  have hP : IsIdempotentElem P := by
    rw [IsIdempotentElem]
    ext x
    have hT_sq_x := LinearMap.congr_fun hT_sq x
    simp only [Module.End.mul_apply] at hT_sq_x
    simp only [P, A, Module.End.mul_apply, LinearMap.smul_apply,
      LinearMap.add_apply, LinearMap.id_coe, id_eq, map_smul, map_add, hT_sq_x]
    module
  have hrange : LinearMap.range P = LinearMap.range A :=
    LinearMap.range_smul A (2 : K)⁻¹ (inv_ne_zero htwo)
  have htraceP : LinearMap.trace K V P =
      (Module.finrank K (LinearMap.range P) : K) :=
    ((LinearMap.isProj_range_iff_isIdempotentElem P).2 hP).trace
  have htraceExpand : LinearMap.trace K V P =
      (2 : K)⁻¹ *
        ((Module.finrank K V : K) + LinearMap.trace K V T) := by
    simp [P, A, LinearMap.trace_id, smul_eq_mul]
    ring
  have heq : (Module.finrank K (LinearMap.range A) : K) =
      (2 : K)⁻¹ *
        ((Module.finrank K V : K) + LinearMap.trace K V T) := by
    rw [← hrange, ← htraceP]
    exact htraceExpand
  rw [show LinearMap.id + T = A from rfl]
  calc
    LinearMap.trace K V T =
        (2 : K) * ((2 : K)⁻¹ *
          ((Module.finrank K V : K) + LinearMap.trace K V T)) -
          (Module.finrank K V : K) := by
      field_simp
      ring
    _ = (2 : K) * (Module.finrank K (LinearMap.range A) : K) -
          (Module.finrank K V : K) := by rw [← heq]

theorem fixed_card_add_card_eq_two_mul_plus_rank
    [CharZero K]
    {I : Type v} {V : Type w} [Fintype I] [DecidableEq I]
    [AddCommGroup V] [Module K V]
    (b : Module.Basis I K V) (T : V →ₗ[K] V) (sigma : Equiv.Perm I)
    (hT : ∀ i, T (b i) = b (sigma i))
    (hsigma : Function.Involutive sigma) :
    Nat.card (Function.fixedPoints sigma) + Nat.card I =
      2 * Module.finrank K (LinearMap.range (LinearMap.id + T)) := by
  have htrace := trace_eq_cast_natCard_fixedPoints_of_basis_action b T sigma hT
  have hrank := trace_eq_two_mul_finrank_range_id_add_sub_finrank b T sigma hT hsigma
  have hdim : Module.finrank K V = Nat.card I := Module.finrank_eq_nat_card_basis b
  have hcast : (Nat.card (Function.fixedPoints sigma) : K) + (Nat.card I : K) =
      (2 : K) * (Module.finrank K (LinearMap.range (LinearMap.id + T)) : K) := by
    rw [← htrace, ← hdim, hrank]
    ring
  exact_mod_cast hcast

/-- Intermediate ranks must be derived independently before this arithmetic step. -/
theorem fixed_card_eq_thirty_one_of_ranks
    [CharZero K]
    {I : Type v} {V : Type w} [Fintype I] [DecidableEq I]
    [AddCommGroup V] [Module K V]
    (b : Module.Basis I K V) (T : V →ₗ[K] V) (sigma : Equiv.Perm I)
    (hT : ∀ i, T (b i) = b (sigma i))
    (hsigma : Function.Involutive sigma)
    (hraw : Module.finrank K V = 41)
    (hplus : Module.finrank K (LinearMap.range (LinearMap.id + T)) = 36) :
    Nat.card (Function.fixedPoints sigma) = 31 := by
  have hcard : Nat.card I = 41 :=
    (Module.finrank_eq_nat_card_basis b).symm.trans hraw
  have h := fixed_card_add_card_eq_two_mul_plus_rank b T sigma hT hsigma
  rw [hcard, hplus] at h
  omega

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierInvolutionBasisRank


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
