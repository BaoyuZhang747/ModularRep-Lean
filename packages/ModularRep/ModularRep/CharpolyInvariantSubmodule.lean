import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
# Characteristic polynomials and invariant subspaces

The characteristic polynomial of an endomorphism factors as the product of
the characteristic polynomials on an invariant subspace and on the quotient.
This is the linear-algebraic input needed to prove additivity of Brauer
characters on exact sequences.
-/

noncomputable section

open Module

universe u v

variable {k : Type u} {V : Type v} [Field k] [AddCommGroup V]
  [Module k V] [FiniteDimensional k V]

/-- The characteristic polynomial of an endomorphism factors over an
invariant subspace and the induced endomorphism of the quotient. -/
theorem LinearMap.charpoly_eq_restrict_mul_mapQ
    (W : Submodule k V) (f : V →ₗ[k] V) (hf : W ≤ W.comap f) :
    f.charpoly = (f.restrict hf).charpoly * (W.mapQ W f hf).charpoly := by
  let m := Module.Free.ChooseBasisIndex k W
  let bW : Basis m k W := Module.Free.chooseBasis k W
  let n := Module.Free.ChooseBasisIndex k (V ⧸ W)
  let bQ : Basis n k (V ⧸ W) := Module.Free.chooseBasis k (V ⧸ W)
  let b := Module.Basis.sumQuot bW bQ
  let A : Matrix m m k := LinearMap.toMatrix bW bW (f.restrict hf)
  let B : Matrix m n k := Matrix.of fun i j ↦
    (b.repr (f (b (Sum.inr j)))) (Sum.inl i)
  let D : Matrix n n k := LinearMap.toMatrix bQ bQ (W.mapQ W f hf)
  suffices LinearMap.toMatrix b b f = Matrix.fromBlocks A B 0 D by
    rw [← LinearMap.charpoly_toMatrix f b, this,
      ← LinearMap.charpoly_toMatrix (f.restrict hf) bW,
      ← LinearMap.charpoly_toMatrix (W.mapQ W f hf) bQ,
      Matrix.charpoly_fromBlocks_zero₂₁]
  ext i j
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          simp only [b, Module.Basis.sumQuot_inl,
            Matrix.fromBlocks_apply₁₁, A, LinearMap.toMatrix_apply]
          apply Module.Basis.sumQuot_repr_inl_of_mem
      | inr j =>
          simp [b, LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₂, B]
  | inr i =>
      cases j with
      | inl j =>
          suffices W.mkQ (f (bW j)) = 0 by
            simp [LinearMap.toMatrix_apply, b, this]
          rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
          exact hf (Submodule.coe_mem (bW j))
      | inr j =>
          simp only [LinearMap.toMatrix_apply,
            Module.Basis.sumQuot_repr_inr,
            Matrix.fromBlocks_apply₂₂, b, D]
          rw [← Module.Basis.sumQuot_inr bW bQ j, W.mapQ_apply]
          simp


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
