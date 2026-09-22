import ModularRep.EvaluationMatrix
import ModularRep.ModularTraceRegularPart

/-!
# Evaluation matrices on prime regular elements

This file combines the abstract evaluation matrix theorem with the fact that
modular traces depend only on the prime regular part of a group element.
-/

namespace ModularRep.PrimeRegularEvaluationMatrix

universe u v w

variable {k : Type u} {G : Type v} {ι : Type w}
variable [Field k] [Group G] [Finite G]
variable {p : ℕ}

/-- A finite linearly independent family of functions which depends only on
the `p`-regular part admits a nonsingular evaluation matrix on `p`-regular
elements. -/
theorem exists_primeRegular_evaluation_det_ne_zero
    [Fintype ι] [DecidableEq ι]
    (hp : p.Prime) (f : ι → G → k) (hf : LinearIndependent k f)
    (hregular : ∀ i g, f i g = f i (primeRegularPart hp g)) :
    ∃ x : ι → PrimeRegularElement (G := G) p,
      Matrix.det (fun i j ↦ f i (x j).1) ≠ 0 := by
  classical
  obtain ⟨y, hy⟩ :=
    EvaluationMatrix.exists_evaluation_det_ne_zero f hf
  let x : ι → PrimeRegularElement (G := G) p := fun j ↦
    ⟨primeRegularPart hp (y j), primeRegular_primeRegularPart hp (y j)⟩
  refine ⟨x, ?_⟩
  have hmatrix :
      (fun i j ↦ f i (x j).1) = (fun i j ↦ f i (y j)) := by
    funext i j
    exact (hregular i (y j)).symm
  rw [hmatrix]
  exact hy

/-- A finite linearly independent family of trace functions of bundled finite
dimensional representations admits a nonsingular evaluation matrix on
`p`-regular elements. -/
theorem exists_fdRep_character_evaluation_det_ne_zero
    [CharP k p] [Fintype ι] [DecidableEq ι]
    (hp : p.Prime) (rho : ι → FDRep k G)
    (hchars : LinearIndependent k (fun i ↦ (rho i).character)) :
    ∃ x : ι → PrimeRegularElement (G := G) p,
      Matrix.det (fun i j ↦ (rho i).character (x j).1) ≠ 0 := by
  apply exists_primeRegular_evaluation_det_ne_zero hp
    (fun i ↦ (rho i).character) hchars
  intro i g
  exact Representation.character_eq_character_primeRegularPart hp (rho i).ρ g

end ModularRep.PrimeRegularEvaluationMatrix


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
