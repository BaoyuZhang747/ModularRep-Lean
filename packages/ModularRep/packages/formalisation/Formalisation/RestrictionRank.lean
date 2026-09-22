import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# The linear algebra behind the restriction-rank calculation

This file formalises the abstract linear-algebra step used in
`eq:restriction-rank` in the computational appendix.  Here `coeff` models the
decomposition matrix: its surjectivity is the full-column-rank hypothesis.
The map `eval` sends the coordinate vectors to the irreducible Brauer
characters: its injectivity is their linear independence.  The composite
therefore has the same range, and hence the same dimension, as `eval`.

This does not formalise Brauer characters, decomposition matrices, or the GAP
calculations that establish the hypotheses in particular blocks.
-/

namespace Formalisation.RestrictionRank

variable {K M N V : Type*}
variable [Field K]
variable [AddCommGroup M] [Module K M]
variable [AddCommGroup N] [Module K N]
variable [AddCommGroup V] [Module K V]

/-- Precomposing a linear map with a surjective coefficient map does not
change its range. -/
theorem range_comp_eq_range_of_surjective
    (coeff : M →ₗ[K] N) (eval : N →ₗ[K] V)
    (hcoeff : Function.Surjective coeff) :
    LinearMap.range (eval.comp coeff) = LinearMap.range eval := by
  apply LinearMap.range_comp_of_range_eq_top
  exact LinearMap.range_eq_top.mpr hcoeff

/-- The span of the restricted ordinary characters has the dimension of the
coordinate space for the Brauer characters. -/
theorem finrank_range_comp_eq
    (coeff : M →ₗ[K] N) (eval : N →ₗ[K] V)
    (hcoeff : Function.Surjective coeff) (heval : Function.Injective eval) :
    Module.finrank K (LinearMap.range (eval.comp coeff)) = Module.finrank K N := by
  rw [range_comp_eq_range_of_surjective coeff eval hcoeff]
  exact LinearMap.finrank_range_of_inj heval

/-- If the coordinate space is indexed by a finite set, its dimension is the
number of indices.  This is the precise numerical form used for
`|IBr(b)|` in the manuscript. -/
theorem finrank_range_comp_eq_card {ι : Type*} [Fintype ι]
    (coeff : M →ₗ[K] (ι → K)) (eval : (ι → K) →ₗ[K] V)
    (hcoeff : Function.Surjective coeff) (heval : Function.Injective eval) :
    Module.finrank K (LinearMap.range (eval.comp coeff)) = Fintype.card ι := by
  rw [finrank_range_comp_eq coeff eval hcoeff heval]
  exact Module.finrank_fintype_fun_eq_card K

/-- Matrix form of the restriction-rank argument.  The vectors `rows i`
are the rows of the decomposition matrix, and `brauer` is the family of
irreducible Brauer characters.  Full row span is the transpose formulation
of full column rank.  The linear combinations represented by the rows then
span a space whose dimension is the number of Brauer characters. -/
theorem finrank_span_matrix_combinations_eq_card
    {ι κ : Type*} [Fintype ι] [Finite κ]
    (rows : κ → (ι → K)) (brauer : ι → V)
    (hrows : Submodule.span K (Set.range rows) = ⊤)
    (hbrauer : LinearIndependent K brauer) :
    Module.finrank K
        (Submodule.span K
          (Set.range fun i => Fintype.linearCombination K brauer (rows i))) =
      Fintype.card ι := by
  let _ := Fintype.ofFinite κ
  let coeff : (κ → K) →ₗ[K] (ι → K) := Fintype.linearCombination K rows
  let eval : (ι → K) →ₗ[K] V := Fintype.linearCombination K brauer
  have hcoeff : Function.Surjective coeff := by
    exact (span_range_eq_top_iff_surjective_fintypeLinearCombination K rows).mp hrows
  have heval : Function.Injective eval := by
    exact hbrauer.fintypeLinearCombination_injective
  have hcomp :
      Fintype.linearCombination K
          (fun i => Fintype.linearCombination K brauer (rows i)) =
        eval.comp coeff := by
    ext c
    simp [coeff, eval, Fintype.linearCombination_apply, map_sum]
  rw [← Fintype.range_linearCombination, hcomp]
  exact finrank_range_comp_eq_card coeff eval hcoeff heval

end Formalisation.RestrictionRank


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
