import ModularRep.CyclicPCore
import Mathlib.RepresentationTheory.Equiv

/-!
# The integral basic set bridge

This file formalises the elementary permutation-lattice part of Lemma 2.8 in
the accompanying manuscript.  The index types `X` and `Y` model an invariant
integral basic set and the irreducible Brauer characters of a block.  Their
integral permutation modules are `MonoidAlgebra ℤ X` and
`MonoidAlgebra ℤ Y`.

The manuscript writes automorphism actions on the right.  An application of
the results below uses the corresponding left action, for example
`a • x = x ^ a⁻¹`.  This file does not connect its linear map to
`DecompositionMapInterface`, construct character index types, prove
nonnegativity of its coefficients, or establish a concrete integral basic
set.  The final argument takes two source shaped results as
explicit inputs: the integral consequence of Conlon's theorem that detects
marks at `p`-hypoelementary subgroups, and injectivity of the Burnside mark
homomorphism.  It does not assume the desired equivariant equivalence for the
particular indexing sets.
-/

namespace ModularRep.IntegralBasicSetBridge

variable {A X Y : Type*} [Group A] [MulAction A X] [MulAction A Y]

/-- An equivalence of sets that commutes with the `A`-actions. -/
def IsEquivariantSetEquiv (e : X ≃ Y) : Prop :=
  ∀ (a : A) (x : X), e (a • x) = a • e x

/-- The inverse of an equivariant equivalence is equivariant. -/
theorem isEquivariantSetEquiv_symm (e : X ≃ Y)
    (he : IsEquivariantSetEquiv (A := A) e) :
    IsEquivariantSetEquiv (A := A) e.symm := by
  intro a y
  apply e.injective
  rw [e.apply_symm_apply, he, e.apply_symm_apply]

/-- The finite group condition called `p`-hypoelementary in the manuscript:
the quotient by the largest normal `p`-subgroup is cyclic. -/
def IsPHypoelementary (p : ℕ) (H : Type*) [Group H] [Finite H] : Prop :=
  IsCyclic (H ⧸ ModularRep.pCore p H)

/-- Every subgroup of a finite `p`-hypoelementary group is
`p`-hypoelementary. -/
theorem isPHypoelementary_subgroup [Finite A]
    (p : ℕ) (hA : IsPHypoelementary p A) (U : Subgroup A) :
    IsPHypoelementary p U := by
  let _ : IsCyclic (A ⧸ ModularRep.pCore p A) := hA
  exact ModularRep.subgroup_quotient_pCore_isCyclic p U

/-- The `(x,y)` entry of a linear map between two integral permutation
modules.  After externally identifying the map with the restricted classical
decomposition map, this coefficient is a decomposition number in the
manuscript application. -/
noncomputable def decompositionMatrix
    (d : MonoidAlgebra ℤ X →ₗ[ℤ] MonoidAlgebra ℤ Y) (x : X) (y : Y) : ℤ :=
  (d (MonoidAlgebra.single x 1)).coeff y

/-- Simultaneous invariance of all entries of the decomposition matrix under
the actions on its row and column labels. -/
def MatrixEquivariant
    (d : MonoidAlgebra ℤ X →ₗ[ℤ] MonoidAlgebra ℤ Y) : Prop :=
  ∀ (a : A) (x : X) (y : Y),
    decompositionMatrix d (a • x) (a • y) = decompositionMatrix d x y

/-- Entrywise equivariance implies equivariance of the entire linear map
between the integral permutation modules. -/
theorem map_action_of_matrixEquivariant
    (d : MonoidAlgebra ℤ X →ₗ[ℤ] MonoidAlgebra ℤ Y)
    (hd : MatrixEquivariant (A := A) d)
    (a : A) (v : MonoidAlgebra ℤ X) :
    d (Representation.ofMulAction ℤ A X a v) =
      Representation.ofMulAction ℤ A Y a (d v) := by
  let lhs : MonoidAlgebra ℤ X →ₗ[ℤ] MonoidAlgebra ℤ Y :=
    d.comp (Representation.ofMulAction ℤ A X a)
  let rhs : MonoidAlgebra ℤ X →ₗ[ℤ] MonoidAlgebra ℤ Y :=
    (Representation.ofMulAction ℤ A Y a).comp d
  have hmaps : lhs = rhs := by
    refine MonoidAlgebra.lhom_ext' fun x ↦ LinearMap.ext_ring ?_
    ext y
    simp only [lhs, rhs, LinearMap.comp_apply]
    rw [Representation.coeff_ofMulAction]
    have h := hd a x (a⁻¹ • y)
    simpa [decompositionMatrix] using h
  exact DFunLike.congr_fun hmaps v

/-- Simultaneous invariance of the decomposition-matrix entries is equivalent
to the usual intertwining identity for the two permutation representations. -/
theorem matrixEquivariant_iff_intertwining
    (d : MonoidAlgebra ℤ X →ₗ[ℤ] MonoidAlgebra ℤ Y) :
    MatrixEquivariant (A := A) d ↔
      ∀ a : A,
        d.comp (Representation.ofMulAction ℤ A X a) =
          (Representation.ofMulAction ℤ A Y a).comp d := by
  constructor
  · intro hd a
    apply LinearMap.ext
    intro v
    exact map_action_of_matrixEquivariant d hd a v
  · intro hd a x y
    have h := DFunLike.congr_fun (hd a) (MonoidAlgebra.single x 1)
    have hc := congrArg (fun v : MonoidAlgebra ℤ Y ↦ v.coeff (a • y)) h
    simpa [decompositionMatrix] using hc

/-- An intertwining integral linear equivalence is an equivalence of the two
permutation representations. -/
noncomputable def permutationLatticeEquivOfIntertwining
    (d : MonoidAlgebra ℤ X ≃ₗ[ℤ] MonoidAlgebra ℤ Y)
    (hd : ∀ a : A,
      d.toLinearMap.comp (Representation.ofMulAction ℤ A X a) =
        (Representation.ofMulAction ℤ A Y a).comp d.toLinearMap) :
    (Representation.ofMulAction ℤ A X).Equiv
      (Representation.ofMulAction ℤ A Y) :=
  Representation.Equiv.mk d hd

/-- The defining linear equivalence of an equivariant integral basic set is
an isomorphism of integral permutation lattices. -/
noncomputable def permutationLatticeEquiv
    (d : MonoidAlgebra ℤ X ≃ₗ[ℤ] MonoidAlgebra ℤ Y)
    (hd : MatrixEquivariant (A := A) d.toLinearMap) :
    (Representation.ofMulAction ℤ A X).Equiv
      (Representation.ofMulAction ℤ A Y) :=
  permutationLatticeEquivOfIntertwining d
    ((matrixEquivariant_iff_intertwining d.toLinearMap).mp hd)

end ModularRep.IntegralBasicSetBridge


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
