import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Central functions induced from a subgroup algebra

Let `H ≤ G`.  This file supplies the elementary group algebra part of the
central-function construction used in block induction: restrict the
coefficients of an element of `k[G]` to the indices in `H`, prove that this
restriction carries `Z(k[G])` into `Z(k[H])`, and compose the resulting linear
map with a supplied algebra homomorphism `Z(k[H]) →ₐ[k] k`.

## Kernel content

The centrality statement is proved here.  A central element of `k[G]` has the
same coefficient on elements conjugate in `G`; in particular its restricted
coefficients are constant under conjugation by `H`.  The proof below expresses
this directly by commuting with the single terms of `k[H]`.

## Deliberate boundary

Coefficient restriction is not multiplicative in general.  Consequently both
`centerCoeffRestrict` and `inducedCentralFunction` are linear maps, not algebra
homomorphisms.  Any assertion that the induced central function is
multiplicative, or that it determines an induced block, is additional
block-theoretic input and is not claimed in this file.
-/

namespace ModularRep

open MonoidAlgebra

noncomputable section

variable {k G : Type*} [CommSemiring k] [Group G]

/-- The centre `Z(k[G])` of a group algebra, retained as a `k`-subalgebra so
that source central characters can be expressed by algebra homomorphisms. -/
abbrev GroupAlgebraCenter (k G : Type*) [CommSemiring k] [Monoid G] :=
  Subalgebra.center k k[G]

namespace GroupAlgebraCenter

/-- Coefficients of a central group algebra element are constant on
conjugacy classes. -/
theorem coeff_conjugate (z : GroupAlgebraCenter k G) (g x : G) :
    (z : k[G]).coeff (g * x * g⁻¹) = (z : k[G]).coeff x := by
  have hcoeff := congrArg (fun a : k[G] ↦ a.coeff (g * x))
    (Subalgebra.mem_center_iff.mp z.property
      (MonoidAlgebra.single g 1)).symm
  simpa only [MonoidAlgebra.coeff_mul_single_apply,
    MonoidAlgebra.coeff_single_mul_apply, mul_one, one_mul, mul_assoc,
    inv_mul_cancel_left] using hcoeff

end GroupAlgebraCenter

/-- Restrict a group algebra element to the coefficients indexed by `H`.

This is coefficient restriction, not the algebra map induced by the subgroup
inclusion in the opposite direction.  In particular it is only linear. -/
def coeffRestrict (H : Subgroup G) : k[G] →ₗ[k] k[H] :=
  ((MonoidAlgebra.coeffLinearEquiv k :
      k[H] ≃ₗ[k] (H →₀ k)).symm.toLinearMap).comp
    ((Finsupp.lcomapDomain (R := k) (M := k)
      (fun h : H ↦ (h : G)) Subtype.val_injective).comp
        (MonoidAlgebra.coeffLinearEquiv k :
          k[G] ≃ₗ[k] (G →₀ k)).toLinearMap)

/-- Coefficient restriction really evaluates the original coefficient at the
underlying element of `G`. -/
@[simp]
theorem coeffRestrict_apply (H : Subgroup G) (x : k[G]) (h : H) :
    (coeffRestrict H x).coeff h = x.coeff (h : G) :=
  rfl

/-- Restricting the coefficients of the identity to a subgroup algebra gives
the identity. -/
@[simp]
theorem coeffRestrict_one (H : Subgroup G) :
    coeffRestrict H (1 : k[G]) = 1 := by
  ext h
  by_cases hh : h = 1
  · subst h
    simp [coeffRestrict_apply, MonoidAlgebra.one_def]
  · have hcoe : (h : G) ≠ 1 := by
      intro heq
      apply hh
      apply Subtype.ext
      exact heq
    simp [coeffRestrict_apply, MonoidAlgebra.one_def, hh, hcoe]

/-- The substantive algebraic step: restricting the coefficients of a
central element of `k[G]` gives a central element of `k[H]`.

No finiteness hypothesis is needed.  Centrality is checked on arbitrary
single terms and then extended to all of `k[H]` by additive induction. -/
theorem coeffRestrict_mem_center (H : Subgroup G) {z : k[G]}
    (hz : z ∈ GroupAlgebraCenter k G) :
    coeffRestrict H z ∈ GroupAlgebraCenter k H := by
  rw [Subalgebra.mem_center_iff]
  intro y
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
    simp only [add_mul, mul_add, ha, hb]
  | single h r =>
    ext x
    have hcoeff := congrArg (fun a : k[G] ↦ a.coeff (x : G))
      (Subalgebra.mem_center_iff.mp hz
        (MonoidAlgebra.single (h : G) r))
    simpa only [MonoidAlgebra.coeff_single_mul_apply,
      MonoidAlgebra.coeff_mul_single_apply, coeffRestrict_apply,
      Subgroup.coe_inv, Subgroup.coe_mul] using hcoeff

/-- Coefficient restriction on the centres of the two group algebras.

The codomain restriction is justified by `coeffRestrict_mem_center`; the map
remains linear because coefficient restriction need not preserve products. -/
def centerCoeffRestrict (H : Subgroup G) :
    GroupAlgebraCenter k G →ₗ[k] GroupAlgebraCenter k H where
  toFun z := ⟨coeffRestrict H (z : k[G]),
    coeffRestrict_mem_center H z.property⟩
  map_add' x y := by
    apply Subtype.ext
    exact (coeffRestrict H).map_add (x : k[G]) (y : k[G])
  map_smul' r x := by
    apply Subtype.ext
    exact (coeffRestrict H).map_smul r (x : k[G])

/-- The underlying subgroup-algebra element of `centerCoeffRestrict` is the
coefficient restriction defined above. -/
@[simp]
theorem centerCoeffRestrict_coe (H : Subgroup G)
    (z : GroupAlgebraCenter k G) :
    ((centerCoeffRestrict H z : GroupAlgebraCenter k H) : k[H]) =
      coeffRestrict H (z : k[G]) :=
  rfl

/-- Coefficient restriction between group algebra centres preserves one. -/
@[simp]
theorem centerCoeffRestrict_one (H : Subgroup G) :
    centerCoeffRestrict H (1 : GroupAlgebraCenter k G) = 1 := by
  apply Subtype.ext
  exact coeffRestrict_one H

/-- The central function on `Z(k[G])` induced from a supplied central
character on `Z(k[H])` by coefficient restriction.

Although `lambda` is an algebra homomorphism on the subgroup centre, the
result is deliberately a linear map: multiplicativity of this composite is
exactly the extra condition needed in the block-induction definition. -/
def inducedCentralFunction (H : Subgroup G)
    (lambda : GroupAlgebraCenter k H →ₐ[k] k) :
    GroupAlgebraCenter k G →ₗ[k] k :=
  lambda.toLinearMap.comp (centerCoeffRestrict H)

/-- Evaluation of the induced central function is evaluation of `lambda` on
the coefficient-restricted central element. -/
@[simp]
theorem inducedCentralFunction_apply (H : Subgroup G)
    (lambda : GroupAlgebraCenter k H →ₐ[k] k)
    (z : GroupAlgebraCenter k G) :
    inducedCentralFunction H lambda z = lambda (centerCoeffRestrict H z) :=
  rfl

end

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
