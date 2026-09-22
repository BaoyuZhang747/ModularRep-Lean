import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.ConjFinite
import ModularRep.GroupAlgebraCentralFunctions

/-!
# Conjugacy class sums for subgroup central functions

For a finite group `G`, this file constructs the raw group algebra sum of a
conjugacy class and proves that it is central.  For `H ≤ G`, it then exposes
the coefficient restriction of that class sum in the precise unnormalised
form used in the block-induction formula:

`∑ x ∈ Cl_G(g) ∩ H, x`.

The intersection sum is written as a dependent conditional sum over
`Cl_G(g)`: a term is the corresponding basis element of `k[H]` when it lies
in `H`, and zero otherwise.  This avoids choosing representatives or an
enumeration of the intersection.  In particular, there is no class-size,
index, averaging, or `p`-regularity condition in this kernel construction.
-/

namespace ModularRep

open MonoidAlgebra
open scoped BigOperators

noncomputable section

variable {k G : Type*} [CommSemiring k] [Group G] [Fintype G]

local instance classSumsPropDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- Restricting a single group algebra basis term to `H` either retains its
coefficient at the corresponding subgroup element or gives zero. -/
theorem coeffRestrict_single (H : Subgroup G) (x : G) (r : k) :
    coeffRestrict H (MonoidAlgebra.single x r) =
      if hx : x ∈ H then MonoidAlgebra.single (⟨x, hx⟩ : H) r else 0 := by
  classical
  by_cases hx : x ∈ H
  · ext h
    by_cases hxh : x = (h : G)
    · subst x
      have hsub : (⟨(h : G), hx⟩ : H) = h := Subtype.ext rfl
      simp [coeffRestrict_apply, hsub]
    · have hsub : (⟨x, hx⟩ : H) ≠ h := by
        intro heq
        exact hxh (congrArg Subtype.val heq)
      simp [coeffRestrict_apply, hx, hxh, hsub]
  · ext h
    have hne : x ≠ (h : G) := by
      intro hEq
      apply hx
      simpa [hEq] using h.property
    simp [coeffRestrict_apply, hx, hne]

/-- The unnormalised sum of the `G`-conjugacy class of `g`, regarded as a
central element of `k[G]`. -/
noncomputable def conjugacyClassSum (g : G) : GroupAlgebraCenter k G := by
  classical
  refine ⟨∑ x : (ConjClasses.mk g).carrier,
    MonoidAlgebra.single (x : G) 1, ?_⟩
  rw [Subalgebra.mem_center_iff]
  intro y
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
    simp only [add_mul, mul_add, ha, hb]
  | single h r =>
    let e : (ConjClasses.mk g).carrier ≃ (ConjClasses.mk g).carrier :=
      { toFun := fun x => ⟨h * (x : G) * h⁻¹, by
          apply ConjClasses.mem_carrier_iff_mk_eq.mpr
          calc
            ConjClasses.mk (h * (x : G) * h⁻¹) = ConjClasses.mk (x : G) := by
              apply ConjClasses.mk_eq_mk_iff_isConj.mpr
              exact isConj_iff.mpr ⟨h⁻¹, by simp [mul_assoc]⟩
            _ = ConjClasses.mk g :=
              ConjClasses.mem_carrier_iff_mk_eq.mp x.property⟩
        invFun := fun x => ⟨h⁻¹ * (x : G) * h, by
          apply ConjClasses.mem_carrier_iff_mk_eq.mpr
          calc
            ConjClasses.mk (h⁻¹ * (x : G) * h) = ConjClasses.mk (x : G) := by
              apply ConjClasses.mk_eq_mk_iff_isConj.mpr
              exact isConj_iff.mpr ⟨h, by simp [mul_assoc]⟩
            _ = ConjClasses.mk g :=
              ConjClasses.mem_carrier_iff_mk_eq.mp x.property⟩
        left_inv := by
          intro x
          apply Subtype.ext
          simp [mul_assoc]
        right_inv := by
          intro x
          apply Subtype.ext
          simp [mul_assoc] }
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Fintype.sum_bijective e e.bijective _ _ fun x => by
      simp [e, mul_assoc]

/-- The raw subgroup-algebra sum of the elements in
`Cl_G(g) ∩ H`.  The dependent conditional is precisely the finite-sum normal
form of that intersection: terms outside `H` are zero and every retained
term is the corresponding basis element of `k[H]`. -/
noncomputable def conjugacyClassIntersectionRawSum
    (H : Subgroup G) (g : G) : k[H] := by
  classical
  exact ∑ x : (ConjClasses.mk g).carrier,
    if hx : (x : G) ∈ H then
      MonoidAlgebra.single (⟨(x : G), hx⟩ : H) 1
    else 0

/-- The conditional implementation normal form is the literal sum indexed by
the intersection `Cl_G(g) ∩ H`. -/
theorem conjugacyClassIntersectionRawSum_eq_subtypeSum
    (H : Subgroup G) (g : G) :
    conjugacyClassIntersectionRawSum (k := k) H g =
      ∑ y : {x : (ConjClasses.mk g).carrier // (x : G) ∈ H},
        MonoidAlgebra.single (⟨(y.1 : G), y.2⟩ : H) 1 := by
  classical
  unfold conjugacyClassIntersectionRawSum
  refine Finset.sum_congr_set
    {x : (ConjClasses.mk g).carrier | (x : G) ∈ H} _ _ ?_ ?_
  · intro x hx
    have hxH : (x : G) ∈ H := by simpa using hx
    simp [hxH]
  · intro x hx
    have hxH : (x : G) ∉ H := by
      intro hxH
      apply hx
      simpa using hxH
    simp [hxH]

/-- Coefficient restriction sends the raw `G`-class sum to the raw sum of
its intersection with `H`. -/
theorem coeffRestrict_conjugacyClassSum
    (H : Subgroup G) (g : G) :
    coeffRestrict H
        ((conjugacyClassSum (k := k) g : GroupAlgebraCenter k G) : k[G]) =
      conjugacyClassIntersectionRawSum (k := k) H g := by
  classical
  change coeffRestrict H
      (∑ x : (ConjClasses.mk g).carrier,
        MonoidAlgebra.single (x : G) 1) = _
  rw [map_sum]
  simp only [conjugacyClassIntersectionRawSum]
  apply Finset.sum_congr rfl
  intro x _
  exact coeffRestrict_single H (x : G) 1

/-- The central element of `k[H]` obtained by intersecting the `G`-class of
`g` with `H`.  Its centrality is inherited from coefficient restriction. -/
noncomputable def conjugacyClassIntersectionSum
    (H : Subgroup G) (g : G) : GroupAlgebraCenter k H :=
  centerCoeffRestrict H (conjugacyClassSum (k := k) g)

/-- Coercing the centred intersection sum exposes the raw,
unnormalised intersection class sum. -/
@[simp]
theorem conjugacyClassIntersectionSum_coe
    (H : Subgroup G) (g : G) :
    ((conjugacyClassIntersectionSum (k := k) H g :
        GroupAlgebraCenter k H) : k[H]) =
      ∑ y : {x : (ConjClasses.mk g).carrier // (x : G) ∈ H},
        MonoidAlgebra.single (⟨(y.1 : G), y.2⟩ : H) 1 := by
  change coeffRestrict H
      ((conjugacyClassSum (k := k) g : GroupAlgebraCenter k G) : k[G]) = _
  rw [coeffRestrict_conjugacyClassSum]
  exact conjugacyClassIntersectionRawSum_eq_subtypeSum H g

/-- Evaluation of the central function induced from `H` on a `G`-class sum.
This is the exact class-sum direction in Späth's Definition 2.1: restrict
from `G` to `H`, then evaluate the local central character. -/
theorem inducedCentralFunction_conjugacyClassSum
    (H : Subgroup G) (lambda : GroupAlgebraCenter k H →ₐ[k] k)
    (g : G) :
    inducedCentralFunction H lambda (conjugacyClassSum (k := k) g) =
      lambda (conjugacyClassIntersectionSum (k := k) H g) :=
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
