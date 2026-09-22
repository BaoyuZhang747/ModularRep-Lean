import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Fixed field factors in an actual semidirect product

A subgroup containing the canonical field factor splits into its intersections
with the two canonical factors. Applied to an already defined action, pointwise
field fixation therefore gives the literal stabilizer product. No second action,
representation theoretic source, or coefficient field hypothesis is introduced.

The action lemmas concern the point supplied by the consumer. For weight classes
they do not assert fixation or factorization of a chosen raw representative.
-/

open scoped Pointwise

namespace ModularRep.PaperProofs.TypeBSemidirectFixedFieldFactorization

variable {H E : Type*} [Group H] [Group E] (field : E →* MulAut H)

/-- Containment of the field factor makes membership depend on the canonical
left factor. This uses the order `inl h * inr e`. -/
theorem mem_iff_inl_mem_of_inr_le (I : Subgroup (H ⋊[field] E))
    (field_le : (SemidirectProduct.inr (φ := field)).range ≤ I)
    (a : H ⋊[field] E) :
    a ∈ I ↔ SemidirectProduct.inl (φ := field) a.left ∈ I := by
  have right_mem : SemidirectProduct.inr (φ := field) a.right ∈ I :=
    field_le ⟨a.right, rfl⟩
  constructor
  · intro ha
    have product_mem :
        SemidirectProduct.inl (φ := field) a.left *
          SemidirectProduct.inr (φ := field) a.right ∈ I :=
      (SemidirectProduct.inl_left_mul_inr_right a).symm ▸ ha
    have cancelled := I.mul_mem product_mem (I.inv_mem right_mem)
    simpa only [mul_inv_cancel_right] using cancelled
  · intro left_mem
    exact SemidirectProduct.inl_left_mul_inr_right a ▸ I.mul_mem left_mem right_mem

/-- The exact set product of the two intersections, inside the SAME ambient
semidirect product. No normality or commutativity hypothesis is needed. -/
theorem subgroup_eq_product_of_inr_le (I : Subgroup (H ⋊[field] E))
    (field_le : (SemidirectProduct.inr (φ := field)).range ≤ I) :
    (I : Set (H ⋊[field] E)) =
      ((I ⊓ (SemidirectProduct.inl (φ := field)).range) : Set (H ⋊[field] E)) *
        ((I ⊓ (SemidirectProduct.inr (φ := field)).range) : Set (H ⋊[field] E)) := by
  apply Set.Subset.antisymm
  · intro a ha
    refine ⟨SemidirectProduct.inl (φ := field) a.left,
      ⟨(mem_iff_inl_mem_of_inr_le field I field_le a).mp ha, ⟨a.left, rfl⟩⟩,
      SemidirectProduct.inr (φ := field) a.right,
      ⟨field_le ⟨a.right, rfl⟩, ⟨a.right, rfl⟩⟩, ?_⟩
    exact SemidirectProduct.inl_left_mul_inr_right a
  · rintro _ ⟨x, hx, y, hy, rfl⟩
    exact I.mul_mem hx.1 hy.1

/-- Two subgroups containing the field factor agree once their restrictions to
the SAME canonical left factor agree. -/
theorem subgroup_eq_of_inl_comap_eq_of_inr_le
    (I J : Subgroup (H ⋊[field] E))
    (field_le_I : (SemidirectProduct.inr (φ := field)).range ≤ I)
    (field_le_J : (SemidirectProduct.inr (φ := field)).range ≤ J)
    (left_eq : I.comap (SemidirectProduct.inl (φ := field)) =
      J.comap (SemidirectProduct.inl (φ := field))) : I = J := by
  ext a
  rw [mem_iff_inl_mem_of_inr_le field I field_le_I a,
    mem_iff_inl_mem_of_inr_le field J field_le_J a]
  change a.left ∈ I.comap (SemidirectProduct.inl (φ := field)) ↔
    a.left ∈ J.comap (SemidirectProduct.inl (φ := field))
  rw [left_eq]

section Actions

variable {X Y : Type*} [MulAction (H ⋊[field] E) X] [MulAction (H ⋊[field] E) Y]

/-- Fixation under the actual canonical field inclusion gives its containment
in the actual action stabilizer. -/
theorem inr_range_le_stabilizer (x : X)
    (fixed : ∀ e : E, SemidirectProduct.inr (φ := field) e • x = x) :
    (SemidirectProduct.inr (φ := field)).range ≤
      MulAction.stabilizer (H ⋊[field] E) x := by
  rintro _ ⟨e, rfl⟩
  exact fixed e

/-- Pointwise field fixation detects full ambient inertia on the left factor. -/
theorem mem_stabilizer_iff_inl_smul_of_inr_fixed (x : X)
    (fixed : ∀ e : E, SemidirectProduct.inr (φ := field) e • x = x)
    (a : H ⋊[field] E) :
    a ∈ MulAction.stabilizer (H ⋊[field] E) x ↔
      SemidirectProduct.inl (φ := field) a.left • x = x :=
  mem_iff_inl_mem_of_inr_le field (MulAction.stabilizer (H ⋊[field] E) x)
    (inr_range_le_stabilizer field x fixed) a

/-- The literal stabilizer product for the existing action and the given point. -/
theorem stabilizer_eq_product_of_inr_fixed (x : X)
    (fixed : ∀ e : E, SemidirectProduct.inr (φ := field) e • x = x) :
    (MulAction.stabilizer (H ⋊[field] E) x : Set (H ⋊[field] E)) =
      ((MulAction.stabilizer (H ⋊[field] E) x ⊓
        (SemidirectProduct.inl (φ := field)).range) : Set (H ⋊[field] E)) *
      ((MulAction.stabilizer (H ⋊[field] E) x ⊓
        (SemidirectProduct.inr (φ := field)).range) : Set (H ⋊[field] E)) :=
  subgroup_eq_product_of_inr_le field (MulAction.stabilizer (H ⋊[field] E) x)
    (inr_range_le_stabilizer field x fixed)

/-- Matched left-factor stabilizers lift to matched full ambient stabilizers
when the actual field inclusion fixes both points. -/
theorem stabilizer_eq_of_inl_comap_eq_of_inr_fixed (x : X) (y : Y)
    (fixedX : ∀ e : E, SemidirectProduct.inr (φ := field) e • x = x)
    (fixedY : ∀ e : E, SemidirectProduct.inr (φ := field) e • y = y)
    (left_eq : (MulAction.stabilizer (H ⋊[field] E) x).comap
        (SemidirectProduct.inl (φ := field)) =
      (MulAction.stabilizer (H ⋊[field] E) y).comap
        (SemidirectProduct.inl (φ := field))) :
    MulAction.stabilizer (H ⋊[field] E) x =
      MulAction.stabilizer (H ⋊[field] E) y :=
  subgroup_eq_of_inl_comap_eq_of_inr_le field _ _
    (inr_range_le_stabilizer field x fixedX)
    (inr_range_le_stabilizer field y fixedY) left_eq

/-- Equivariance for the two canonical inclusions proves equivariance for the
SAME function under the existing ambient actions. -/
theorem equivariant_of_inl_of_inr (f : X → Y)
    (left : ∀ (h : H) (x : X),
      f (SemidirectProduct.inl (φ := field) h • x) =
        SemidirectProduct.inl (φ := field) h • f x)
    (right : ∀ (e : E) (x : X),
      f (SemidirectProduct.inr (φ := field) e • x) =
        SemidirectProduct.inr (φ := field) e • f x)
    (a : H ⋊[field] E) (x : X) : f (a • x) = a • f x := by
  calc
    f (a • x) = f (SemidirectProduct.inl (φ := field) a.left •
        (SemidirectProduct.inr (φ := field) a.right • x)) := by
      rw [← mul_smul, SemidirectProduct.inl_left_mul_inr_right]
    _ = SemidirectProduct.inl (φ := field) a.left •
        (SemidirectProduct.inr (φ := field) a.right • f x) := by rw [left, right]
    _ = a • f x := by rw [← mul_smul, SemidirectProduct.inl_left_mul_inr_right]

/-- With pointwise field fixation on both full carriers, only the left-factor
square remains. This preserves the supplied function without making a new choice. -/
theorem equivariant_of_inl_of_inr_fixed (f : X → Y)
    (left : ∀ (h : H) (x : X),
      f (SemidirectProduct.inl (φ := field) h • x) =
        SemidirectProduct.inl (φ := field) h • f x)
    (fixedX : ∀ (e : E) (x : X), SemidirectProduct.inr (φ := field) e • x = x)
    (fixedY : ∀ (e : E) (y : Y), SemidirectProduct.inr (φ := field) e • y = y)
    (a : H ⋊[field] E) (x : X) : f (a • x) = a • f x := by
  apply equivariant_of_inl_of_inr field f left _ a x
  intro e z
  rw [fixedX, fixedY]

end Actions

end ModularRep.PaperProofs.TypeBSemidirectFixedFieldFactorization


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
