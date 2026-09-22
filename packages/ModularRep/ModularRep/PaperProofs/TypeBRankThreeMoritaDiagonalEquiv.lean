import ModularRep.PaperProofs.TypeBRankThreeMoritaDiagonal

/-!
# Explicit coordinates for the split diagonal

The inverse reads the common field coordinate from the first factor. Its
right base coordinate is corrected by that same field automorphism. This
gives a literal inverse hom for restriction of an honest representation to
the diagonal, with the same base and field generators.
-/

set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRankThreeMoritaDiagonalEquiv

open MulOpposite TypeBRankThreeMoritaDiagonal

variable {G L Q : Type*} [Group G] [Group L] [Group Q]
variable (aG : Q →* MulAut G) (aL : Q →* MulAut L)

theorem splitHom_first_left (x : (G × Lᵐᵒᵖ) ⋊[baseAction aG aL] Q) :
    (splitHom aG aL x).val.1.left = x.left.1 := by
  simpa using congrArg
    (fun y : (G ⋊[aG] Q) × (L ⋊[aL] Q)ᵐᵒᵖ => y.1.left)
    (splitHom_val aG aL x)

theorem splitHom_first_right (x : (G × Lᵐᵒᵖ) ⋊[baseAction aG aL] Q) :
    (splitHom aG aL x).val.1.right = x.right := by
  simpa using congrArg
    (fun y : (G ⋊[aG] Q) × (L ⋊[aL] Q)ᵐᵒᵖ => y.1.right)
    (splitHom_val aG aL x)

theorem splitHom_second_left (x : (G × Lᵐᵒᵖ) ⋊[baseAction aG aL] Q) :
    (unop (splitHom aG aL x).val.2).left =
      aL x.right⁻¹ (unop x.left.2) := by
  simpa using congrArg
    (fun y : (G ⋊[aG] Q) × (L ⋊[aL] Q)ᵐᵒᵖ => (unop y.2).left)
    (splitHom_val aG aL x)

theorem splitHom_second_right (x : (G × Lᵐᵒᵖ) ⋊[baseAction aG aL] Q) :
    (unop (splitHom aG aL x).val.2).right = x.right⁻¹ := by
  simpa using congrArg
    (fun y : (G ⋊[aG] Q) × (L ⋊[aL] Q)ᵐᵒᵖ => (unop y.2).right)
    (splitHom_val aG aL x)

/-- Correct the right base coordinate by the first factor's field coordinate. -/
def coordinateInverse (d : D aG aL) :
    (G × Lᵐᵒᵖ) ⋊[baseAction aG aL] Q :=
  ⟨(d.val.1.left, op (aL d.val.1.right (unop d.val.2).left)), d.val.1.right⟩

theorem coordinateInverse_splitHom
    (x : (G × Lᵐᵒᵖ) ⋊[baseAction aG aL] Q) :
    coordinateInverse aG aL (splitHom aG aL x) = x := by
  apply SemidirectProduct.ext
  · apply Prod.ext
    · exact splitHom_first_left aG aL x
    · apply unop_injective
      change aL (splitHom aG aL x).val.1.right
        (unop (splitHom aG aL x).val.2).left = unop x.left.2
      rw [splitHom_first_right, splitHom_second_left]
      simp only [map_inv, MulAut.apply_inv_self]
  · exact splitHom_first_right aG aL x

theorem splitHom_coordinateInverse (d : D aG aL) :
    splitHom aG aL (coordinateInverse aG aL d) = d := by
  apply Subtype.ext
  apply Prod.ext
  · apply SemidirectProduct.ext
    · rw [splitHom_first_left]
      rfl
    · rw [splitHom_first_right]
      rfl
  · apply unop_injective
    apply SemidirectProduct.ext
    · rw [splitHom_second_left]
      change aL d.val.1.right⁻¹ (aL d.val.1.right (unop d.val.2).left) =
        (unop d.val.2).left
      simp only [map_inv, MulAut.inv_apply_self]
    · rw [splitHom_second_right]
      exact (right_unop_eq aG aL d).symm

/-- The forward map is the previously constructed hom, with its explicit inverse. -/
def splitEquiv : (G × Lᵐᵒᵖ) ⋊[baseAction aG aL] Q ≃* D aG aL where
  toFun := splitHom aG aL
  invFun := coordinateInverse aG aL
  left_inv := coordinateInverse_splitHom aG aL
  right_inv := splitHom_coordinateInverse aG aL
  map_mul' := map_mul (splitHom aG aL)

@[simp] theorem splitEquiv_apply
    (x : (G × Lᵐᵒᵖ) ⋊[baseAction aG aL] Q) :
    splitEquiv aG aL x = splitHom aG aL x := rfl

@[simp] theorem splitEquiv_symm_apply (d : D aG aL) :
    (splitEquiv aG aL).symm d = coordinateInverse aG aL d := rfl

/-- Pull an honest semidirect representation back along this actual hom. -/
def inverseHom : D aG aL →* (G × Lᵐᵒᵖ) ⋊[baseAction aG aL] Q :=
  (splitEquiv aG aL).symm.toMonoidHom

@[simp] theorem inverseHom_apply (d : D aG aL) :
    inverseHom aG aL d = coordinateInverse aG aL d := rfl

@[simp] theorem inverseHom_base (x : G × Lᵐᵒᵖ) :
    inverseHom aG aL (baseEmbedding aG aL x) = SemidirectProduct.inl x := by
  apply (splitEquiv aG aL).injective
  change splitEquiv aG aL ((splitEquiv aG aL).symm (baseEmbedding aG aL x)) =
    splitEquiv aG aL (SemidirectProduct.inl x)
  rw [MulEquiv.apply_symm_apply, splitEquiv_apply, splitHom_inl]

@[simp] theorem inverseHom_field (q : Q) :
    inverseHom aG aL (fieldEmbedding aG aL q) = SemidirectProduct.inr q := by
  apply (splitEquiv aG aL).injective
  change splitEquiv aG aL ((splitEquiv aG aL).symm (fieldEmbedding aG aL q)) =
    splitEquiv aG aL (SemidirectProduct.inr q)
  rw [MulEquiv.apply_symm_apply, splitEquiv_apply, splitHom_inr]

theorem inverseHom_comp_base :
    (inverseHom aG aL).comp (baseEmbedding aG aL) =
      (SemidirectProduct.inl : G × Lᵐᵒᵖ →* (G × Lᵐᵒᵖ) ⋊[baseAction aG aL] Q) := by
  apply MonoidHom.ext
  exact inverseHom_base aG aL

theorem inverseHom_comp_field :
    (inverseHom aG aL).comp (fieldEmbedding aG aL) =
      (SemidirectProduct.inr : Q →* (G × Lᵐᵒᵖ) ⋊[baseAction aG aL] Q) := by
  apply MonoidHom.ext
  exact inverseHom_field aG aL

end ModularRep.PaperProofs.TypeBRankThreeMoritaDiagonalEquiv


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
