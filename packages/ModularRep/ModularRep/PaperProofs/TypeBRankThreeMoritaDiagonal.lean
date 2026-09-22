import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.Group.Opposite
import Mathlib.Data.Finite.Prod

/-!
# The split diagonal for the same two field actions

The right component is an opposite group. The defining equation therefore
uses the inverse of its underlying field coordinate. The field generator is
the pair of the first field element and the opposite of its inverse on the
second side. These constructions require no commutativity of the field group.

This is generic group infrastructure for the induced Morita construction.
No representation, tensor functor, block or equivalence theorem is an input.
-/

set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRankThreeMoritaDiagonal

open MulOpposite

variable {G L Q : Type*} [Group G] [Group L] [Group Q]
variable (aG : Q →* MulAut G) (aL : Q →* MulAut L)

/-- The literal inverse-coordinate diagonal in the two split overgroups. -/
def D : Subgroup ((G ⋊[aG] Q) × (L ⋊[aL] Q)ᵐᵒᵖ) where
  carrier := {x | SemidirectProduct.rightHom x.1 =
    (SemidirectProduct.rightHom (unop x.2))⁻¹}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    change SemidirectProduct.rightHom (x.1 * y.1) =
      (SemidirectProduct.rightHom (unop (x.2 * y.2)))⁻¹
    simpa only [unop_mul, map_mul, mul_inv_rev] using congrArg₂ (· * ·) hx hy
  inv_mem' := by
    intro x hx
    change SemidirectProduct.rightHom x.1⁻¹ =
      (SemidirectProduct.rightHom (unop x.2⁻¹))⁻¹
    simpa only [unop_inv, map_inv] using congrArg Inv.inv hx

@[simp] theorem mem_D (x : (G ⋊[aG] Q) × (L ⋊[aL] Q)ᵐᵒᵖ) :
    x ∈ D aG aL ↔ SemidirectProduct.rightHom x.1 =
      (SemidirectProduct.rightHom (unop x.2))⁻¹ := Iff.rfl

theorem right_eq (x : D aG aL) :
    x.val.1.right = (unop x.val.2).right⁻¹ := x.property

theorem right_unop_eq (x : D aG aL) :
    (unop x.val.2).right = x.val.1.right⁻¹ := by
  simpa only [inv_inv] using (congrArg Inv.inv (right_eq aG aL x)).symm

/-- The unchanged base pair, using the opposite group on the right. -/
def baseEmbedding : G × Lᵐᵒᵖ →* D aG aL where
  toFun x := ⟨(SemidirectProduct.inl x.1,
    op (SemidirectProduct.inl (unop x.2))), by simp⟩
  map_one' := by
    apply Subtype.ext
    apply Prod.ext <;> simp
  map_mul' x y := by
    apply Subtype.ext
    apply Prod.ext
    · exact map_mul SemidirectProduct.inl x.1 y.1
    · apply unop_injective
      change (SemidirectProduct.inl (unop y.2 * unop x.2) : L ⋊[aL] Q) =
        SemidirectProduct.inl (unop y.2) * SemidirectProduct.inl (unop x.2)
      exact map_mul SemidirectProduct.inl (unop y.2) (unop x.2)

@[simp] theorem baseEmbedding_val (x : G × Lᵐᵒᵖ) :
    (baseEmbedding aG aL x).val =
      (SemidirectProduct.inl x.1, op (SemidirectProduct.inl (unop x.2))) := rfl

@[simp] theorem baseEmbedding_pair (g : G) (l : L) :
    (baseEmbedding aG aL (g, op l)).val =
      (SemidirectProduct.inl g, op (SemidirectProduct.inl l)) := rfl

theorem baseEmbedding_injective : Function.Injective (baseEmbedding aG aL) := by
  intro x y h
  apply Prod.ext
  · exact SemidirectProduct.inl_injective
      (congrArg (fun z : D aG aL => z.val.1) h)
  · apply unop_injective
    exact SemidirectProduct.inl_injective
      (congrArg (fun z : D aG aL => unop z.val.2) h)

/-- The diagonal field generator has the inverse in the opposite factor. -/
def fieldEmbedding : Q →* D aG aL where
  toFun q := ⟨(SemidirectProduct.inr q,
    op (SemidirectProduct.inr q⁻¹)), by simp⟩
  map_one' := by
    apply Subtype.ext
    apply Prod.ext <;> simp
  map_mul' q r := by
    apply Subtype.ext
    apply Prod.ext
    · exact map_mul SemidirectProduct.inr q r
    · apply unop_injective
      change (SemidirectProduct.inr (q * r)⁻¹ : L ⋊[aL] Q) =
        SemidirectProduct.inr r⁻¹ * SemidirectProduct.inr q⁻¹
      simp only [mul_inv_rev, map_mul]

@[simp] theorem fieldEmbedding_val (q : Q) :
    (fieldEmbedding aG aL q).val =
      (SemidirectProduct.inr q, op (SemidirectProduct.inr q⁻¹)) := rfl

/-- The first field coordinate, with the second coordinate fixed by membership. -/
def fieldProjection : D aG aL →* Q where
  toFun x := SemidirectProduct.rightHom x.val.1
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem fieldProjection_base (x : G × Lᵐᵒᵖ) :
    fieldProjection aG aL (baseEmbedding aG aL x) = 1 := rfl

@[simp] theorem fieldProjection_field (q : Q) :
    fieldProjection aG aL (fieldEmbedding aG aL q) = q := rfl

theorem fieldEmbedding_injective : Function.Injective (fieldEmbedding aG aL) := by
  intro q r h
  exact congrArg (fieldProjection aG aL) h

theorem fieldProjection_surjective : Function.Surjective (fieldProjection aG aL) := by
  intro q
  exact ⟨fieldEmbedding aG aL q, rfl⟩

/-- The componentwise action uses the same automorphism on the right base group. -/
def baseAction : Q →* MulAut (G × Lᵐᵒᵖ) where
  toFun q :=
    { toFun := fun x => (aG q x.1, op (aL q (unop x.2)))
      invFun := fun x => ((aG q).symm x.1, op ((aL q).symm (unop x.2)))
      left_inv := by intro x; apply Prod.ext <;> simp
      right_inv := by intro x; apply Prod.ext <;> simp
      map_mul' := by
        intro x y
        apply Prod.ext
        · exact map_mul (aG q) x.1 y.1
        · apply unop_injective
          change aL q (unop y.2 * unop x.2) =
            aL q (unop y.2) * aL q (unop x.2)
          exact map_mul (aL q) (unop y.2) (unop x.2) }
  map_one' := by
    apply MulEquiv.ext
    intro x
    apply Prod.ext <;> simp
  map_mul' q r := by
    apply MulEquiv.ext
    intro x
    apply Prod.ext <;> simp [MulAut.mul_apply]

@[simp] theorem baseAction_apply (q : Q) (x : G × Lᵐᵒᵖ) :
    baseAction aG aL q x = (aG q x.1, op (aL q (unop x.2))) := rfl

/-- Conjugation by the signed diagonal field element is the same base action. -/
theorem baseEmbedding_action (q : Q) (x : G × Lᵐᵒᵖ) :
    baseEmbedding aG aL (baseAction aG aL q x) =
      fieldEmbedding aG aL q * baseEmbedding aG aL x * fieldEmbedding aG aL q⁻¹ := by
  apply Subtype.ext
  apply Prod.ext
  · exact SemidirectProduct.inl_aut q x.1
  · apply unop_injective
    change (SemidirectProduct.inl (aL q (unop x.2)) : L ⋊[aL] Q) =
      SemidirectProduct.inr (q⁻¹)⁻¹ *
        (SemidirectProduct.inl (unop x.2) * SemidirectProduct.inr q⁻¹)
    simpa only [inv_inv, mul_assoc] using
      (SemidirectProduct.inl_aut (φ := aL) q (unop x.2))

/-- The canonical hom from the honest simultaneous-action semidirect product. -/
def splitHom : (G × Lᵐᵒᵖ) ⋊[baseAction aG aL] Q →* D aG aL :=
  SemidirectProduct.lift (baseEmbedding aG aL) (fieldEmbedding aG aL)
    (fun q => by
      apply MonoidHom.ext
      intro x
      simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, map_inv] using baseEmbedding_action aG aL q x)

@[simp] theorem splitHom_inl (x : G × Lᵐᵒᵖ) :
    splitHom aG aL (SemidirectProduct.inl x) = baseEmbedding aG aL x := by
  exact SemidirectProduct.lift_inl _ _ _ x

@[simp] theorem splitHom_inr (q : Q) :
    splitHom aG aL (SemidirectProduct.inr q) = fieldEmbedding aG aL q := by
  exact SemidirectProduct.lift_inr _ _ _ q

theorem splitHom_val (x : (G × Lᵐᵒᵖ) ⋊[baseAction aG aL] Q) :
    (splitHom aG aL x).val =
      (SemidirectProduct.inl x.left.1 * SemidirectProduct.inr x.right,
       op (SemidirectProduct.inr x.right⁻¹ * SemidirectProduct.inl (unop x.left.2))) := rfl

/-- Finiteness is needed only here, and is inherited from the three actual groups. -/
instance finiteD [Finite G] [Finite L] [Finite Q] : Finite (D aG aL) := by
  letI : Finite (G ⋊[aG] Q) :=
    Finite.of_equiv (G × Q) SemidirectProduct.equivProd.symm
  letI : Finite (L ⋊[aL] Q) :=
    Finite.of_equiv (L × Q) SemidirectProduct.equivProd.symm
  letI : Finite (L ⋊[aL] Q)ᵐᵒᵖ :=
    Finite.of_equiv (L ⋊[aL] Q) MulOpposite.opEquiv
  infer_instance

end ModularRep.PaperProofs.TypeBRankThreeMoritaDiagonal


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
