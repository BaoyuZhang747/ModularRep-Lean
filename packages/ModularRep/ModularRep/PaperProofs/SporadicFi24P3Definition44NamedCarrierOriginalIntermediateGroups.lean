import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQOneIntermediateBlocks

/-! The original-group top interval has local intersection equal to the
actual local group, without assuming that group is the whole ambient. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalIntermediateGroups

open SporadicFi24P3Definition44NamedCarrierQOneIntermediateBlocks

universe u
variable {G : Type u} [Group G]

def topIntersectionEquiv (D : Subgroup G) :
    localIntersection D (⊤ : Subgroup G) ≃* D where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, Subgroup.mem_top _⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem topIntersectionEquiv_toMonoidHom (D : Subgroup G) :
    (topIntersectionEquiv D).toMonoidHom = localInclusion D (⊤ : Subgroup G) := by
  ext x
  rfl

theorem topIntersection_square (D : Subgroup G) :
    (Subgroup.topEquiv.symm : G ≃* (⊤ : Subgroup G)).toMonoidHom.comp D.subtype =
      (localIntersection D (⊤ : Subgroup G)).subtype.comp
        (topIntersectionEquiv D).symm.toMonoidHom := by
  ext x
  rfl

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalIntermediateGroups


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
