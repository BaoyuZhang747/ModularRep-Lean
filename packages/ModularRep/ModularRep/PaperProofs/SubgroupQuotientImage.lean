import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The image of a subgroup in a quotient

This module contains the elementary group-theoretic map from a subgroup to
its image in a quotient.  It is independent of the representation and
character-extension modules that use it.
-/

namespace ModularRep.PaperProofs.EvenFieldFLZ318SelfCover

universe u

variable {D : Type u} [Group D]
variable (Q N : Subgroup D) [Q.Normal]

/-- The image of a subgroup `N` in the quotient `D / Q`. -/
abbrev QuotientImage : Subgroup (D ⧸ Q) :=
  N.map (QuotientGroup.mk' Q)

/-- The quotient map restricted to `N`, with codomain its image. -/
def subgroupToQuotientImage : N →* QuotientImage Q N where
  toFun := fun n ↦
    ⟨QuotientGroup.mk' Q n.1,
      Subgroup.mem_map_of_mem (QuotientGroup.mk' Q) n.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' := fun a b ↦ by
    apply Subtype.ext
    simp

@[simp]
theorem subgroupToQuotientImage_coe (n : N) :
    ((subgroupToQuotientImage Q N n : QuotientImage Q N) : D ⧸ Q) =
      QuotientGroup.mk' Q n.1 :=
  rfl

end ModularRep.PaperProofs.EvenFieldFLZ318SelfCover


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
