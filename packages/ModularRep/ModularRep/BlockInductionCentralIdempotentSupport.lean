import ModularRep.BlockInduction
import ModularRep.CentralIdempotentBlockExpansion

/-!
# Central idempotent support under block induction

This module proves the elementary support calculation behind preservation of a
central prime-to-p character by block induction. It uses literal coefficient
restriction in the existing definition, not a premise asserting the desired
sector equality. Applying it to standard central character idempotents and
deriving the ordinary character formula for lying over require further results.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep

namespace BlockCentralCharacterCatalogue

variable {k G Block : Type*}
variable [Field k] [IsAlgClosed k] [Group G] [Fintype G] [Fintype Block]
variable {blockIdempotent : Block → k[G]}
variable {blocks : BlockIdempotentDecomposition blockIdempotent}

/-- A central idempotent is supported at a block precisely when that block's
central algebra character takes value one on it. This uses primitivity and
the existing catalogue delta law, not a scalar identity in the whole block
algebra. -/
theorem centralIdempotent_value_one_iff
    (catalogue : BlockCentralCharacterCatalogue blocks)
    (b : Block) (e : GroupAlgebraCenter k G)
    (he : IsIdempotentElem (e : k[G])) :
    catalogue.centralCharacter b e = 1 ↔
      blockIdempotent b * (e : k[G]) = blockIdempotent b := by
  have heCentral : IsMulCentral (e : k[G]) :=
    Set.mem_center_iff.mp
      (Semigroup.mem_center_iff.mpr (Subalgebra.mem_center_iff.mp e.property))
  constructor
  · intro hvalue
    rcases (blocks.primitive b).mul_eq_zero_or_eq_self_of_central_idempotent
      he heCentral with hzero | hself
    · have hzeroCenter : blocks.blockIdempotentInCenter b * e = 0 := by
        apply Subtype.ext
        exact hzero
      have hbad := congrArg (catalogue.centralCharacter b) hzeroCenter
      have : (1 : k) = 0 := by
        simpa only [map_mul, map_zero, catalogue.centralCharacter_own,
          hvalue, one_mul] using hbad
      exact (one_ne_zero this).elim
    · exact hself
  · intro hself
    have hselfCenter : blocks.blockIdempotentInCenter b * e =
        blocks.blockIdempotentInCenter b := by
      apply Subtype.ext
      exact hself
    have hvalue := congrArg (catalogue.centralCharacter b) hselfCenter
    simpa only [map_mul, catalogue.centralCharacter_own, one_mul] using hvalue

end BlockCentralCharacterCatalogue

section Restriction

variable {k G LocalBlock AmbientBlock : Type*}
variable [Field k] [IsAlgClosed k] [Group G] [Fintype G]
variable [Fintype LocalBlock] [Fintype AmbientBlock]
variable (H : Subgroup G)
local instance subgroupFintype : Fintype H := Fintype.ofFinite H
variable {localIdempotent : LocalBlock → k[H]}
variable {ambientIdempotent : AmbientBlock → k[G]}
variable {localBlocks : BlockIdempotentDecomposition localIdempotent}
variable {ambientBlocks : BlockIdempotentDecomposition ambientIdempotent}
variable (localCatalogue : BlockCentralCharacterCatalogue localBlocks)
variable (ambientCatalogue : BlockCentralCharacterCatalogue ambientBlocks)

/-- If coefficient restriction carries a specified central idempotent to a
central idempotent, block induction preserves its support. For the intended
application, the idempotent is the one attached to a central prime-to-p
character and its support lies in H. -/
theorem blockInducesTo_preserves_centralIdempotentSupport
    {b : LocalBlock} {B : AmbientBlock}
    (hinduces : BlockInducesTo H localCatalogue ambientCatalogue b B)
    (e : GroupAlgebraCenter k G)
    (he : IsIdempotentElem (e : k[G]))
    (heLocal : IsIdempotentElem
      ((centerCoeffRestrict H e : GroupAlgebraCenter k H) : k[H]))
    (hB : ambientIdempotent B * (e : k[G]) = ambientIdempotent B) :
    localIdempotent b *
        ((centerCoeffRestrict H e : GroupAlgebraCenter k H) : k[H]) =
      localIdempotent b := by
  obtain ⟨hdefined, hcharacter⟩ := hinduces
  have hvalueG : ambientCatalogue.centralCharacter B e = 1 :=
    (ambientCatalogue.centralIdempotent_value_one_iff B e he).mpr hB
  have hvalueH : localCatalogue.centralCharacter b (centerCoeffRestrict H e) = 1 := by
    calc
      localCatalogue.centralCharacter b (centerCoeffRestrict H e) =
          inducedCentralCharacter H (localCatalogue.centralCharacter b) hdefined e := rfl
      _ = ambientCatalogue.centralCharacter B e :=
        congrArg (fun f : GroupAlgebraCenter k G →ₐ[k] k ↦ f e) hcharacter
      _ = 1 := hvalueG
  exact (localCatalogue.centralIdempotent_value_one_iff
    b (centerCoeffRestrict H e) heLocal).mp hvalueH

end Restriction

end ModularRep



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
