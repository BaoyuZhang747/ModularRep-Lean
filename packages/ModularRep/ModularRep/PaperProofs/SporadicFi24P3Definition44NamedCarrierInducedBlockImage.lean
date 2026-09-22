import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientBlockAlgebra

/-!
# The ambient block image from local block induction

The actual local image, two defined inductions, and the coefficient
restriction square determine the ambient specified image. Only unselected
guarded primitivity is required; nonzeroness is derived internally.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierInducedBlockImage

open ModularRep
open SporadicFi24P3Definition44NamedCarrierQuotientBlockAlgebra

universe u

variable {k G H BU BD LU LD : Type u} [Field k] [IsAlgClosed k]
  [Group G] [Group H] [Fintype G] [Fintype H]
  [Fintype BU] [Fintype BD] [Fintype LU] [Fintype LD]

variable (U : Subgroup G) (V : Subgroup H)
local instance : Fintype U := Fintype.ofFinite _
local instance : Fintype V := Fintype.ofFinite _

variable {eGU : BU → k[G]} {eHD : BD → k[H]}
  {eU : LU → k[U]} {eV : LD → k[V]}
  {dGU : BlockIdempotentDecomposition eGU} {dHD : BlockIdempotentDecomposition eHD}
  {dU : BlockIdempotentDecomposition eU} {dV : BlockIdempotentDecomposition eV}

theorem blockInducesTo_image_of_local_image
    (f : G →* H) (hf : Function.Surjective f)
    (fU : U →* V) (hfU : Function.Surjective fU)
    (square : ∀ x : U, (fU x : H) = f x)
    (saturated : ∀ g : G, g ∈ U ↔ f g ∈ V)
    (cGU : BlockCentralCharacterCatalogue dGU) (cHD : BlockCentralCharacterCatalogue dHD)
    (cU : BlockCentralCharacterCatalogue dU) (cV : BlockCentralCharacterCatalogue dV)
    (bU : LU) (bV : LD) (BU' : BU) (BD' : BD)
    (primitive : ∀ e : k[G], IsPrimitiveCentralIdempotent e →
      algebraMapOf f e ≠ 0 → IsPrimitiveCentralIdempotent (algebraMapOf f e))
    (localPhysical : algebraMapOf fU (eU bU) = eV bV)
    (upInduces : BlockInducesTo U cU cGU bU BU')
    (downInduces : BlockInducesTo V cV cHD bV BD') :
    algebraMapOf f (eGU BU') = eHD BD' := by
  obtain ⟨hup, hequp⟩ := upInduces
  obtain ⟨hdown, heqdown⟩ := downInduces
  have hpull (z : GroupAlgebraCenter k G) :
      cHD.centralCharacter BD' (centerMap f hf z) = cGU.centralCharacter BU' z := by
    calc
      _ = inducedCentralCharacter V (cV.centralCharacter bV) hdown
          (centerMap f hf z) := by rw [heqdown]
      _ = cV.centralCharacter bV (centerCoeffRestrict V (centerMap f hf z)) := rfl
      _ = cV.centralCharacter bV (centerMap fU hfU (centerCoeffRestrict U z)) := by
        rw [center_restriction_square f hf U V fU hfU square saturated]
      _ = cU.centralCharacter bU (centerCoeffRestrict U z) :=
        centralCharacter_pullback fU hfU cU cV bU bV localPhysical _
      _ = inducedCentralCharacter U (cU.centralCharacter bU) hup z := rfl
      _ = cGU.centralCharacter BU' z := by rw [hequp]
  have hv : cHD.centralCharacter BD'
      (centerMap f hf (dGU.blockIdempotentInCenter BU')) = 1 := by
    rw [hpull, cGU.centralCharacter_own]
  have hn : algebraMapOf f (eGU BU') ≠ 0 := by
    intro hz
    have hc : centerMap f hf (dGU.blockIdempotentInCenter BU') = 0 := Subtype.ext hz
    rw [hc, map_zero] at hv
    exact zero_ne_one hv
  obtain ⟨j, hj⟩ := dHD.primitiveBlockOfIndex_surjective
    ⟨algebraMapOf f (eGU BU'), primitive _ (dGU.primitive BU') hn⟩
  have hjval : eHD j = algebraMapOf f (eGU BU') := congrArg Subtype.val hj
  have hjc : centerMap f hf (dGU.blockIdempotentInCenter BU') =
      dHD.blockIdempotentInCenter j := Subtype.ext hjval.symm
  have heq : BD' = j := by
    by_contra hne
    rw [hjc, cHD.centralCharacter_other hne] at hv
    exact zero_ne_one hv
  exact hjval.symm.trans (congrArg eHD heq.symm)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierInducedBlockImage


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
