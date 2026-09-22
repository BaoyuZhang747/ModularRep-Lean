import ModularRep.BlockInductionCentralIdempotentSupport
import ModularRep.CentralCharacterBlockSector
import Mathlib.Algebra.Group.Subgroup.Map

/-!
# Central subgroup characters preserved by block induction

The first part proves the literal coefficient-restriction formula for the
standard central character idempotent. The subgroup order is unchanged under
subgroupOfEquivOfLe, so invertibility transfers without a new hypothesis.

The final theorem identifies the actual Schur characters of two fixed
irreducible representations from literal block induction and the actions of
their literal block idempotents. It assumes neither the desired
central character equality nor either representation's central sector; the
ordinary-trace and root-lift comparison is outside this module.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep

section CentralSubgroupRestriction

variable {k G : Type*} [Field k] [Group G]

/-- A central subgroup remains central when viewed inside any subgroup. -/
theorem subgroupOf_le_center (H Z : Subgroup G)
    (hZ : Z ≤ Subgroup.center G) :
    Z.subgroupOf H ≤ Subgroup.center H := by
  intro z hz
  apply Subgroup.mem_center_iff.mpr
  intro h
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp (hZ hz) (h : G)

/-- If `Z ≤ H`, passing to the subgroup of `H` does not change its order. -/
theorem card_subgroupOf_eq_of_le (H Z : Subgroup G)
    [Fintype Z] [Fintype (Z.subgroupOf H)] (hZH : Z ≤ H) :
    Fintype.card (Z.subgroupOf H) = Fintype.card Z :=
  Fintype.card_congr (Subgroup.subgroupOfEquivOfLe hZH).toEquiv

/-- Transfer invertibility of the central subgroup order along its literal
subgroup equivalence. This is a definition, not a new source assumption or
a global instance. -/
def invertibleCardSubgroupOfOfLe (H Z : Subgroup G)
    [Fintype Z] [Fintype (Z.subgroupOf H)] (hZH : Z ≤ H)
    [Invertible (Fintype.card Z : k)] :
    Invertible (Fintype.card (Z.subgroupOf H) : k) :=
  (inferInstance : Invertible (Fintype.card Z : k)).copy _
    (congrArg (Nat.cast : ℕ → k) (card_subgroupOf_eq_of_le H Z hZH))

/-- Coefficient restriction of the character idempotent is the idempotent
for the same character in the subgroup. This algebraic formula does not
require centrality. -/
theorem coeffRestrict_centralCharacterIdempotent
    (H Z : Subgroup G) [Fintype Z] [Fintype (Z.subgroupOf H)]
    (hZH : Z ≤ H) [Invertible (Fintype.card Z : k)]
    [Invertible (Fintype.card (Z.subgroupOf H) : k)]
    (nu : Z →* kˣ) :
    coeffRestrict H (centralCharacterIdempotent Z nu) =
      centralCharacterIdempotent (Z.subgroupOf H)
        (nu.comp (Subgroup.subgroupOfEquivOfLe hZH).toMonoidHom) := by
  classical
  have hcard := card_subgroupOf_eq_of_le H Z hZH
  have hinv : ⅟(Fintype.card Z : k) =
      ⅟(Fintype.card (Z.subgroupOf H) : k) := by
    simp only [invOf_eq_inv, hcard]
  ext h
  rw [coeffRestrict_apply]
  by_cases hz : (h : G) ∈ Z
  · let zH : Z.subgroupOf H := ⟨h, hz⟩
    let zG : Z := Subgroup.subgroupOfEquivOfLe hZH zH
    change (centralCharacterIdempotent Z nu).coeff (zG : G) =
      (centralCharacterIdempotent (Z.subgroupOf H)
        (nu.comp (Subgroup.subgroupOfEquivOfLe hZH).toMonoidHom)).coeff (zH : H)
    simp only [centralCharacterIdempotent_coeff_coe, hinv, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, zG]
  · rw [centralCharacterIdempotent_coeff_of_not_mem Z nu hz,
      centralCharacterIdempotent_coeff_of_not_mem (Z.subgroupOf H)
        (nu.comp (Subgroup.subgroupOfEquivOfLe hZH).toMonoidHom)
        (show h ∉ Z.subgroupOf H from hz)]

/-- The standard central character idempotent as an element of the centre
subalgebra used in the definition of block induction. -/
def centralCharacterIdempotentInCenter
    (Z : Subgroup G) [Fintype Z] [Invertible (Fintype.card Z : k)]
    (nu : Z →* kˣ) (hZ : Z ≤ Subgroup.center G) :
    GroupAlgebraCenter k G :=
  ⟨centralCharacterIdempotent Z nu,
    Subalgebra.mem_center_iff.mpr
      (Semigroup.mem_center_iff.mp (centralCharacterIdempotent_mem_center Z nu hZ))⟩

@[simp]
theorem centralCharacterIdempotentInCenter_coe
    (Z : Subgroup G) [Fintype Z] [Invertible (Fintype.card Z : k)]
    (nu : Z →* kˣ) (hZ : Z ≤ Subgroup.center G) :
    ((centralCharacterIdempotentInCenter Z nu hZ : GroupAlgebraCenter k G) : k[G]) =
      centralCharacterIdempotent Z nu := rfl

/-- Centre-valued form of the literal coefficient-restriction formula. -/
theorem centerCoeffRestrict_centralCharacterIdempotentInCenter
    (H Z : Subgroup G) [Fintype Z] [Fintype (Z.subgroupOf H)]
    (hZH : Z ≤ H) (hZ : Z ≤ Subgroup.center G)
    [Invertible (Fintype.card Z : k)]
    [Invertible (Fintype.card (Z.subgroupOf H) : k)]
    (nu : Z →* kˣ) :
    centerCoeffRestrict H (centralCharacterIdempotentInCenter Z nu hZ) =
      centralCharacterIdempotentInCenter (Z.subgroupOf H)
        (nu.comp (Subgroup.subgroupOfEquivOfLe hZH).toMonoidHom)
        (subgroupOf_le_center H Z hZ) := by
  apply Subtype.ext
  exact coeffRestrict_centralCharacterIdempotent H Z hZH nu

/-- The restricted idempotent is idempotent. Only the global subgroup order
needs to be supplied as invertible; the local inverse is derived. -/
theorem coeffRestrict_centralCharacterIdempotent_isIdempotentElem
    (H Z : Subgroup G) [Fintype Z] [Fintype (Z.subgroupOf H)]
    (hZH : Z ≤ H) [Invertible (Fintype.card Z : k)]
    (nu : Z →* kˣ) :
    IsIdempotentElem (coeffRestrict H (centralCharacterIdempotent Z nu)) := by
  letI : Invertible (Fintype.card (Z.subgroupOf H) : k) :=
    invertibleCardSubgroupOfOfLe H Z hZH
  rw [coeffRestrict_centralCharacterIdempotent H Z hZH nu]
  exact centralCharacterIdempotent_isIdempotentElem (Z.subgroupOf H)
    (nu.comp (Subgroup.subgroupOfEquivOfLe hZH).toMonoidHom)

end CentralSubgroupRestriction

end ModularRep

namespace Representation

open ModularRep

variable {k G LocalBlock AmbientBlock VN VG : Type*}
variable [Field k] [IsAlgClosed k] [Group G] [Fintype G]
variable [Fintype LocalBlock] [Fintype AmbientBlock]
variable [AddCommGroup VN] [Module k VN] [FiniteDimensional k VN]
variable [AddCommGroup VG] [Module k VG] [FiniteDimensional k VG]
variable (H Z : Subgroup G)

local instance centralCharacterBlockInductionSubgroupFintype : Fintype H :=
  Fintype.ofFinite H

local instance centralCharacterBlockInductionCentralSubgroupFintype :
    Fintype (Z.subgroupOf H) := Fintype.ofFinite (Z.subgroupOf H)

variable {localIdempotent : LocalBlock → k[H]}
variable {ambientIdempotent : AmbientBlock → k[G]}
variable {localBlocks : BlockIdempotentDecomposition localIdempotent}
variable {ambientBlocks : BlockIdempotentDecomposition ambientIdempotent}

/-- Block induction preserves the actual Schur character on any contained
central subgroup of invertible order. Both representations are fixed, and
the block actions are literal; all central-sector equalities are deduced. -/
theorem centralCharacter_eq_comp_of_blockInducesTo
    [Fintype Z] [Invertible (Fintype.card Z : k)]
    (hZH : Z ≤ H) (hZ : Z ≤ Subgroup.center G)
    (localCatalogue : BlockCentralCharacterCatalogue localBlocks)
    (ambientCatalogue : BlockCentralCharacterCatalogue ambientBlocks)
    {b : LocalBlock} {B : AmbientBlock}
    (hinduces : BlockInducesTo H localCatalogue ambientCatalogue b B)
    (rhoN : Representation k H VN) [rhoN.IsIrreducible]
    (rhoG : Representation k G VG) [rhoG.IsIrreducible]
    (hbV : ∀ v : rhoN.asModule, localIdempotent b • v = v)
    (hBV : ∀ v : rhoG.asModule, ambientIdempotent B • v = v) :
    rhoN.centralCharacter (Z.subgroupOf H) (subgroupOf_le_center H Z hZ) =
      (rhoG.centralCharacter Z hZ).comp
        (Subgroup.subgroupOfEquivOfLe hZH).toMonoidHom := by
  classical
  letI : Invertible (Fintype.card (Z.subgroupOf H) : k) :=
    invertibleCardSubgroupOfOfLe H Z hZH
  let nu : Z →* kˣ :=
    (ambientBlocks.primitive B).centralCharacterSector Z hZ
  let nuH : Z.subgroupOf H →* kˣ :=
    nu.comp (Subgroup.subgroupOfEquivOfLe hZH).toMonoidHom
  let e : GroupAlgebraCenter k G :=
    centralCharacterIdempotentInCenter Z nu hZ
  have he : IsIdempotentElem (e : k[G]) :=
    centralCharacterIdempotent_isIdempotentElem Z nu
  have heLocal : IsIdempotentElem
      ((centerCoeffRestrict H e : GroupAlgebraCenter k H) : k[H]) :=
    coeffRestrict_centralCharacterIdempotent_isIdempotentElem H Z hZH nu
  have hB : ambientIdempotent B * (e : k[G]) = ambientIdempotent B :=
    (ambientBlocks.primitive B).mul_centralCharacterSector Z hZ
  have hrestricted : localIdempotent b *
      ((centerCoeffRestrict H e : GroupAlgebraCenter k H) : k[H]) =
      localIdempotent b :=
    blockInducesTo_preserves_centralIdempotentSupport H
      localCatalogue ambientCatalogue hinduces e he heLocal hB
  have hb : localIdempotent b * centralCharacterIdempotent (Z.subgroupOf H) nuH =
      localIdempotent b := by
    change localIdempotent b *
      coeffRestrict H (centralCharacterIdempotent Z nu) = localIdempotent b
      at hrestricted
    rw [coeffRestrict_centralCharacterIdempotent H Z hZH nu] at hrestricted
    exact hrestricted
  have hLocalSector :
      (localBlocks.primitive b).centralCharacterSector (Z.subgroupOf H)
        (subgroupOf_le_center H Z hZ) = nuH := by
    by_contra hne
    have hzero :=
      (localBlocks.primitive b).mul_centralCharacterIdempotent_eq_zero_of_ne_sector
        (Z.subgroupOf H) (subgroupOf_le_center H Z hZ) (Ne.symm hne)
    exact (localBlocks.primitive b).ne_zero (hb.symm.trans hzero)
  have hGlobalSector : nu = rhoG.centralCharacter Z hZ :=
    rhoG.primitiveCentralIdempotentSector_eq_centralCharacter Z hZ
      (ambientBlocks.primitive B) hBV
  calc
    rhoN.centralCharacter (Z.subgroupOf H) (subgroupOf_le_center H Z hZ) =
        (localBlocks.primitive b).centralCharacterSector (Z.subgroupOf H)
          (subgroupOf_le_center H Z hZ) :=
      (rhoN.primitiveCentralIdempotentSector_eq_centralCharacter
        (Z.subgroupOf H) (subgroupOf_le_center H Z hZ)
        (localBlocks.primitive b) hbV).symm
    _ = nuH := hLocalSector
    _ = (rhoG.centralCharacter Z hZ).comp
        (Subgroup.subgroupOfEquivOfLe hZH).toMonoidHom := by
      change nu.comp (Subgroup.subgroupOfEquivOfLe hZH).toMonoidHom = _
      rw [hGlobalSector]

/-- Pointwise interface for the ordinary restriction join. The local
centrality witness is arbitrary, so an existing literal proof can be used
without replacing either subgroup or character convention. -/
theorem centralCharacter_apply_eq_of_blockInducesTo
    [Fintype Z] [Invertible (Fintype.card Z : k)]
    (hZH : Z ≤ H) (hZ : Z ≤ Subgroup.center G)
    (hZLocal : Z.subgroupOf H ≤ Subgroup.center H)
    (localCatalogue : BlockCentralCharacterCatalogue localBlocks)
    (ambientCatalogue : BlockCentralCharacterCatalogue ambientBlocks)
    {b : LocalBlock} {B : AmbientBlock}
    (hinduces : BlockInducesTo H localCatalogue ambientCatalogue b B)
    (rhoN : Representation k H VN) [rhoN.IsIrreducible]
    (rhoG : Representation k G VG) [rhoG.IsIrreducible]
    (hbV : ∀ v : rhoN.asModule, localIdempotent b • v = v)
    (hBV : ∀ v : rhoG.asModule, ambientIdempotent B • v = v)
    (zN : Z.subgroupOf H) :
    rhoN.centralCharacter (Z.subgroupOf H) hZLocal zN =
      rhoG.centralCharacter Z hZ (Subgroup.subgroupOfEquivOfLe hZH zN) := by
  have h := centralCharacter_eq_comp_of_blockInducesTo H Z hZH hZ
    localCatalogue ambientCatalogue hinduces rhoN rhoG hbV hBV
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using
    congrArg (fun nu : Z.subgroupOf H →* kˣ ↦ nu zN) h

end Representation



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
