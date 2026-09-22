import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralBlockKernel
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBrauerBlockAction
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction

/-!
# Fixed central support and the local kernel

Ambient trivial-central block support implies a kernel statement for the
actual local reduction. No ambient character or matched pair is required.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFixedCentralBlockKernel

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open SporadicFi24P3Definition44NamedCarrierCentralBlockKernel
open SporadicFi24P3Definition44NamedCarrierBrauerBlockAction
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction

universe u

@[instance_reducible]
def fixedCentralCardInvertible
    {p : ℕ} {k G : Type u} [Field k] [CharP k p]
    [Group G] [Finite G] (Z : Subgroup G) [Fintype Z]
    (hprimeTo : ¬ p ∣ Nat.card Z) : Invertible (Fintype.card Z : k) :=
  invertibleOfNonzero (by
    intro h
    apply hprimeTo
    simpa only [Nat.card_eq_fintype_card] using
      (CharP.cast_eq_zero_iff k p (Fintype.card Z)).mp h)

section Induction

variable {k G LocalBlock AmbientBlock VN : Type*}
variable [Field k] [IsAlgClosed k] [Group G] [Fintype G]
variable [Fintype LocalBlock] [Fintype AmbientBlock]
variable [AddCommGroup VN] [Module k VN] [FiniteDimensional k VN]
variable (H Z : Subgroup G)

local instance subgroupFintype : Fintype H := Fintype.ofFinite H

variable {localIdempotent : LocalBlock → k[H]} {ambientIdempotent : AmbientBlock → k[G]}
variable {localBlocks : BlockIdempotentDecomposition localIdempotent}
variable {ambientBlocks : BlockIdempotentDecomposition ambientIdempotent}

theorem local_central_kernel_of_blockInducesTo_support
    [Fintype Z] [Invertible (Fintype.card Z : k)]
    (hZH : Z ≤ H) (hZ : Z ≤ Subgroup.center G)
    (localCatalogue : BlockCentralCharacterCatalogue localBlocks)
    (ambientCatalogue : BlockCentralCharacterCatalogue ambientBlocks)
    {b : LocalBlock} {B : AmbientBlock}
    (hinduces : BlockInducesTo H localCatalogue ambientCatalogue b B)
    (rhoN : Representation k H VN) [rhoN.IsIrreducible]
    (hbV : ∀ v : rhoN.asModule, localIdempotent b • v = v)
    (hB : ambientIdempotent B * centralCharacterIdempotent Z (1 : Z →* kˣ) =
      ambientIdempotent B) : Z.subgroupOf H ≤ rhoN.ker := by
  let : Fintype (Z.subgroupOf H) := Fintype.ofFinite _
  let : Invertible (Fintype.card (Z.subgroupOf H) : k) :=
    invertibleCardSubgroupOfOfLe H Z hZH
  have hb : localIdempotent b * centralCharacterIdempotent (Z.subgroupOf H)
      (1 : Z.subgroupOf H →* kˣ) = localIdempotent b := by
    have h := blockInducesTo_preserves_centralIdempotentSupport H
      localCatalogue ambientCatalogue hinduces
      (centralCharacterIdempotentInCenter Z (1 : Z →* kˣ) hZ)
      (centralCharacterIdempotent_isIdempotentElem Z 1)
      (coeffRestrict_centralCharacterIdempotent_isIdempotentElem H Z hZH 1) hB
    change localIdempotent b * coeffRestrict H (centralCharacterIdempotent Z 1) =
      localIdempotent b at h
    rw [coeffRestrict_centralCharacterIdempotent H Z hZH 1] at h
    have hone : (1 : Z →* kˣ).comp
        (Subgroup.subgroupOfEquivOfLe hZH).toMonoidHom = 1 := by
      ext z
      rfl
    simpa only [hone] using h
  apply le_ker_of_centralCharacter_eq_one (Z.subgroupOf H)
    (subgroupOf_le_center H Z hZ) rhoN
  rw [← rhoN.primitiveCentralIdempotentSector_eq_centralCharacter
    (Z.subgroupOf H) (subgroupOf_le_center H Z hZ) (localBlocks.primitive b) hbV]
  by_contra hne
  have hz := (localBlocks.primitive b).mul_centralCharacterIdempotent_eq_zero_of_ne_sector
    (Z.subgroupOf H) (subgroupOf_le_center H Z hZ) (Ne.symm hne)
  exact (localBlocks.primitive b).ne_zero (hb.symm.trans hz)

end Induction

section CharacterWeight

variable {p : ℕ} {k K G Block : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [MulAction (MulAut G)ᵐᵒᵖ Block]

local instance weightSubgroupFintype (H : Subgroup G) : Fintype H := Fintype.ofFinite H

theorem fixedZ_local_kernel
    (iota : PrimeRegularRootEmbedding p k K G)
    (O : LocalBlockInductionOperations
      (p := p) (k := k) (K := K) (G := G) (Block := Block))
    (W : CharacterWeight p K G) (source : CanonicalRawReduction iota W)
    (compatibility : CanonicalLocalBlockCompatibility iota O)
    (Z : Subgroup G) [Invertible (Fintype.card Z : k)] (hZ : Z ≤ Subgroup.center G)
    (hsupport : O.ambientBlockData.blockIdempotent (O.rawWeightBlock W) *
        centralCharacterIdempotent Z (1 : Z →* kˣ) =
      O.ambientBlockData.blockIdempotent (O.rawWeightBlock W)) :
    Z.subgroupOf (Subgroup.normalizer (W.subgroup : Set G)) ≤
      (chosenIBrRepresentation source.normalizerRoot source.localBrauer).ρ.ker := by
  let localData := O.inflatedNormalizerBlockData W.subgroup
  let := O.ambientBlockData.fintypeBlock
  let := localData.fintypeBlock
  let N := Subgroup.normalizer (W.subgroup : Set G)
  let injN := irreducibleBrauerCharacterInjectivity_of_rootEmbedding source.normalizerRoot
  have hlocal : irreducibleBrauerCharacterBlock source.normalizerRoot injN
      localData.blocks source.localBrauer =
        O.inflateToNormalizer W.subgroup
          (O.localCharacterBlock W.subgroup W.localCharacter W.defectZero) :=
    compatibility.normalizerBrauerBlock_eq_inflateToNormalizer W source
  have hbase : BlockInducesTo N localData.catalogue O.ambientBlockData.catalogue
      (irreducibleBrauerCharacterBlock source.normalizerRoot injN
        localData.blocks source.localBrauer) (O.rawWeightBlock W) := by
    rw [hlocal]
    exact inducedBlock_spec N localData.catalogue O.ambientBlockData.catalogue
      (O.inflateToNormalizer W.subgroup
        (O.localCharacterBlock W.subgroup W.localCharacter W.defectZero))
      (O.blockInductionDefined W)
  let rhoN := (chosenIBrRepresentation source.normalizerRoot source.localBrauer).ρ
  let : Representation.IsIrreducible rhoN := (Classical.choose_spec source.localBrauer.2).1
  exact local_central_kernel_of_blockInducesTo_support N Z
    (hZ.trans (Subgroup.center_le_normalizer (W.subgroup : Set G))) hZ
    localData.catalogue O.ambientBlockData.catalogue hbase rhoN
    (block_smul_of_affording source.normalizerRoot injN localData.blocks source.localBrauer
      (chosenIBrRepresentation source.normalizerRoot source.localBrauer)
      (Classical.choose_spec source.localBrauer.2).1
      (chosenIBrRepresentation_character source.normalizerRoot source.localBrauer)) hsupport

end CharacterWeight

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFixedCentralBlockKernel


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
