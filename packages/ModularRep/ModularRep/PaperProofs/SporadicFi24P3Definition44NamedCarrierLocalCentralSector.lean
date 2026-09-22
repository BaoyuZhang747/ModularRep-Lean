import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFixedCentralBlockKernel
import ModularRep.PaperProofs.SporadicFi24LiteralCarrierBase

/-!
# The local central character of the own induced block

Coefficient restriction carries central character support through actual
block induction. The canonical local reduction therefore has the central
character of its own specified induced block.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierLocalCentralSector

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierCentralBlockKernel
open SporadicFi24P3Definition44NamedCarrierBrauerBlockAction
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction

universe u

section Induction

variable {k G LocalBlock AmbientBlock VN : Type*}
variable [Field k] [IsAlgClosed k] [Group G] [Fintype G]
variable [Fintype LocalBlock] [Fintype AmbientBlock]
variable [AddCommGroup VN] [Module k VN] [FiniteDimensional k VN]
variable (H Z : Subgroup G)
local instance subgroupFintype : Fintype H := Fintype.ofFinite H
variable {localIdempotent : LocalBlock → k[H]}
variable {ambientIdempotent : AmbientBlock → k[G]}
variable {localBlocks : BlockIdempotentDecomposition localIdempotent}
variable {ambientBlocks : BlockIdempotentDecomposition ambientIdempotent}

theorem local_centralCharacter_eq_of_blockInducesTo_support
    [Fintype Z] [Invertible (Fintype.card Z : k)]
    (hZH : Z ≤ H) (hZ : Z ≤ Subgroup.center G)
    (localCatalogue : BlockCentralCharacterCatalogue localBlocks)
    (ambientCatalogue : BlockCentralCharacterCatalogue ambientBlocks)
    {b : LocalBlock} {B : AmbientBlock}
    (hinduces : BlockInducesTo H localCatalogue ambientCatalogue b B)
    (rhoN : Representation k H VN) [rhoN.IsIrreducible]
    (hbV : ∀ v : rhoN.asModule, localIdempotent b • v = v)
    (nu : Z →* kˣ)
    (hB : ambientIdempotent B * centralCharacterIdempotent Z nu =
      ambientIdempotent B) :
    rhoN.centralCharacter (Z.subgroupOf H) (subgroupOf_le_center H Z hZ) =
      nu.comp (Subgroup.subgroupOfEquivOfLe hZH).toMonoidHom := by
  classical
  let : Fintype (Z.subgroupOf H) := Fintype.ofFinite _
  let : Invertible (Fintype.card (Z.subgroupOf H) : k) :=
    invertibleCardSubgroupOfOfLe H Z hZH
  have hb : localIdempotent b * centralCharacterIdempotent (Z.subgroupOf H)
      (nu.comp (Subgroup.subgroupOfEquivOfLe hZH).toMonoidHom) =
      localIdempotent b := by
    have h := blockInducesTo_preserves_centralIdempotentSupport H
      localCatalogue ambientCatalogue hinduces
      (centralCharacterIdempotentInCenter Z nu hZ)
      (centralCharacterIdempotent_isIdempotentElem Z nu)
      (coeffRestrict_centralCharacterIdempotent_isIdempotentElem H Z hZH nu) hB
    change localIdempotent b * coeffRestrict H (centralCharacterIdempotent Z nu) =
      localIdempotent b at h
    rw [coeffRestrict_centralCharacterIdempotent H Z hZH nu] at h
    exact h
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
variable (iota : PrimeRegularRootEmbedding p k K G)
variable (O : LocalBlockInductionOperations
  (p := p) (k := k) (K := K) (G := G) (Block := Block))
variable (W : CharacterWeight p K G) (source : CanonicalRawReduction iota W)
variable (compatibility : CanonicalLocalBlockCompatibility iota O)

local instance localIrreducible : Representation.IsIrreducible
    (chosenIBrRepresentation source.normalizerRoot source.localBrauer).ρ :=
  (Classical.choose_spec source.localBrauer.2).1

include compatibility in
theorem fixedZ_local_centralCharacter
    (Z : Subgroup G) [Invertible (Fintype.card Z : k)]
    (hZ : Z ≤ Subgroup.center G) (nu : Z →* kˣ)
    (hsupport : O.ambientBlockData.blockIdempotent (O.rawWeightBlock W) *
        centralCharacterIdempotent Z nu =
      O.ambientBlockData.blockIdempotent (O.rawWeightBlock W)) :
    Representation.centralCharacter (chosenIBrRepresentation source.normalizerRoot source.localBrauer).ρ
      (Z.subgroupOf (Subgroup.normalizer (W.subgroup : Set G)))
      (subgroupOf_le_center (Subgroup.normalizer (W.subgroup : Set G)) Z hZ) =
      nu.comp (Subgroup.subgroupOfEquivOfLe
        (hZ.trans (Subgroup.center_le_normalizer (W.subgroup : Set G)))).toMonoidHom := by
  let localData := O.inflatedNormalizerBlockData W.subgroup
  let _ := O.ambientBlockData.fintypeBlock
  let _ := localData.fintypeBlock
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
  exact local_centralCharacter_eq_of_blockInducesTo_support N Z
    (hZ.trans (Subgroup.center_le_normalizer (W.subgroup : Set G))) hZ
    localData.catalogue O.ambientBlockData.catalogue hbase rhoN
    (block_smul_of_affording source.normalizerRoot injN localData.blocks source.localBrauer
      (chosenIBrRepresentation source.normalizerRoot source.localBrauer)
      (Classical.choose_spec source.localBrauer.2).1
      (chosenIBrRepresentation_character source.normalizerRoot source.localBrauer)) nu hsupport

end CharacterWeight

section ActualCharacterWeight

variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G]
local instance actualSubgroupFintype (H : Subgroup G) : Fintype H := Fintype.ofFinite H
variable (iota : PrimeRegularRootEmbedding p k K G)
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := G))
variable (W : CharacterWeight p K G) (source : CanonicalRawReduction iota W)
variable (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)

local instance actualLocalIrreducible : Representation.IsIrreducible
    (chosenIBrRepresentation source.normalizerRoot source.localBrauer).ρ :=
  (Classical.choose_spec source.localBrauer.2).1

include compatibility in
theorem rawWeightBlock_local_centralCharacter
    [Invertible (Fintype.card (Subgroup.center G) : k)] :
    Representation.centralCharacter (chosenIBrRepresentation source.normalizerRoot source.localBrauer).ρ
      ((Subgroup.center G).subgroupOf (Subgroup.normalizer (W.subgroup : Set G)))
      (subgroupOf_le_center (Subgroup.normalizer (W.subgroup : Set G))
        (Subgroup.center G) le_rfl) =
      (blockSector (k := k) (X := G) (R.1.operations.rawWeightBlock W)).comp
        (Subgroup.subgroupOfEquivOfLe
          (Subgroup.center_le_normalizer (W.subgroup : Set G))).toMonoidHom := by
  exact fixedZ_local_centralCharacter iota R.1.operations W source compatibility
    (Subgroup.center G) le_rfl
    (blockSector (k := k) (X := G) (R.1.operations.rawWeightBlock W)) (by
      rw [R.2]
      exact (R.1.operations.rawWeightBlock W).2.mul_centralCharacterSector
        (Subgroup.center G) le_rfl)

end ActualCharacterWeight

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierLocalCentralSector


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
