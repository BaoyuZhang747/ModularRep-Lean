import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierEmbeddedPhysicalBlockRows
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierEmbeddedBlockInputs
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualOuterQuotient

/-! The specified quotient block law supplies every retained positive-radical
model pair, using unselected catalogues and their uniform interval law. -/

noncomputable section
set_option maxHeartbeats 2000000
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedBlockRows

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.NavarroCoveringBrauerExtension ModularRep.NavarroBrauerRestrictionCovering
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierActualNormalizerBase
open SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
open SporadicFi24P3Definition44NamedCarrierEmbeddedModelBlockRows
open SporadicFi24P3Definition44NamedCarrierEmbeddedPhysicalBlockRows
open SporadicFi24P3Definition44NamedCarrierEmbeddedBlockInputs
open SporadicFi24P3Definition44NamedCarrierQOneBlockCatalogues (UnselectedCatalogue)

universe u
variable {p : ℕ} {k K G Block : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [MulAction (MulAut G)ᵐᵒᵖ Block]
variable (iota : PrimeRegularRootEmbedding p k K G)
variable (phi : IBr iota) (V : CharacterWeight p K G)
variable (source : CanonicalRawReduction iota V)

local notation "AM" => ActualAutAmbient iota phi
local notation "B" => actualBase iota phi
local notation "D" => embeddedNormalizer (innerEmbedding iota phi) V.subgroup
local instance ambientFintype : Fintype AM := Fintype.ofFinite _
local instance normalizerFintype :
    Fintype (Subgroup.normalizer (V.subgroup : Set G)) := Fintype.ofFinite _
local instance subgroupFintype (H : Subgroup AM) : Fintype H := Fintype.ofFinite _
local instance localBaseFintype : Fintype ((B).comap (D).subtype) := Fintype.ofFinite _

theorem reduced_every_model_pair_blocks
    (O : LocalBlockInductionOperations (p := p) (k := k) (K := K) (G := G) (Block := Block))
    (compatibility : CanonicalLocalBlockCompatibility iota O)
    (hblock : letI : Fintype Block := O.ambientBlockData.fintypeBlock
      irreducibleBrauerCharacterBlock iota
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
        O.ambientBlockData.blocks phi = O.rawWeightBlock V)
    (hcenter : Subgroup.center G = ⊥)
    (hOuter : Nat.card (LiteralOuterQuotient G) = 2)
    (hV : V.subgroup ≠ ⊥)
    (S9295 : Navarro9295BrauerRestrictionCoveringPrinciple p k K)
    (S9495 : Navarro9495BrauerCoveringPrinciple p k K)
    (S820 : Navarro820CyclicBrauerTwistPrinciple p k K)
    (fieldSource : SpathCoefficientField p k iota.prime)
    (seed : Nonempty (PrimeRegularRootEmbedding p k K AM))
    (ambient : B ≠ ⊤ → UnselectedCatalogue (k := k) (A := AM))
    (localInputs : letI : Fact p.Prime := ⟨iota.prime⟩
      B ≠ ⊤ → PositiveLocalCatalogueInput (p := p) (k := k) (innerEmbedding iota phi)) :
    EveryEmbeddedModelPairBlocks B D
      (iota.alongMulEquiv (actualBaseEquiv iota phi hcenter))
      (source.normalizerRoot.alongMulEquiv
        (normalizerBaseEquiv (innerEmbedding iota phi)
          (innerEmbedding_injective iota phi hcenter) V.subgroup))
      (IrreducibleBrauerCharacter.alongMulEquiv iota (actualBaseEquiv iota phi hcenter) phi)
      (IrreducibleBrauerCharacter.alongMulEquiv source.normalizerRoot
        (normalizerBaseEquiv (innerEmbedding iota phi)
          (innerEmbedding_injective iota phi hcenter) V.subgroup) source.localBrauer) := by
  let _ : Fact p.Prime := ⟨iota.prime⟩
  let data := O.inflatedNormalizerBlockData V.subgroup
  let _ : Fintype Block := O.ambientBlockData.fintypeBlock
  let _ : Fintype (InflatedNormalizerBlock (k := k) V.subgroup) := data.fintypeBlock
  let dataN : AmbientBlockCatalogueData (k := k)
      (G := Subgroup.normalizer (V.subgroup : Set G))
      (Block := InflatedNormalizerBlock (k := k) V.subgroup) := {
    fintypeBlock := data.fintypeBlock
    blockIdempotent := inflatedNormalizerBlockIdempotent (k := k) V.subgroup
    blocks := data.blocks
    catalogue := data.catalogue }
  have hInd : BlockInducesTo (Subgroup.normalizer (V.subgroup : Set G))
      dataN.catalogue O.ambientBlockData.catalogue
      (irreducibleBrauerCharacterBlock source.normalizerRoot
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) dataN.blocks source.localBrauer)
      (irreducibleBrauerCharacterBlock iota
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) O.ambientBlockData.blocks phi) := by
    change BlockInducesTo _ data.catalogue O.ambientBlockData.catalogue
      (NavarroLocalReductionInflationBlockCompatibility.normalizerBrauerBlock
        O V.subgroup source.normalizerRoot source.localBrauer)
      (irreducibleBrauerCharacterBlock iota
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) O.ambientBlockData.blocks phi)
    rw [compatibility.normalizerBrauerBlock_eq_inflateToNormalizer V source, hblock]
    exact inducedBlock_spec (Subgroup.normalizer (V.subgroup : Set G))
      data.catalogue O.ambientBlockData.catalogue
      (O.inflateToNormalizer V.subgroup
        (O.localCharacterBlock V.subgroup V.localCharacter V.defectZero))
      (O.blockInductionDefined V)
  exact every_embedded_physical_model_pair_blocks iota phi V source B D
    (actualBaseEquiv iota phi hcenter)
    (normalizerBaseEquiv (innerEmbedding iota phi)
      (innerEmbedding_injective iota phi hcenter) V.subgroup)
    S9295 S9495 S820 (fun _ => rfl)
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
    O.ambientBlockData dataN hInd seed fieldSource
    (actual_quotient_isCyclic iota phi hOuter)
    (actual_intermediate_eq_base_or_top iota phi hOuter)
    (V.subgroup.map (innerEmbedding iota phi))
    (normalizerCentralBrauerInterval (V.radical.isPGroup.map (innerEmbedding iota phi)))
    ambient (fun hB => localInputs hB ⟨V.subgroup, V.radical⟩ hV)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedBlockRows


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
