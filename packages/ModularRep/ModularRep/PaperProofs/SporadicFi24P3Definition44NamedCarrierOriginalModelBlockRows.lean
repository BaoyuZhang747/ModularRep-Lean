import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalTopExtensions
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalTopIntermediateBlocks
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction

/-! Both actual retained models realize the original characters, and their
same extensions satisfy the complete original-group intermediate block law. -/

noncomputable section
set_option maxHeartbeats 2000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalModelBlockRows

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open Representation.Extension
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierAssociatedProjectiveModel
open SporadicFi24P3Definition44NamedCarrierFactorOneExtension
open SporadicFi24P3Definition44NamedCarrierOriginalTopExtensions
open SporadicFi24P3Definition44NamedCarrierOriginalTopIntermediateBlocks
open SporadicFi24P3Definition44NamedCarrierIntermediateBlockConclusions

universe u
variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G]
variable (iota : PrimeRegularRootEmbedding p k K G) (phi : IBr iota)
variable (V : CharacterWeight p K G) (source : CanonicalRawReduction iota V)
local notation "N" => Subgroup.normalizer (V.subgroup : Set G)
local instance normalizerFintype : Fintype N := Fintype.ofFinite _
local notation "B" => (⊤ : Subgroup G)
local notation "L" => (⊤ : Subgroup N)
local notation "eG" => (Subgroup.topEquiv.symm : G ≃* B)
local notation "eN" => (Subgroup.topEquiv.symm : N ≃* L)
local notation "rB" => iota.alongMulEquiv eG
local notation "rL" => source.normalizerRoot.alongMulEquiv eN
local notation "phiB" => IrreducibleBrauerCharacter.alongMulEquiv iota eG phi
local notation "phiL" => IrreducibleBrauerCharacter.alongMulEquiv source.normalizerRoot eN source.localBrauer

variable {UG UL : Type u}
variable [AddCommGroup UG] [Module k UG] [FiniteDimensional k UG]
variable [AddCommGroup UL] [Module k UL] [FiniteDimensional k UL]
variable (rhoG : Representation k (⊤ : Subgroup G) UG)
variable (rhoL : Representation k (⊤ : Subgroup (Subgroup.normalizer (V.subgroup : Set G))) UL)
variable (MG : AssociatedProjectiveModel (⊤ : Subgroup G) rhoG)
variable (ML : AssociatedProjectiveModel (⊤ : Subgroup (Subgroup.normalizer (V.subgroup : Set G))) rhoL)
variable (hMG : MG.factorSet = ScalarFactorSet.trivial)
variable (hML : ML.factorSet = ScalarFactorSet.trivial)

def OriginalModelPairBlocks : Prop :=
  ∃ globalW : BrauerCharacterExtensionWitness iota rB phiB,
    globalW.val = phi ∧
    globalW.val.val = (representationOfFactorOne MG hMG).brauerCharacterOfRootEmbedding iota ∧
    ∃ localW : BrauerCharacterExtensionWitness source.normalizerRoot rL phiL,
      localW.val = source.localBrauer ∧
      localW.val.val = (representationOfFactorOne ML hML).brauerCharacterOfRootEmbedding source.normalizerRoot ∧
      AllIntermediateBlocks (k := k) N globalW.val.val localW.val.val B

theorem original_model_pair_blocks
    (hirrG : Representation.IsIrreducible rhoG)
    (haffordsG : (phiB).val = rhoG.brauerCharacterOfRootEmbedding rB)
    (hirrL : Representation.IsIrreducible rhoL)
    (haffordsL : (phiL).val = rhoL.brauerCharacterOfRootEmbedding rL)
    (injG : IrreducibleBrauerCharacterInjectivity iota)
    {BG BL : Type u}
    (dataG : AmbientBlockCatalogueData (k := k) (G := G) (Block := BG))
    (dataL : AmbientBlockCatalogueData (k := k) (G := N) (Block := BL))
    (hInd : letI : Fintype BG := dataG.fintypeBlock
      letI : Fintype BL := dataL.fintypeBlock
      BlockInducesTo N dataL.catalogue dataG.catalogue
        (irreducibleBrauerCharacterBlock source.normalizerRoot
          (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) dataL.blocks source.localBrauer)
        (irreducibleBrauerCharacterBlock iota injG dataG.blocks phi)) :
    OriginalModelPairBlocks iota phi V source rhoG rhoL MG ML hMG hML := by
  let globalW := topModelExtension iota phi rhoG MG hMG hirrG haffordsG
  let localW := topModelExtension source.normalizerRoot source.localBrauer rhoL ML hML hirrL haffordsL
  have hglobal : globalW.val = phi := topModelExtension_val iota phi rhoG MG hMG hirrG haffordsG
  have hlocal : localW.val = source.localBrauer :=
    topModelExtension_val source.normalizerRoot source.localBrauer rhoL ML hML hirrL haffordsL
  refine ⟨globalW, hglobal, rfl, localW, hlocal, rfl, ?_⟩
  rw [hglobal, hlocal]
  exact original_top_intermediate_blocks N iota source.normalizerRoot injG
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) phi source.localBrauer dataG dataL hInd


def EveryOriginalModelPairBlocks : Prop :=
  ∀ (WG : FDRep k B) (WL : FDRep k L)
    (MG : AssociatedProjectiveModel B WG.ρ) (ML : AssociatedProjectiveModel L WL.ρ)
    (hMG : MG.factorSet = ScalarFactorSet.trivial) (hML : ML.factorSet = ScalarFactorSet.trivial),
    Representation.IsIrreducible WG.ρ →
    (phiB).val = Representation.brauerCharacterOfRootEmbedding WG.ρ rB →
    Representation.IsIrreducible WL.ρ →
    (phiL).val = Representation.brauerCharacterOfRootEmbedding WL.ρ rL →
    OriginalModelPairBlocks iota phi V source WG.ρ WL.ρ MG ML hMG hML

theorem every_original_model_pair_blocks
    (injG : IrreducibleBrauerCharacterInjectivity iota)
    {BG BL : Type u}
    (dataG : AmbientBlockCatalogueData (k := k) (G := G) (Block := BG))
    (dataL : AmbientBlockCatalogueData (k := k) (G := N) (Block := BL))
    (hInd : letI : Fintype BG := dataG.fintypeBlock
      letI : Fintype BL := dataL.fintypeBlock
      BlockInducesTo N dataL.catalogue dataG.catalogue
        (irreducibleBrauerCharacterBlock source.normalizerRoot
          (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) dataL.blocks source.localBrauer)
        (irreducibleBrauerCharacterBlock iota injG dataG.blocks phi)) :
    EveryOriginalModelPairBlocks iota phi V source := by
  intro WG WL MG ML hMG hML hirrG haffordsG hirrL haffordsL
  exact original_model_pair_blocks iota phi V source WG.ρ WL.ρ MG ML hMG hML
    hirrG haffordsG hirrL haffordsL injG dataG dataL hInd

/-- Apply the universal conclusion to both unchanged representation carriers. -/
theorem every_original_model_pair_blocks_apply
    (h : EveryOriginalModelPairBlocks iota phi V source)
    {UG UL : Type u}
    [AddCommGroup UG] [Module k UG] [FiniteDimensional k UG]
    [AddCommGroup UL] [Module k UL] [FiniteDimensional k UL]
    (rhoG : Representation k B UG) (rhoL : Representation k L UL)
    (MG : AssociatedProjectiveModel B rhoG) (ML : AssociatedProjectiveModel L rhoL)
    (hMG : MG.factorSet = ScalarFactorSet.trivial) (hML : ML.factorSet = ScalarFactorSet.trivial)
    (hirrG : Representation.IsIrreducible rhoG)
    (haffordsG : (phiB).val = rhoG.brauerCharacterOfRootEmbedding rB)
    (hirrL : Representation.IsIrreducible rhoL)
    (haffordsL : (phiL).val = rhoL.brauerCharacterOfRootEmbedding rL) :
    OriginalModelPairBlocks iota phi V source rhoG rhoL MG ML hMG hML :=
  h (FDRep.of rhoG) (FDRep.of rhoL) MG ML hMG hML hirrG haffordsG hirrL haffordsL

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalModelBlockRows


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
