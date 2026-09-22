import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessEmbeddedBlockRows
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierDerivedCoveringPhysicalRows
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierEmbeddedBlockInputs
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPhysicalQOneBlockRows
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSameFamilyBlockInduction

/-! Positive radical block laws on the actual centreless branch,
for every pair of the same retained factor-one models, with local covering derived from their actual restriction. -/

noncomputable section
set_option maxHeartbeats 2000000
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierDerivedCoveringCenterlessRows

open ModularRep ModularRep.CharacterWeight
open ModularRep.NavarroCoveringBrauerExtension ModularRep.NavarroBrauerRestrictionCovering
open SporadicFi24P3Definition44NamedCarrierEmbeddedModelBlockRows
open SporadicFi24P3Definition44NamedCarrierDerivedCoveringPhysicalRows
open SporadicFi24P3Definition44NamedCarrierCenterlessEmbeddedBlockRows
open SporadicFi24P3Definition44NamedCarrierEmbeddedBlockInputs
open SporadicFi24P3Definition44NamedCarrierSameFamilyBlockInduction
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorCarriers
open SporadicFi24P3Definition44NamedCarrierQOneBlockCatalogues
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierActualNormalizerBase
open SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
open SporadicFi24P3Definition44NamedCarrierCentralTwoExtensionAmbient
open SporadicFi24P3Definition44NamedCarrierCentralTwoIntermediateGroups

universe u
variable {p : ℕ} {k K G Block : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Fintype Block]
variable {blockIdempotent : Block → k[G]}
local instance centerFintype : Fintype (Subgroup.center G) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center G) : k)]
variable (iota : PrimeRegularRootEmbedding p k K G)
variable (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := G))
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable (E1 : RoutineTransportInput iota hinj blocks R)
local notation "FW" => FaithfulWeight iota hinj blocks R E1
local notation "FB" => FaithfulIBr iota hinj blocks R E1

theorem centerless_positive_block_output_of_model_restriction
    (hcenter : Subgroup.center G = ⊥) (hOuter : Nat.card (LiteralOuterQuotient G) = 2)
    (e : FB ≃ FW) (hBlocks : MatchedBlockOutput iota hinj R blocks E1 e)
    (S9495 : Navarro9495BrauerCoveringPrinciple p k K)
    (S820 : Navarro820CyclicBrauerTwistPrinciple p k K)
    (fieldSource : SpathCoefficientField p k iota.prime)
    (ambient : ∀ phi : FB,
      letI : Fintype (ActualAutAmbient iota phi.val) := Fintype.ofFinite _
      actualBase iota phi.val ≠ ⊤ → UnselectedCatalogue (k := k) (A := ActualAutAmbient iota phi.val))
    (seed : ∀ phi : FB, Nonempty (PrimeRegularRootEmbedding p k K (ActualAutAmbient iota phi.val)))
    (localInputs : CenterlessPositiveLocalInputs iota hinj R blocks E1) :
    CenterlessPositiveBlockOutput iota hinj R blocks E1 hcenter e := by
  let : Fact p.Prime := ⟨iota.prime⟩
  intro phi
  let : Fintype (ActualAutAmbient iota phi.val) := Fintype.ofFinite _
  intro V hmatch hV source
  let : Fintype (Subgroup.normalizer (V.subgroup : Set G)) := Fintype.ofFinite _
  let data := R.1.operations.inflatedNormalizerBlockData V.subgroup
  let : Fintype (InflatedNormalizerBlock (k := k) V.subgroup) := data.fintypeBlock
  let dataN : AmbientBlockCatalogueData (k := k)
      (G := Subgroup.normalizer (V.subgroup : Set G))
      (Block := InflatedNormalizerBlock (k := k) V.subgroup) := {
    fintypeBlock := data.fintypeBlock
    blockIdempotent := inflatedNormalizerBlockIdempotent (k := k) V.subgroup
    blocks := data.blocks
    catalogue := data.catalogue }
  exact every_embedded_physical_model_pair_blocks_of_literal_restriction iota phi.val V source
    (actualBase iota phi.val) (embeddedNormalizer (innerEmbedding iota phi.val) V.subgroup)
    (actualBaseEquiv iota phi.val hcenter)
    (normalizerBaseEquiv (innerEmbedding iota phi.val)
      (innerEmbedding_injective iota phi.val hcenter) V.subgroup)
    S9495 S820 (fun n => rfl) hinj R.1.operations.ambientBlockData dataN
    ((hBlocks.2 phi V hmatch).2.2 source) (seed phi) fieldSource
    (actual_quotient_isCyclic iota phi.val hOuter)
    (actual_intermediate_eq_base_or_top iota phi.val hOuter)
    (V.subgroup.map (innerEmbedding iota phi.val))
    (normalizerCentralBrauerInterval (V.radical.isPGroup.map (innerEmbedding iota phi.val)))
    (ambient phi) (fun hB => localInputs phi hB ⟨V.subgroup, V.radical⟩ hV)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierDerivedCoveringCenterlessRows


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
