import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierEmbeddedPhysicalBlockRows
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierEmbeddedBlockInputs
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPhysicalQOneBlockRows
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSameFamilyBlockInduction

/-! Positive radical block laws on the actual centre-two branch,
for every pair of the same retained factor-one models. -/

noncomputable section
set_option maxHeartbeats 2000000
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralTwoEmbeddedBlockRows

open ModularRep ModularRep.CharacterWeight
open ModularRep.NavarroCoveringBrauerExtension ModularRep.NavarroBrauerRestrictionCovering
open SporadicFi24P3Definition44NamedCarrierEmbeddedModelBlockRows
open SporadicFi24P3Definition44NamedCarrierEmbeddedPhysicalBlockRows
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

variable {T C : Type u} [Group T] [Group C]
variable (E : GroupExtension G T C) (hC : Nat.card C = 2)

def CentralTwoPositiveLocalInputs : Prop :=
  letI : Fact p.Prime := ⟨iota.prime⟩
  letI : Finite T := extension_finite E hC
  ∀ phi : FB,
    letI : Fintype (brauerAmbient E iota phi.val) := Fintype.ofFinite _
    (brauerEmbedding E iota phi.val).range ≠ ⊤ →
      PositiveLocalCatalogueInput (p := p) (k := k) (brauerEmbedding E iota phi.val)

def CentralTwoPositiveBlockOutput (e : FB ≃ FW) : Prop :=
  letI : Finite T := extension_finite E hC
  ∀ phi : FB,
    letI : Fintype (brauerAmbient E iota phi.val) := Fintype.ofFinite _
    ∀ (V : CharacterWeight p K G),
      (Quotient.mk'' (Quotient.mk'' V) : ConjugacyClass) = (e phi).val →
      V.subgroup ≠ ⊥ → ∀ source : CanonicalRawReduction iota V,
        EveryEmbeddedModelPairBlocks
          ((brauerEmbedding E iota phi.val).range) (embeddedNormalizer (brauerEmbedding E iota phi.val) V.subgroup)
          (iota.alongMulEquiv (MonoidHom.ofInjective (brauerEmbedding_injective E iota phi.val)))
          (source.normalizerRoot.alongMulEquiv (normalizerBaseEquiv (brauerEmbedding E iota phi.val)
            (brauerEmbedding_injective E iota phi.val) V.subgroup))
          (IrreducibleBrauerCharacter.alongMulEquiv iota (MonoidHom.ofInjective (brauerEmbedding_injective E iota phi.val)) phi.val)
          (IrreducibleBrauerCharacter.alongMulEquiv source.normalizerRoot
            (normalizerBaseEquiv (brauerEmbedding E iota phi.val)
              (brauerEmbedding_injective E iota phi.val) V.subgroup) source.localBrauer)

theorem central_two_positive_block_output
    (e : FB ≃ FW) (hBlocks : MatchedBlockOutput iota hinj R blocks E1 e)
    (S9295 : Navarro9295BrauerRestrictionCoveringPrinciple p k K)
    (S9495 : Navarro9495BrauerCoveringPrinciple p k K)
    (S820 : Navarro820CyclicBrauerTwistPrinciple p k K)
    (fieldSource : SpathCoefficientField p k iota.prime)
    (ambient : letI : Finite T := extension_finite E hC
      ∀ phi : FB,
      letI : Fintype (brauerAmbient E iota phi.val) := Fintype.ofFinite _
      (brauerEmbedding E iota phi.val).range ≠ ⊤ → UnselectedCatalogue (k := k) (A := brauerAmbient E iota phi.val))
    (seed : letI : Finite T := extension_finite E hC
      ∀ phi : FB, Nonempty (PrimeRegularRootEmbedding p k K (brauerAmbient E iota phi.val)))
    (localInputs : CentralTwoPositiveLocalInputs iota hinj R blocks E1 E hC) :
    CentralTwoPositiveBlockOutput iota hinj R blocks E1 E hC e := by
  let : Fact p.Prime := ⟨iota.prime⟩
  let : Finite T := extension_finite E hC
  intro phi
  let : Fintype (brauerAmbient E iota phi.val) := Fintype.ofFinite _
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
  exact every_embedded_physical_model_pair_blocks iota phi.val V source
    ((brauerEmbedding E iota phi.val).range) (embeddedNormalizer (brauerEmbedding E iota phi.val) V.subgroup)
    (MonoidHom.ofInjective (brauerEmbedding_injective E iota phi.val))
    (normalizerBaseEquiv (brauerEmbedding E iota phi.val)
      (brauerEmbedding_injective E iota phi.val) V.subgroup)
    S9295 S9495 S820 (fun n => rfl) hinj R.1.operations.ambientBlockData dataN
    ((hBlocks.2 phi V hmatch).2.2 source) (seed phi) fieldSource
    (brauerQuotient_cyclic E iota phi.val hC)
    (brauer_intermediate_eq_base_or_top E iota phi.val hC)
    (V.subgroup.map (brauerEmbedding E iota phi.val))
    (normalizerCentralBrauerInterval (V.radical.isPGroup.map (brauerEmbedding E iota phi.val)))
    (ambient phi) (fun hB => localInputs phi hB ⟨V.subgroup, V.radical⟩ hV)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralTwoEmbeddedBlockRows


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
