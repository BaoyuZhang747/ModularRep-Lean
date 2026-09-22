import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSamePairQOneBlockRows
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralTwoIntermediateGroups
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPhysicalQOneExtensionRows

/-! The Q=1 all-intermediate block law on each branch's actual carriers.
It is universal in the common pair already retained by the correspondence. -/

noncomputable section
set_option maxHeartbeats 2000000
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPhysicalQOneBlockRows

open ModularRep ModularRep.CharacterWeight
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorCarriers
open SporadicFi24P3Definition44NamedCarrierSamePairQOneGroups
open SporadicFi24P3Definition44NamedCarrierQOneBlockCatalogues
open SporadicFi24P3Definition44NamedCarrierSamePairQOneBlockRows
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
local notation "FB" => FaithfulIBr iota hinj blocks R E1

def CenterlessCommonBlockOutput (hcenter : Subgroup.center G = ⊥) : Prop :=
  ∀ phi : FB,
    letI : Fintype (ActualAutAmbient iota phi.val) := Fintype.ofFinite _
    ∀ (V : CharacterWeight p K G) (source : CanonicalRawReduction iota V) (hV : V.subgroup = ⊥),
      CommonPairIntermediateBlocks iota phi.val V source
        (actualBase iota phi.val) (actualBaseEquiv iota phi.val hcenter)
        (embeddedNormalizer (innerEmbedding iota phi.val) V.subgroup)
        (embeddedNormalizer_eq_top (innerEmbedding iota phi.val) V.subgroup hV)
        (embeddedLocalBase (innerEmbedding iota phi.val) V.subgroup)
        (normalizerBaseEquiv (innerEmbedding iota phi.val)
          (innerEmbedding_injective iota phi.val hcenter) V.subgroup)

theorem centerless_common_block_output (hcenter : Subgroup.center G = ⊥)
    (hOuter : Nat.card (LiteralOuterQuotient G) = 2)
    (ambient : ∀ phi : FB,
      letI : Fintype (ActualAutAmbient iota phi.val) := Fintype.ofFinite _
      actualBase iota phi.val ≠ ⊤ → UnselectedCatalogue (k := k) (A := ActualAutAmbient iota phi.val)) :
    CenterlessCommonBlockOutput iota hinj R blocks E1 hcenter := by
  intro phi
  let : Fintype (ActualAutAmbient iota phi.val) := Fintype.ofFinite _
  intro V source hV
  apply common_pair_intermediate_blocks iota phi.val V source
    (actualBase iota phi.val) (actualBaseEquiv iota phi.val hcenter)
    (embeddedNormalizer (innerEmbedding iota phi.val) V.subgroup)
    (embeddedNormalizer_eq_top (innerEmbedding iota phi.val) V.subgroup hV)
    (embeddedLocalBase (innerEmbedding iota phi.val) V.subgroup)
    (normalizerBaseEquiv (innerEmbedding iota phi.val)
      (innerEmbedding_injective iota phi.val hcenter) V.subgroup)
    R.1.operations.ambientBlockData
  · exact actual_intermediate_eq_base_or_top iota phi.val hOuter
  · exact ambient phi

section CentralTwo
variable {T C : Type u} [Group T] [Group C]
variable (E : GroupExtension G T C) (hC : Nat.card C = 2)

def CentralTwoCommonBlockOutput : Prop :=
  letI : Finite T := extension_finite E hC
  ∀ phi : FB,
    letI : Fintype (brauerAmbient E iota phi.val) := Fintype.ofFinite _
    ∀ (V : CharacterWeight p K G) (source : CanonicalRawReduction iota V) (hV : V.subgroup = ⊥),
      CommonPairIntermediateBlocks iota phi.val V source
        (brauerEmbedding E iota phi.val).range
        (MonoidHom.ofInjective (brauerEmbedding_injective E iota phi.val))
        (embeddedNormalizer (brauerEmbedding E iota phi.val) V.subgroup)
        (embeddedNormalizer_eq_top (brauerEmbedding E iota phi.val) V.subgroup hV)
        (embeddedLocalBase (brauerEmbedding E iota phi.val) V.subgroup)
        (normalizerBaseEquiv (brauerEmbedding E iota phi.val)
          (brauerEmbedding_injective E iota phi.val) V.subgroup)

theorem central_two_common_block_output
    (ambient : letI : Finite T := extension_finite E hC
      ∀ phi : FB,
        letI : Fintype (brauerAmbient E iota phi.val) := Fintype.ofFinite _
        (brauerEmbedding E iota phi.val).range ≠ ⊤ →
          UnselectedCatalogue (k := k) (A := brauerAmbient E iota phi.val)) :
    CentralTwoCommonBlockOutput iota hinj R blocks E1 E hC := by
  let : Finite T := extension_finite E hC
  intro phi
  let : Fintype (brauerAmbient E iota phi.val) := Fintype.ofFinite _
  intro V source hV
  apply common_pair_intermediate_blocks iota phi.val V source
    (brauerEmbedding E iota phi.val).range
    (MonoidHom.ofInjective (brauerEmbedding_injective E iota phi.val))
    (embeddedNormalizer (brauerEmbedding E iota phi.val) V.subgroup)
    (embeddedNormalizer_eq_top (brauerEmbedding E iota phi.val) V.subgroup hV)
    (embeddedLocalBase (brauerEmbedding E iota phi.val) V.subgroup)
    (normalizerBaseEquiv (brauerEmbedding E iota phi.val)
      (brauerEmbedding_injective E iota phi.val) V.subgroup)
    R.1.operations.ambientBlockData
  · exact brauer_intermediate_eq_base_or_top E iota phi.val hC
  · exact ambient phi

end CentralTwo

def OriginalCommonBlockOutput : Prop :=
  ∀ (phi : FB) (V : CharacterWeight p K G) (source : CanonicalRawReduction iota V) (hV : V.subgroup = ⊥),
    CommonPairIntermediateBlocks iota phi.val V source
      (⊤ : Subgroup G) Subgroup.topEquiv.symm
      (Subgroup.normalizer (V.subgroup : Set G))
      (by rw [hV]; exact Subgroup.normalizer_eq_top (⊥ : Subgroup G))
      (⊤ : Subgroup (Subgroup.normalizer (V.subgroup : Set G))) Subgroup.topEquiv.symm

theorem original_common_block_output :
    OriginalCommonBlockOutput iota hinj R blocks E1 := by
  intro phi V source hV
  apply common_pair_intermediate_blocks iota phi.val V source
    (⊤ : Subgroup G) Subgroup.topEquiv.symm
    (Subgroup.normalizer (V.subgroup : Set G))
    (by rw [hV]; exact Subgroup.normalizer_eq_top (⊥ : Subgroup G))
    (⊤ : Subgroup (Subgroup.normalizer (V.subgroup : Set G))) Subgroup.topEquiv.symm
    R.1.operations.ambientBlockData
  · intro J hJ
    exact Or.inl (top_unique hJ)
  · intro _
    exact ⟨ActualBlock (k := k) (X := G), ⟨R.1.operations.ambientBlockData⟩⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPhysicalQOneBlockRows


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
