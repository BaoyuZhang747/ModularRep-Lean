import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalModelBlockRows
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSameFamilyBlockInduction
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulAD3Assembly

/-! Every raw match of the same family supplies the block law for every
actual retained original-group model pair, including positive radicals. -/

noncomputable section
set_option maxHeartbeats 2000000
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPhysicalOriginalBlockRows

open ModularRep ModularRep.CharacterWeight
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorCarriers
open SporadicFi24P3Definition44NamedCarrierSameFamilyBlockInduction
open SporadicFi24P3Definition44NamedCarrierOriginalModelBlockRows
open SporadicFi24P3Definition44NamedCarrierAssociatedProjectiveModel
open SporadicFi24P3Definition44NamedCarrierFaithfulCenterEquivariantReplacement
open SporadicFi24P3Definition44NamedCarrierPhysicalScalarBindings

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
local notation "FW" => FaithfulWeight iota hinj blocks R E1

def MatchedOriginalModelBlockOutput (e : FB ≃ FW) : Prop :=
  ∀ (phi : FB) (V : CharacterWeight p K G),
    (Quotient.mk'' (Quotient.mk'' V) : ConjugacyClass) = (e phi).val →
    ∀ source : CanonicalRawReduction iota V,
      EveryOriginalModelPairBlocks iota phi.val V source

theorem matched_original_model_block_output (e : FB ≃ FW)
    (hBlocks : MatchedBlockOutput iota hinj R blocks E1 e) :
    MatchedOriginalModelBlockOutput iota hinj R blocks E1 e := by
  intro phi V hmatch source
  let : Fintype (Subgroup.normalizer (V.subgroup : Set G)) := Fintype.ofFinite _
  let D := R.1.operations.inflatedNormalizerBlockData V.subgroup
  let : Fintype (InflatedNormalizerBlock (k := k) V.subgroup) := D.fintypeBlock
  let dataL : AmbientBlockCatalogueData (k := k)
      (G := Subgroup.normalizer (V.subgroup : Set G))
      (Block := InflatedNormalizerBlock (k := k) V.subgroup) := {
    fintypeBlock := D.fintypeBlock
    blockIdempotent := inflatedNormalizerBlockIdempotent (k := k) V.subgroup
    blocks := D.blocks
    catalogue := D.catalogue }
  exact every_original_model_pair_blocks iota phi.val V source hinj
    R.1.operations.ambientBlockData dataL
    ((hBlocks.2 phi V hmatch).2.2 source)

variable (e : FaithfulIBr iota hinj blocks R E1 ≃ FaithfulWeight iota hinj blocks R E1)
variable (phi : FaithfulIBr iota hinj blocks R E1) (V : CharacterWeight p K G)
variable (source : CanonicalRawReduction iota V)
local notation "N" => Subgroup.normalizer (V.subgroup : Set G)
local notation "nu" => brauerSector iota hinj blocks phi.val
local notation "sphi" => scalarBrauer iota hinj blocks phi.val
local notation "rhoG" => globalRepresentation iota nu sphi
local notation "rhoL" => localRepresentation iota V source

/-- The universal output applies to the two literal models in the retained AD3 comparison. -/
theorem retained_original_models_blocks
    (h : MatchedOriginalModelBlockOutput iota hinj R blocks E1 e)
    (hmatch : (Quotient.mk'' (Quotient.mk'' V) : ConjugacyClass) = (e phi).val)
    (MG : AssociatedProjectiveModel (⊤ : Subgroup G) rhoG)
    (ML : AssociatedProjectiveModel (⊤ : Subgroup N) rhoL)
    (hG : GlobalGammaProduct iota nu sphi MG)
    (hL : LocalGammaProduct iota nu V source ML)
    (hMG : MG.factorSet = ScalarFactorSet.trivial)
    (hML : ML.factorSet = ScalarFactorSet.trivial) :
    OriginalModelPairBlocks iota phi.val V source rhoG rhoL MG ML hMG hML :=
  every_original_model_pair_blocks_apply iota phi.val V source
    (h phi V hmatch source) rhoG rhoL MG ML hMG hML hG.1 hG.2.1 hL.1 hL.2.1

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPhysicalOriginalBlockRows


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
