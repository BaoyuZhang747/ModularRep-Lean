import ModularRep.PaperProofs.TypeBQ3PrincipalExtensionApplication

/-!
The fixed pair extension construction on the actual matrix G3 applies to
every supported block. The B2 consumer supplies pair-class invariance from
its constructed matching. One specified idempotent equation and the selected
normalizer reduction identify the base block induction. The cyclic extension
principle constructs both extensions once; the accepted covering and interval
statements then retain those extensions in every intermediate block equation.
The resulting packet is an output of this deduction.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBQ3B2PairExtension

open ModularRep CharacterWeight FDRepSimpleClassKZero
open TypeBQ3TripleCoverCarrier TypeBRankThreePrincipalCountBinding
open TypeBCentralKernelBlockSource
open TypeBCentralKernelTripleCertificate (PhysicalBlocks)
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierActualNormalizerBase
open TypeBQ3PrincipalPairBlockChoice TypeBQ3PrincipalPairBaseInduction
open TypeBQ3PrincipalExtensionApplication
open Representation.Extension NavarroBrauerRestrictionCovering

variable {k K : Type} [Field k] [Field K] [CharP k 2]
  [IsAlgClosed k] [CharZero K]

local instance groupFintype (Y : Type) [Group Y] [Finite Y] : Fintype Y :=
  Fintype.ofFinite Y

local instance twoPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- One literal idempotent identifies the block of the same affording module. -/
theorem supported_character_block
    {Y : Type} [Group Y] [Finite Y]
    (operations : LocalBlockInductionOperations
      (p := 2) (k := k) (K := K) (G := Y) (Block := LiteralPrimitiveBlock k Y))
    (root : PrimeRegularRootEmbedding 2 k K Y)
    (b : LiteralPrimitiveBlock k Y) (phi : IBr root)
    (literalAt : operations.ambientBlockData.blockIdempotent b = b.val)
    (support : Supported root b phi) :
    letI := operations.ambientBlockData.fintypeBlock
    irreducibleBrauerCharacterBlock root
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root)
      operations.ambientBlockData.blocks phi = b := by
  letI := operations.ambientBlockData.fintypeBlock
  obtain ⟨V, hV, hchar, hsupp⟩ := support
  letI : IsSimpleModule k[Y] (Representation.asModule V.ρ) :=
    (Representation.irreducible_iff_isSimpleModule_asModule V.ρ).mp hV
  have hphi : simpleClassToIBr root (simpleClassOfIrreducibleFDRep V hV) = phi := by
    apply Subtype.ext
    change Representation.brauerCharacterOfRootEmbedding
      (simpleClassFDRep (simpleClassOfIrreducibleFDRep V hV)).ρ root = phi.val
    rw [hchar]
    exact Representation.brauerCharacterOfRootEmbedding_iso root
      (simpleClassOfIrreducibleFDRepIso V hV)
  have hblock : irreducibleBrauerCharacterBlock root
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root)
      operations.ambientBlockData.blocks phi =
      operations.ambientBlockData.blocks.moduleBlock
        (V := Representation.asModule V.ρ) := by
    rw [← hphi, irreducibleBrauerCharacterBlock_simpleClassToIBr]
    exact simpleModuleClassBlock_simpleClassOfIrreducibleFDRep
      operations.ambientBlockData.blocks V hV
  rw [hblock]
  symm
  apply operations.ambientBlockData.blocks.moduleBlock_eq_of_smul_eq_self
  intro v
  apply (Representation.asModuleEquiv V.ρ).injective
  rw [Representation.asModuleEquiv_map_smul, literalAt, hsupp]
  rfl

/-- The specified local reduction induces to the block of the supported character. -/
theorem baseBlockInducesTo
    (S : OmegaWeightSource (k := k) (K := K) (ZMod 3))
    (root : PrimeRegularRootEmbedding 2 k K G3)
    (b : LiteralPrimitiveBlock k G3) (phi : IBr root)
    (literalAt : S.operations.ambientBlockData.blockIdempotent b = b.val)
    (brauerSupport : Supported root b phi)
    (W : CharacterWeight 2 K G3)
    (weightSupport : S.operations.rawWeightBlock W = b)
    (reduction : CanonicalRawReduction root W)
    (compatibility :
      NavarroLocalReductionInflationBlockCompatibility.normalizerBrauerBlock
        S.operations W.subgroup reduction.normalizerRoot reduction.localBrauer =
      S.operations.inflateToNormalizer W.subgroup
        (S.operations.localCharacterBlock W.subgroup W.localCharacter W.defectZero)) :
    letI := S.operations.ambientBlockData.fintypeBlock
    letI := (S.operations.inflatedNormalizerBlockData W.subgroup).fintypeBlock
    BlockInducesTo (Subgroup.normalizer (W.subgroup : Set G3))
      (S.operations.inflatedNormalizerBlockData W.subgroup).catalogue
      S.operations.ambientBlockData.catalogue
      (irreducibleBrauerCharacterBlock reduction.normalizerRoot
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding reduction.normalizerRoot)
        (S.operations.inflatedNormalizerBlockData W.subgroup).blocks reduction.localBrauer)
      (irreducibleBrauerCharacterBlock root
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root)
        S.operations.ambientBlockData.blocks phi) := by
  letI := S.operations.ambientBlockData.fintypeBlock
  letI := (S.operations.inflatedNormalizerBlockData W.subgroup).fintypeBlock
  rw [supported_character_block S.operations root b phi literalAt brauerSupport]
  change BlockInducesTo (Subgroup.normalizer (W.subgroup : Set G3))
    (S.operations.inflatedNormalizerBlockData W.subgroup).catalogue
    S.operations.ambientBlockData.catalogue
    (NavarroLocalReductionInflationBlockCompatibility.normalizerBrauerBlock
      S.operations W.subgroup reduction.normalizerRoot reduction.localBrauer) b
  rw [compatibility]
  have supported : S.operations.induceToAmbient W = b := weightSupport
  rw [← supported]
  exact inducedBlock_spec (Subgroup.normalizer (W.subgroup : Set G3))
    (S.operations.inflatedNormalizerBlockData W.subgroup).catalogue
    S.operations.ambientBlockData.catalogue _ (S.operations.blockInductionDefined W)

/-- Construct both extensions once and retain them on every intermediate subgroup. -/
theorem exists_pair_extensions_all_intermediate
    (matrixSource : MatrixExceptionalSource)
    (automorphisms : TypeBQ3TripleCoverAutomorphisms.MatrixAutomorphismSource)
    (indexTwo : (G (ZMod 3)).index = 2)
    (S : OmegaWeightSource (k := k) (K := K) (ZMod 3))
    (root : PrimeRegularRootEmbedding 2 k K G3)
    (b : LiteralPrimitiveBlock k G3) (phi : IBr root)
    (literalAt : S.operations.ambientBlockData.blockIdempotent b = b.val)
    (brauerSupport : Supported root b phi)
    (W : CharacterWeight 2 K G3)
    (weightSupport : S.operations.rawWeightBlock W = b)
    (pairFixed : ∀ alpha : MulAut G3,
      MulOpposite.op alpha • phi = phi →
        MulOpposite.op alpha • TypeBQ3PrincipalPairExtensions.rawClass W =
          TypeBQ3PrincipalPairExtensions.rawClass W)
    (reduction : CanonicalRawReduction root W)
    (compatibility :
      NavarroLocalReductionInflationBlockCompatibility.normalizerBrauerBlock
        S.operations W.subgroup reduction.normalizerRoot reduction.localBrauer =
      S.operations.inflateToNormalizer W.subgroup
        (S.operations.localCharacterBlock W.subgroup W.localCharacter W.defectZero))
    (ambientBlocks : PhysicalBlocks k (ActualAutAmbient root phi))
    (localBlocks : PhysicalBlocks k
      (embeddedNormalizer (innerEmbedding root phi) W.subgroup))
    (principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} 2 k)
    (ambientSeed : PrimeRegularRootEmbedding 2 k K (ActualAutAmbient root phi))
    (fieldSource : SpathCoefficientField 2 k Nat.prime_two)
    (S9295 : Navarro9295BrauerRestrictionCoveringPrinciple 2 k K)
    (S96 : Navarro96PGroupCoveringUniquenessPrinciple 2 k)
    (S414 : letI := localBlocks.blockFintype
      Navarro414IntervalCentralCharacterSource (embeddedRadicalInterval root phi W)
        localBlocks.decomposition localBlocks.catalogue) :
    Nonempty (MatchedExtensionData root phi W reduction
      (TypeBQ3PrincipalInertiaQuotient.center_eq_bot matrixSource)) := by
  let hcenter := TypeBQ3PrincipalInertiaQuotient.center_eq_bot matrixSource
  let A := ActualAutAmbient root phi
  let B := actualBase root phi
  let D := embeddedNormalizer (innerEmbedding root phi) W.subgroup
  let eG := actualBaseEquiv root phi hcenter
  let eN := normalizerBaseEquiv (innerEmbedding root phi)
    (innerEmbedding_injective root phi hcenter) W.subgroup
  have bound : Nat.card (A ⧸ B) ≤ 2 :=
    TypeBQ3PrincipalInertiaQuotient.actual_quotient_card_le_two
      automorphisms indexTwo root phi
  obtain ⟨rA, rD, globalExt, localExt, globalAgreement, localAgreement⟩ :=
    TypeBQ3PrincipalPairExtensions.exists_pair_extensions root phi W pairFixed
      reduction hcenter bound principle ambientSeed
  letI := S.operations.ambientBlockData.fintypeBlock
  letI := (S.operations.inflatedNormalizerBlockData W.subgroup).fintypeBlock
  letI := ambientBlocks.blockFintype
  letI := localBlocks.blockFintype
  have square := baseSquare_of_localEmbedding
    (Subgroup.normalizer (W.subgroup : Set G3)) B D eG eN (fun _ => rfl)
  have baseInduction := baseBlockInducesTo S root b phi literalAt brauerSupport
    W weightSupport reduction compatibility
  let intermediate := allIntermediateBlockData
    (Subgroup.normalizer (W.subgroup : Set G3)) B D eG eN square
    root reduction.normalizerRoot rA rD
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root)
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding reduction.normalizerRoot)
    S.operations.ambientBlockData.blocks
    (S.operations.inflatedNormalizerBlockData W.subgroup).blocks
    ambientBlocks.decomposition localBlocks.decomposition
    S.operations.ambientBlockData.catalogue
    (S.operations.inflatedNormalizerBlockData W.subgroup).catalogue
    ambientBlocks.catalogue localBlocks.catalogue
    phi reduction.localBrauer globalExt localExt globalAgreement localAgreement
    fieldSource (inertia_isTwoGroup root phi bound) bound
    (W.subgroup.map (innerEmbedding root phi)) (embeddedRadicalInterval root phi W)
    S414 S9295 S96 baseInduction
  exact ⟨⟨rA, rD, globalExt, localExt, globalAgreement, localAgreement, intermediate⟩⟩

end ModularRep.PaperProofs.TypeBQ3B2PairExtension


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
