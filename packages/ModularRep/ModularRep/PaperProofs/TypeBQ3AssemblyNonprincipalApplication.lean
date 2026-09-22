import ModularRep.PaperProofs.TypeBQ3AssemblyBranchSources
import ModularRep.PaperProofs.TypeBQ3AssemblyQuotientPresentation

/-!
The B2 and B3 applications are invoked on their original specified sources.
Their constructed lower block, complete deflation, matching and selected
representatives are retained. Only the specified extension catalogues at
those selected pairs remain before the natural quotient witness is returned.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBQ3AssemblyNonprincipalApplication

open ModularRep CharacterWeight FDRepSimpleClassKZero
open TypeBQ3TripleCoverCarrier TypeBRankThreePrincipalCountBinding
open TypeBCentralKernelBlockSource TypeBCentralKernelInertia
open TypeBCentralKernelTripleCertificate (PhysicalBlocks)
open TypeBQ3PrincipalWeightInflation TypeBQ3PrincipalCriterionDominatedBlock
open TypeBExceptionalQ3Proposition416Actual
open TypeBFixedRootDefinitionFamily TypeBLocalReductionInstantiation
open TypeBQ3FaithfulLocalReduction TypeBQ3PrincipalPairBlockChoice
open TypeBQ3AssemblyBranchSources TypeBQ3AssemblyQuotientPresentation
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierActualNormalizerBase
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open SporadicFi24P3Definition44NamedCarrierQuotientBlockAlgebra
open Representation.Extension NavarroBrauerRestrictionCovering
open Formalisation.ComputationArithmetic

variable {k K : Type} [Field k] [Field K] [CharP k 2]
  [IsAlgClosed k] [CharZero K]

local instance groupFintype (Y : Type) [Group Y] [Finite Y] : Fintype Y :=
  Fintype.ofFinite Y

local instance twoPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Specified inputs only at the representatives selected by the matching. -/
structure ExtensionCatalogues
    (root : PrimeRegularRootEmbedding 2 k K G3)
    (R : OmegaWeightSource (k := k) (K := K) (ZMod 3))
    (b : LiteralPrimitiveBlock k G3)
    (selected : (phi : BrauerFibre root b) →
      {W : CharacterWeight 2 K G3 // R.operations.rawWeightBlock W = b}) where
  ambientBlocks : ∀ phi : BrauerFibre root b,
    PhysicalBlocks k (ActualAutAmbient root phi.val)
  localBlocks : ∀ phi : BrauerFibre root b, PhysicalBlocks k
    (embeddedNormalizer (innerEmbedding root phi.val) (selected phi).val.subgroup)
  ambientSeed : ∀ phi : BrauerFibre root b,
    PrimeRegularRootEmbedding 2 k K (ActualAutAmbient root phi.val)
  S414 : ∀ phi : BrauerFibre root b,
    letI := (localBlocks phi).blockFintype
    Navarro414IntervalCentralCharacterSource
      (TypeBQ3PrincipalPairBaseInduction.embeddedRadicalInterval
        root phi.val (selected phi).val)
      (localBlocks phi).decomposition (localBlocks phi).catalogue

/-- Normalize the already constructed specified extension stage without
changing its lower block, deflation, matching or selected representatives. -/
theorem of_physicalExtensionConclusion
    (matrixSource : MatrixExceptionalSource)
    (freeSource : TypeBExceptionalCanonicalCover.FreePresentationCoverSource)
    [Finite X]
    (rootX : PrimeRegularRootEmbedding 2 k K X)
    (bX : LiteralPrimitiveBlock k X)
    (sectorOne : centralSector matrixSource freeSource bX = 1)
    (rootDown : PrimeRegularRootEmbedding 2 k K G3)
    (R : OmegaWeightSource (k := k) (K := K) (ZMod 3))
    (b : LiteralPrimitiveBlock k G3)
    (image : algebraMapOf (q matrixSource freeSource) bX.val = b.val)
    (deflation : BrauerFibre rootX bX ≃ BrauerFibre rootDown b)
    (pullback : ∀ phi : BrauerFibre rootX bX,
      PrimeRegularClassFunction.pullback (q matrixSource freeSource)
        (deflation phi).val.val = phi.val.val)
    (ownKernel : ∀ phi : BrauerFibre rootX bX,
      TypeBBSCentralCharacterQuotient.centralKernel rootX phi.val =
        (q matrixSource freeSource).ker)
    (omega : BrauerFibre rootDown b ≃ CoverWeight R b)
    (extension : TypeBQ3B2CriterionFinish.PhysicalExtensionConclusion rootDown R b omega)
    (principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} 2 k)
    (fieldSource : SpathCoefficientField 2 k Nat.prime_two)
    (S9295 : Navarro9295BrauerRestrictionCoveringPrinciple 2 k K)
    (S96 : Navarro96PGroupCoveringUniquenessPrinciple 2 k) :
    ∃ selected : (phi : BrauerFibre rootDown b) →
        {W : CharacterWeight 2 K G3 // R.operations.rawWeightBlock W = b},
      ∀ catalogues : ExtensionCatalogues rootDown R b selected,
        Nonempty (Witness matrixSource freeSource rootX bX
          (q matrixSource freeSource) rootDown R) := by
  refine Exists.elim extension ?_
  intro selected selectedData
  refine ⟨selected, ?_⟩
  intro catalogues
  exact ⟨{
    surjective := q_surjective matrixSource freeSource
    kernel_eq_common :=
      (TypeBQ3B2CentralQuotient.sectorKernel_eq_qker
        matrixSource freeSource bX sectorOne).symm
    downBlock := b
    block_image := image
    deflation := deflation
    deflation_pullback := pullback
    ownKernel_eq := ownKernel
    centralFaithful := TypeBQ3AssemblyQuotientPresentation.centralFaithful_G3
      matrixSource rootDown b
    matching := omega
    clauses := TypeBQ3AssemblyCriterionData.of_b2 rootDown R b omega
      (selectedData.2 catalogues.ambientBlocks catalogues.localBlocks
        principle catalogues.ambientSeed fieldSource S9295 S96 catalogues.S414)
  }⟩

variable {O : Type} [CommRing O] [IsDomain O] [Algebra O K]

/-- The sealed B2 application supplies the constructed block and all
matching data before sources on that block and its selected pairs are used. -/
theorem b2_criterion
    (matrixSource : MatrixExceptionalSource)
    (freeSource : TypeBExceptionalCanonicalCover.FreePresentationCoverSource)
    (automorphisms : TypeBQ3TripleCoverAutomorphisms.MatrixAutomorphismSource)
    (indexTwo : (G (ZMod 3)).index = 2)
    (principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} 2 k)
    (fieldSource : SpathCoefficientField 2 k Nat.prime_two)
    (S9295 : Navarro9295BrauerRestrictionCoveringPrinciple 2 k K)
    (S96 : Navarro96PGroupCoveringUniquenessPrinciple 2 k) :
    letI : Finite X := finite_X matrixSource
    ∀ (root : PrimeRegularRootEmbedding 2 k K X)
      (Msys : ModularSystem 2 K O k)
      (calibration : RootResidueCompatible Msys root)
      [ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card X)]
      (d : Q3Block → k[X]) (blocks : BlockIdempotentDecomposition d)
      (brauerMap : LiteralBrauerOutputMap root)
      (map_injective : Function.Injective brauerMap.character)
      (map_surjective : Function.Surjective brauerMap.character)
      (compatible : BrauerBlockFibreCompatible root
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root) blocks brauerMap)
      (R : OmegaWeightSource (k := k) (K := K) (ZMod 3))
      (primitive : CentralPrimeToPrimitiveImageSource (k := k)
        (q matrixSource freeSource) (q_surjective matrixSource freeSource) root.prime
        (q_kernel_le_center matrixSource freeSource) (q_kernel_primeToTwo matrixSource freeSource))
      (before : B2Before matrixSource freeSource root Msys calibration blocks brauerMap),
      let rootDown := TypeBQ3B2CentralQuotient.downRoot matrixSource freeSource root
      letI := TypeBQ3B2RootDescent.downOrdinaryRoots (K := K) matrixSource freeSource
      let calibrationDown :=
        TypeBQ3B2RootDescent.downRoot_residue matrixSource freeSource root Msys calibration
      ∃ (b : LiteralPrimitiveBlock k G3)
        (image : algebraMapOf (q matrixSource freeSource) (d .B2) = b.val),
        ∀ (ambientAt : R.operations.ambientBlockData.blockIdempotent b = b.val)
          (navarro : ∀ W : CharacterWeight 2 K G3,
            letI := localOrdinaryRoots (K := K) W.subgroup
            ScopedDefectZeroReductionSource Msys (localQuotientRoot rootDown W.subgroup)
              (localRoot_residueCanonical Msys rootDown calibrationDown W.subgroup))
          (physical : GuardedBlockCompatibility rootDown R.operations)
          (after : B2After matrixSource freeSource Msys rootDown calibrationDown
            blocks before.D before.defect R b ambientAt image navarro physical),
          ∃ selected : (phi : BrauerFibre rootDown b) →
              {W : CharacterWeight 2 K G3 // R.operations.rawWeightBlock W = b},
            ∀ catalogues : ExtensionCatalogues rootDown R b selected,
              Nonempty (Witness matrixSource freeSource root
                (primitiveBlockOfLabel blocks .B2) (q matrixSource freeSource) rootDown R) := by
  letI : Finite X := finite_X matrixSource
  intro root Msys calibration ordinaryRoots d blocks brauerMap map_injective
    map_surjective compatible R primitive before
  let rootDown := TypeBQ3B2CentralQuotient.downRoot matrixSource freeSource root
  letI := TypeBQ3B2RootDescent.downOrdinaryRoots (K := K) matrixSource freeSource
  let calibrationDown :=
    TypeBQ3B2RootDescent.downRoot_residue matrixSource freeSource root Msys calibration
  have previous := TypeBQ3B2CriterionApplication.actualTripleCover_B2_criterion
    matrixSource freeSource root Msys calibration d blocks before.ordinary
    before.D before.defect before.table before.classification before.heightZero
    before.quaternion brauerMap map_injective map_surjective compatible
    before.outerClass before.outer before.outer_nontrivial before.outerClass_ker
    before.outerValues before.sectorOne R primitive
  refine Exists.elim previous ?_
  intro b imageData
  refine Exists.elim imageData ?_
  intro image deflationData
  refine Exists.elim deflationData ?_
  intro deflation data
  refine ⟨b, image, ?_⟩
  intro ambientAt navarro physical after
  have finished := data.2.2.2.2.2 ambientAt after.defectImage navarro physical
    after.census automorphisms indexTwo
  refine Exists.elim finished ?_
  intro omega extension
  exact of_physicalExtensionConclusion matrixSource freeSource root
    (primitiveBlockOfLabel blocks .B2) before.sectorOne rootDown R b image
    deflation data.1 data.2.1 omega extension principle fieldSource S9295 S96

/-- The sealed B3 application supplies its singleton matching from local
ordinary-character facts, then retains the same specified extension stage. -/
theorem b3_criterion
    (matrixSource : MatrixExceptionalSource)
    (freeSource : TypeBExceptionalCanonicalCover.FreePresentationCoverSource)
    (automorphisms : TypeBQ3TripleCoverAutomorphisms.MatrixAutomorphismSource)
    (indexTwo : (G (ZMod 3)).index = 2)
    (principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} 2 k)
    (fieldSource : SpathCoefficientField 2 k Nat.prime_two)
    (S9295 : Navarro9295BrauerRestrictionCoveringPrinciple 2 k K)
    (S96 : Navarro96PGroupCoveringUniquenessPrinciple 2 k) :
    letI : Finite X := finite_X matrixSource
    ∀ (root : PrimeRegularRootEmbedding 2 k K X)
      (Msys : ModularSystem 2 K O k)
      (calibration : RootResidueCompatible Msys root)
      [ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card X)]
      (d : Q3Block → k[X]) (blocks : BlockIdempotentDecomposition d)
      (brauerMap : LiteralBrauerOutputMap root)
      (map_injective : Function.Injective brauerMap.character)
      (map_surjective : Function.Surjective brauerMap.character)
      (compatible : BrauerBlockFibreCompatible root
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root) blocks brauerMap)
      (R : OmegaWeightSource (k := k) (K := K) (ZMod 3))
      (primitive : CentralPrimeToPrimitiveImageSource (k := k)
        (q matrixSource freeSource) (q_surjective matrixSource freeSource) root.prime
        (q_kernel_le_center matrixSource freeSource) (q_kernel_primeToTwo matrixSource freeSource))
      (before : B3Before matrixSource freeSource blocks),
      let rootDown := TypeBQ3B2CentralQuotient.downRoot matrixSource freeSource root
      letI := TypeBQ3B2RootDescent.downOrdinaryRoots (K := K) matrixSource freeSource
      let calibrationDown :=
        TypeBQ3B2RootDescent.downRoot_residue matrixSource freeSource root Msys calibration
      ∃ (b : LiteralPrimitiveBlock k G3)
        (image : algebraMapOf (q matrixSource freeSource) (d .B3) = b.val),
        ∀ (ambientAt : R.operations.ambientBlockData.blockIdempotent b = b.val)
          (navarro : ∀ W : CharacterWeight 2 K G3,
            letI := localOrdinaryRoots (K := K) W.subgroup
            ScopedDefectZeroReductionSource Msys (localQuotientRoot rootDown W.subgroup)
              (localRoot_residueCanonical Msys rootDown calibrationDown W.subgroup))
          (physical : GuardedBlockCompatibility rootDown R.operations)
          (after : B3After matrixSource freeSource Msys rootDown calibrationDown
            blocks before.D before.defect before.cardD R b ambientAt image navarro physical),
          ∃ selected : (phi : BrauerFibre rootDown b) →
              {W : CharacterWeight 2 K G3 // R.operations.rawWeightBlock W = b},
            ∀ catalogues : ExtensionCatalogues rootDown R b selected,
              Nonempty (Witness matrixSource freeSource root
                (primitiveBlockOfLabel blocks .B3) (q matrixSource freeSource) rootDown R) := by
  letI : Finite X := finite_X matrixSource
  intro root Msys calibration ordinaryRoots d blocks brauerMap map_injective
    map_surjective compatible R primitive before
  let rootDown := TypeBQ3B2CentralQuotient.downRoot matrixSource freeSource root
  letI := TypeBQ3B2RootDescent.downOrdinaryRoots (K := K) matrixSource freeSource
  let calibrationDown :=
    TypeBQ3B2RootDescent.downRoot_residue matrixSource freeSource root Msys calibration
  have previous := TypeBQ3B3CriterionApplication.actualTripleCover_B3_criterion
    matrixSource freeSource root Msys calibration d blocks before.D before.defect
    before.cardD brauerMap map_injective map_surjective compatible
    before.sectorOne R primitive
  refine Exists.elim previous ?_
  intro b imageData
  refine Exists.elim imageData ?_
  intro image deflationData
  refine Exists.elim deflationData ?_
  intro deflation data
  refine ⟨b, image, ?_⟩
  intro ambientAt navarro physical after
  have finished := data.2.2.2.2.2 ambientAt after.defectImage navarro physical
    after.localSource automorphisms indexTwo
  refine Exists.elim finished ?_
  intro omega extensionData
  exact of_physicalExtensionConclusion matrixSource freeSource root
    (primitiveBlockOfLabel blocks .B3) before.sectorOne rootDown R b image
    deflation data.1 data.2.1 omega extensionData.2 principle fieldSource S9295 S96

end ModularRep.PaperProofs.TypeBQ3AssemblyNonprincipalApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
