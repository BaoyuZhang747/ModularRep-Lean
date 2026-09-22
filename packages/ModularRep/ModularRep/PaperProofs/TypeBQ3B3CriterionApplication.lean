import ModularRep.PaperProofs.TypeBQ3B3DownstairsMatching
import ModularRep.PaperProofs.TypeBQ3B3DefectImage
import ModularRep.PaperProofs.TypeBQ3B3NilpotentWeights
import ModularRep.PaperProofs.TypeBQ3B2CentralQuotient
import ModularRep.PaperProofs.TypeBQ3B2RootDescent
import ModularRep.PaperProofs.TypeBQ3B2CriterionFinish

/-!
The B3 deduction on the actual central character quotient of the retained
triple cover. The complete table dictionary supplies the single supported
Brauer character L15; local ordinary-character facts at the actual order-two
defect group supply the weight singleton through the checked conjugacy and
normalizer-quotient constructions. Their intrinsic matching graph is proved.
The existing nonprincipal extension construction supplies the complete criterion
with the same selected raw representatives at every intermediate subgroup.

The cyclic-defect iBAW theorem is not an input. No matching, weight singleton,
global outer-action assertion, or equivalent criterion is an external input.
All specified table, local block, reduction and extension sources remain
explicit on the constructed carriers.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBQ3B3CriterionApplication

open ModularRep CharacterWeight FDRepSimpleClassKZero
open TypeBQ3TripleCoverCarrier TypeBRankThreePrincipalCountBinding
open TypeBCentralKernelBlockSource TypeBCentralKernelInertia
open TypeBQ3PrincipalWeightInflation TypeBQ3PrincipalCriterionDominatedBlock
open TypeBExceptionalQ3Proposition416Actual
open TypeBLocalReductionInstantiation TypeBFixedRootDefinitionFamily
open TypeBQ3FaithfulLocalReduction TypeBQ3B2CriterionFinish
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open SporadicFi24P3Definition44NamedCarrierQuotientBlockAlgebra
open Formalisation.ComputationArithmetic

variable (matrixSource : MatrixExceptionalSource)
  (freeSource : TypeBExceptionalCanonicalCover.FreePresentationCoverSource)

local instance groupFintype (Y : Type) [Group Y] [Finite Y] : Fintype Y :=
  Fintype.ofFinite Y
local instance twoPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {k K O : Type}
  [Field k] [Field K] [CommRing O] [IsDomain O] [Algebra O K]
  [CharP k 2] [IsAlgClosed k] [CharZero K]

/-- The actual B3 central quotient and complete fixed-block criterion,
relative only to the displayed specified and published subordinate sources. -/
theorem actualTripleCover_B3_criterion :
  letI : Finite X := finite_X matrixSource
  ∀ (root : PrimeRegularRootEmbedding 2 k K X)
    (Msys : ModularSystem 2 K O k)
    (calibration : RootResidueCompatible Msys root)
    [ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card X)]
    (d : Q3Block → k[X]) (blocks : BlockIdempotentDecomposition d)
    (D : Subgroup X)
    (defect : Navarro411DefectRepresentative (p := 2) blocks .B3 D)
    (cardD : Nat.card D = 2)
    (brauerMap : LiteralBrauerOutputMap root)
    (map_injective : Function.Injective brauerMap.character)
    (map_surjective : Function.Surjective brauerMap.character)
    (compatible : BrauerBlockFibreCompatible root
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root) blocks brauerMap)
    (sectorOne : centralSector matrixSource freeSource
      (primitiveBlockOfLabel blocks .B3) = 1)
    (R : OmegaWeightSource (k := k) (K := K) (ZMod 3))
    (primitive : CentralPrimeToPrimitiveImageSource (k := k)
      (q matrixSource freeSource) (q_surjective matrixSource freeSource) root.prime
      (q_kernel_le_center matrixSource freeSource) (q_kernel_primeToTwo matrixSource freeSource)),
    let rootDown := TypeBQ3B2CentralQuotient.downRoot matrixSource freeSource root
    letI := TypeBQ3B2RootDescent.downOrdinaryRoots (K := K) matrixSource freeSource
    let calibrationDown :=
      TypeBQ3B2RootDescent.downRoot_residue matrixSource freeSource root Msys calibration
    ∃ (b : LiteralPrimitiveBlock k G3)
      (image : algebraMapOf (q matrixSource freeSource) (d .B3) = b.val)
      (deflation : BrauerFibre root (primitiveBlockOfLabel blocks .B3) ≃ BrauerFibre rootDown b),
      (∀ phi : BrauerFibre root (primitiveBlockOfLabel blocks .B3),
        PrimeRegularClassFunction.pullback (q matrixSource freeSource)
          (deflation phi).val.val = phi.val.val) ∧
      (∀ phi : BrauerFibre root (primitiveBlockOfLabel blocks .B3),
        TypeBBSCentralCharacterQuotient.centralKernel root phi.val =
          (q matrixSource freeSource).ker) ∧
      (∀ phi : BrauerFibre root (primitiveBlockOfLabel blocks .B3),
        ∃ e : TypeBQ3PrincipalExtensionCentralQuotient.CentralQuotient root
            (primitiveBlockOfLabel blocks .B3) phi ≃* G3,
          (∀ x : X, e (QuotientGroup.mk'
            (TypeBBSCentralCharacterQuotient.centralKernel root phi.val) x) =
              q matrixSource freeSource x) ∧
          (TypeBQ3PrincipalExtensionCentralQuotient.quotientBrauer root
            (primitiveBlockOfLabel blocks .B3) phi).val =
            PrimeRegularClassFunction.pullback e.toMonoidHom (deflation phi).val.val) ∧
      Nat.card (BrauerFibre rootDown b) = 1 ∧
      Nat.card (D.map (q matrixSource freeSource)) = 2 ∧
      ∀ (ambientAt : R.operations.ambientBlockData.blockIdempotent b = b.val)
        (defectImage : TypeBQ3B3DefectImage.Navarro99cDefectImageSource
          matrixSource freeSource blocks D defect R b ambientAt image)
        (navarro : ∀ W : CharacterWeight 2 K G3,
          letI := localOrdinaryRoots (K := K) W.subgroup
          ScopedDefectZeroReductionSource Msys (localQuotientRoot rootDown W.subgroup)
            (localRoot_residueCanonical Msys rootDown calibrationDown W.subgroup))
        (physical : GuardedBlockCompatibility rootDown R.operations)
        (localSource : TypeBQ3B3NilpotentWeights.LocalSource
          Msys rootDown calibrationDown navarro R physical b ambientAt
          (D.map (q matrixSource freeSource))
          (TypeBQ3B3DefectImage.mappedDefect
            matrixSource freeSource blocks D defect R b ambientAt image defectImage)
          (TypeBQ3B3DefectImage.mappedDefect_card_two
            matrixSource freeSource blocks D defect cardD))
        (automorphisms : TypeBQ3TripleCoverAutomorphisms.MatrixAutomorphismSource)
        (indexTwo : (G (ZMod 3)).index = 2),
        ∃ omega : BrauerFibre rootDown b ≃ R.Fibre b,
          Nat.card (R.Fibre b) = 1 ∧ PhysicalExtensionConclusion rootDown R b omega := by
  letI : Finite X := finite_X matrixSource
  intro root Msys calibration ordinaryRoots d blocks D defect cardD brauerMap
    map_injective map_surjective compatible sectorOne R primitive
  let bX := primitiveBlockOfLabel blocks .B3
  letI : Fintype (LiteralPrimitiveBlock k X) := TypeBLiteralBlockReindex.literalBlockFintype blocks
  letI : Fintype (LiteralPrimitiveBlock k G3) := R.operations.ambientBlockData.fintypeBlock
  let DX := TypeBLiteralBlockReindex.literalBlocks blocks
  let DB := TypeBLiteralBlockReindex.literalBlocks R.operations.ambientBlockData.blocks
  let rootDown := TypeBQ3B2CentralQuotient.downRoot matrixSource freeSource root
  letI := TypeBQ3B2RootDescent.downOrdinaryRoots (K := K) matrixSource freeSource
  let calibrationDown :=
    TypeBQ3B2RootDescent.downRoot_residue matrixSource freeSource root Msys calibration
  let reference : BrauerFibre root bX :=
    TypeBQ3B3DownstairsMatching.reference root blocks brauerMap compatible
  have cardUp : Nat.card (BrauerFibre root bX) = 1 :=
    TypeBQ3B3DownstairsMatching.brauer_card root blocks brauerMap
      map_injective map_surjective compatible
  let b := TypeBQ3B2CentralQuotient.downBlock matrixSource freeSource root DX bX
    sectorOne DB reference primitive
  have image : algebraMapOf (q matrixSource freeSource) (d .B3) = b.val := rfl
  let deflation := TypeBQ3B2CentralQuotient.brauerDeflation matrixSource freeSource
    root DX bX sectorOne DB reference primitive
  have cardDown : Nat.card (BrauerFibre rootDown b) = 1 :=
    (Nat.card_congr deflation.symm).trans cardUp
  have defectCardDown :=
    TypeBQ3B3DefectImage.mappedDefect_card_two matrixSource freeSource blocks D defect cardD
  refine ⟨b, image, deflation, ?_, ?_, ?_, cardDown, defectCardDown, ?_⟩
  · exact TypeBQ3B2CentralQuotient.brauerDeflation_pullback
      matrixSource freeSource root DX bX sectorOne DB reference primitive
  · exact TypeBQ3B2CentralQuotient.centralKernel_eq_qker
      matrixSource freeSource root DX bX sectorOne
  · intro phi
    exact ⟨TypeBQ3B2CentralQuotient.centralQuotientEquiv
      matrixSource freeSource root DX bX sectorOne phi,
      TypeBQ3B2CentralQuotient.centralQuotientEquiv_mk
        matrixSource freeSource root DX bX sectorOne phi,
      TypeBQ3B2CentralQuotient.quotientBrauer_eq_pullback_deflation
        matrixSource freeSource root DX bX sectorOne DB reference primitive phi⟩
  · intro ambientAt defectImage navarro physical localSource automorphisms indexTwo
    let downDefect := TypeBQ3B3DefectImage.mappedDefect
      matrixSource freeSource blocks D defect R b ambientAt image defectImage
    have weightCard := TypeBQ3B3NilpotentWeights.weight_fibre_card_one
      Msys rootDown calibrationDown navarro R physical b ambientAt
      (D.map (q matrixSource freeSource)) downDefect defectCardDown localSource
    obtain ⟨omega, graph⟩ := TypeBQ3B3DownstairsMatching.exists_equivariant_matching
      rootDown R b cardDown weightCard
    exact ⟨omega, weightCard,
      TypeBQ3B2CriterionFinish.of_matching rootDown R b matrixSource
        automorphisms indexTwo Msys calibrationDown navarro physical ambientAt omega graph⟩

end ModularRep.PaperProofs.TypeBQ3B3CriterionApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
