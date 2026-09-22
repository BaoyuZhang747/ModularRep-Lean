import ModularRep.PaperProofs.TypeBQ3B2Matching
import ModularRep.PaperProofs.TypeBQ3B2CentralQuotient
import ModularRep.PaperProofs.TypeBQ3B2AutomorphismLift
import ModularRep.PaperProofs.TypeBQ3B2DefectDescent
import ModularRep.PaperProofs.TypeBQ3B2DownstairsWeights
import ModularRep.PaperProofs.TypeBQ3B2DownstairsMatching
import ModularRep.PaperProofs.TypeBQ3B2RootDescent
import ModularRep.PaperProofs.TypeBQ3B2CriterionFinish
import ModularRep.PaperProofs.TypeBQ3FaithfulFibreBinding

/-!
The B2 criterion is combined on its actual dominated block of matrix G3.
The block and reference character are constructed before the exact downstairs
defect and census sources are supplied. The upstream D8 deduction is reused
directly, with no upstairs weight catalogue or quotient-weight correspondence.
All specified extension sources remain scoped to the selected matched pairs.
The numbered result, criterion, matching and extension data are outputs.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBQ3B2CriterionApplication

open ModularRep CharacterWeight
open TypeBQ3TripleCoverCarrier TypeBRankThreePrincipalCountBinding
open TypeBCentralKernelBlockSource TypeBCentralKernelInertia
open TypeBQ3PrincipalWeightInflation TypeBQ3PrincipalCriterionDominatedBlock
open TypeBExceptionalQ3Proposition416Actual
open TypeBExceptionalQ3Proposition416Relative
open TypeBLocalReductionInstantiation TypeBFixedRootDefinitionFamily
open TypeBQ3FaithfulLocalReduction TypeBQ3B2DihedralDefect
open TypeBQ3B2CriterionFinish
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open SporadicFi24P3Definition44NamedCarrierQuotientBlockAlgebra
open Formalisation.ComputationArithmetic
open FDRepSimpleClassKZero

variable (matrixSource : MatrixExceptionalSource)
  (freeSource : TypeBExceptionalCanonicalCover.FreePresentationCoverSource)

local instance groupFintype (Y : Type) [Group Y] [Finite Y] : Fintype Y :=
  Fintype.ofFinite Y
local instance twoPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {k K O : Type}
  [Field k] [Field K] [CommRing O] [IsDomain O] [Algebra O K]
  [CharP k 2] [IsAlgClosed k] [CharZero K]

/-- The specified B2 deduction, including its central quotient and complete
criterion on the literal dominated block, relative to the displayed sources. -/
theorem actualTripleCover_B2_criterion :
  letI : Finite X := finite_X matrixSource
  ∀ (root : PrimeRegularRootEmbedding 2 k K X)
    (Msys : ModularSystem 2 K O k)
    (calibration : RootResidueCompatible Msys root)
    [ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card X)]
    (d : Q3Block → k[X]) (blocks : BlockIdempotentDecomposition d)
    (ordinary : PhysicalOrdinarySource blocks Msys root
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root))
    (D : Subgroup X)
    (defect : Navarro411DefectRepresentative (p := 2) blocks .B2 D)
    (table : PhysicalTableSource blocks Msys root
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root) ordinary D)
    (classification : OrderEightClassificationSource D)
    (heightZero : AbelianHeightZeroSource blocks Msys root calibration
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root) ordinary D defect)
    (quaternion : QuaternionTwoBrauerSource blocks Msys root calibration
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root) ordinary D defect)
    (brauerMap : LiteralBrauerOutputMap root)
    (map_injective : Function.Injective brauerMap.character)
    (map_surjective : Function.Surjective brauerMap.character)
    (compatible : BrauerBlockFibreCompatible root
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root) blocks brauerMap)
    (outerClass : (MulAut X)ᵐᵒᵖ →* Equiv.Perm (Fin 2))
    (outer : (MulAut X)ᵐᵒᵖ)
    (outer_nontrivial : outerClass outer ≠ 1)
    (outerClass_ker : outerClass.ker =
      (RepresentationWeight.innerInverseOpHom (G := X)).range)
    (outerValues : TypeBQ3B2Matching.B2OuterBrauerActionSource root brauerMap outer)
    (sectorOne : centralSector matrixSource freeSource (primitiveBlockOfLabel blocks .B2) = 1)
    (R : OmegaWeightSource (k := k) (K := K) (ZMod 3))
    (primitive : CentralPrimeToPrimitiveImageSource (k := k)
      (q matrixSource freeSource) (q_surjective matrixSource freeSource) root.prime
      (q_kernel_le_center matrixSource freeSource) (q_kernel_primeToTwo matrixSource freeSource)),
    let rootDown := TypeBQ3B2CentralQuotient.downRoot matrixSource freeSource root
    letI := TypeBQ3B2RootDescent.downOrdinaryRoots (K := K) matrixSource freeSource
    let calibrationDown :=
      TypeBQ3B2RootDescent.downRoot_residue matrixSource freeSource root Msys calibration
    ∃ (b : LiteralPrimitiveBlock k G3)
      (image : algebraMapOf (q matrixSource freeSource) (d .B2) = b.val)
      (deflation : BrauerFibre root (primitiveBlockOfLabel blocks .B2) ≃ BrauerFibre rootDown b),
      (∀ phi : BrauerFibre root (primitiveBlockOfLabel blocks .B2),
        PrimeRegularClassFunction.pullback (q matrixSource freeSource)
          (deflation phi).val.val = phi.val.val) ∧
      (∀ phi : BrauerFibre root (primitiveBlockOfLabel blocks .B2),
        TypeBBSCentralCharacterQuotient.centralKernel root phi.val =
          (q matrixSource freeSource).ker) ∧
      (∀ phi : BrauerFibre root (primitiveBlockOfLabel blocks .B2),
        ∃ e : TypeBQ3PrincipalExtensionCentralQuotient.CentralQuotient root
            (primitiveBlockOfLabel blocks .B2) phi ≃* G3,
          (∀ x : X, e (QuotientGroup.mk'
            (TypeBBSCentralCharacterQuotient.centralKernel root phi.val) x) =
              q matrixSource freeSource x) ∧
          (TypeBQ3PrincipalExtensionCentralQuotient.quotientBrauer root
            (primitiveBlockOfLabel blocks .B2) phi).val =
            PrimeRegularClassFunction.pullback e.toMonoidHom (deflation phi).val.val) ∧
      Nat.card (BrauerFibre rootDown b) = 2 ∧
      Nonempty ((D.map (q matrixSource freeSource)) ≃* DihedralGroup 4) ∧
      ∀ (ambientAt : R.operations.ambientBlockData.blockIdempotent b = b.val)
        (defectImage : TypeBQ3B2DefectDescent.Navarro99cDefectImageSource
          matrixSource freeSource blocks D defect R b ambientAt image)
        (navarro : ∀ W : CharacterWeight 2 K G3,
          letI := localOrdinaryRoots (K := K) W.subgroup
          ScopedDefectZeroReductionSource Msys (localQuotientRoot rootDown W.subgroup)
            (localRoot_residueCanonical Msys rootDown calibrationDown W.subgroup))
        (physical : GuardedBlockCompatibility rootDown R.operations)
        (census : TypeBQ3B2DownstairsWeights.SambaleKessarOrderSource
          Msys rootDown calibrationDown navarro R physical b ambientAt)
        (automorphisms : TypeBQ3TripleCoverAutomorphisms.MatrixAutomorphismSource)
        (indexTwo : (G (ZMod 3)).index = 2),
        ∃ omega : BrauerFibre rootDown b ≃ R.Fibre b,
          PhysicalExtensionConclusion rootDown R b omega := by
  letI : Finite X := finite_X matrixSource
  intro root Msys calibration ordinaryRoots d blocks ordinary D defect table
    classification heightZero quaternion brauerMap map_injective map_surjective
    compatible outerClass outer outer_nontrivial outerClass_ker outerValues sectorOne R primitive
  let hinj := irreducibleBrauerCharacterInjectivity_of_rootEmbedding root
  let bX := primitiveBlockOfLabel blocks .B2
  letI : Fintype (LiteralPrimitiveBlock k X) := TypeBLiteralBlockReindex.literalBlockFintype blocks
  letI : Fintype (LiteralPrimitiveBlock k G3) := R.operations.ambientBlockData.fintypeBlock
  let DX := TypeBLiteralBlockReindex.literalBlocks blocks
  let DB := TypeBLiteralBlockReindex.literalBlocks R.operations.ambientBlockData.blocks
  let rootDown := TypeBQ3B2CentralQuotient.downRoot matrixSource freeSource root
  letI := TypeBQ3B2RootDescent.downOrdinaryRoots (K := K) matrixSource freeSource
  let calibrationDown :=
    TypeBQ3B2RootDescent.downRoot_residue matrixSource freeSource root Msys calibration
  let tableEquiv := (brauerBlockFibreEquiv root hinj blocks brauerMap
    map_injective map_surjective compatible .B2).trans
      (TypeBQ3FaithfulFibreBinding.brauerFibreEquiv root hinj blocks .B2)
  have cardUp : Nat.card (BrauerFibre root bX) = 2 := by
    calc
      Nat.card (BrauerFibre root bX) = Nat.card (BrauerOutputFibre .B2) :=
        Nat.card_congr tableEquiv.symm
      _ = Fintype.card (BrauerOutputFibre .B2) := Nat.card_eq_fintype_card
      _ = 2 := brauerOutputFibre_card .B2
  have inhabited : Nonempty (BrauerFibre root bX) :=
    (Nat.card_ne_zero.mp (by rw [cardUp]; decide)).1
  let reference : BrauerFibre root bX := Classical.choice inhabited
  let b := TypeBQ3B2CentralQuotient.downBlock matrixSource freeSource root DX bX
    sectorOne DB reference primitive
  have image : algebraMapOf (q matrixSource freeSource) (d .B2) = b.val := rfl
  let deflation := TypeBQ3B2CentralQuotient.brauerDeflation matrixSource freeSource
    root DX bX sectorOne DB reference primitive
  have cardDown : Nat.card (BrauerFibre rootDown b) = 2 :=
    (Nat.card_congr deflation.symm).trans cardUp
  have dihedral := defect_is_dihedral blocks Msys root calibration hinj ordinary
    D defect table classification heightZero quaternion brauerMap map_injective map_surjective compatible
  have downDihedral := TypeBQ3B2DefectDescent.mappedDefect_dihedral
    matrixSource freeSource blocks D defect dihedral
  have fixedUp (alpha : (MulAut X)ᵐᵒᵖ) (phi : BrauerFibre root bX) :
      alpha • phi.val = phi.val :=
    TypeBQ3B2Matching.brauer_fixed blocks root hinj brauerMap map_injective map_surjective
      compatible outerClass outer outer_nontrivial outerClass_ker outerValues alpha
      ((TypeBQ3FaithfulFibreBinding.brauerFibreEquiv root hinj blocks .B2).symm phi)
  have fixedDown (alpha : (MulAut G3)ᵐᵒᵖ) (phi : BrauerFibre rootDown b) :
      alpha • phi.val = phi.val := by
    exact TypeBQ3B2AutomorphismLift.fixed_downstairs matrixSource freeSource root
      (deflation.symm phi).val phi.val rfl (fun beta => fixedUp beta (deflation.symm phi)) alpha
  refine ⟨b, image, deflation, ?_, ?_, ?_, cardDown, downDihedral, ?_⟩
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
  · intro ambientAt defectImage navarro physical census automorphisms indexTwo
    let downDefect := TypeBQ3B2DefectDescent.mappedDefect
      matrixSource freeSource blocks D defect R b ambientAt image defectImage
    obtain ⟨weightEight, weightFour, orderEight, orderFour, exhaustive, weightCard, weightFixed⟩ :=
      TypeBQ3B2DownstairsWeights.weight_orders_card_and_fixed
        Msys rootDown calibrationDown navarro R physical b ambientAt census
        (D.map (q matrixSource freeSource)) downDefect downDihedral cardDown
    obtain ⟨omega, graph⟩ := TypeBQ3B2DownstairsMatching.exists_equivariant_matching
      rootDown R b cardDown weightCard fixedDown weightFixed
    exact ⟨omega, TypeBQ3B2CriterionFinish.of_matching rootDown R b matrixSource
      automorphisms indexTwo Msys calibrationDown navarro physical ambientAt omega graph⟩

end ModularRep.PaperProofs.TypeBQ3B2CriterionApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
