import ModularRep.PaperProofs.TypeBQ3B2CriterionApplication
import ModularRep.PaperProofs.TypeBQ3B3CriterionApplication

/-!
Specified inputs for the B2 and B3 branches of the nine-block construction.
The first records contain the inputs used before central descent. The later
records are indexed by the constructed dominated block and its image equation.
Shared reductions, block operations and group sources remain parameters.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBQ3AssemblyBranchSources

open ModularRep CharacterWeight FDRepSimpleClassKZero
open TypeBQ3TripleCoverCarrier TypeBRankThreePrincipalCountBinding
open TypeBCentralKernelBlockSource TypeBCentralKernelInertia
open TypeBQ3PrincipalCriterionDominatedBlock
open TypeBExceptionalQ3Proposition416Actual
open TypeBExceptionalQ3Proposition416Relative
open TypeBLocalReductionInstantiation TypeBFixedRootDefinitionFamily
open TypeBQ3FaithfulLocalReduction TypeBQ3B2DihedralDefect
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierQuotientBlockAlgebra
open Formalisation.ComputationArithmetic

variable (matrixSource : MatrixExceptionalSource)
  (freeSource : TypeBExceptionalCanonicalCover.FreePresentationCoverSource)

variable [Finite X]
local instance groupFintype (Y : Type) [Group Y] [Finite Y] : Fintype Y :=
  Fintype.ofFinite Y
local instance twoPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {k K O : Type}
  [Field k] [Field K] [CommRing O] [IsDomain O] [Algebra O K]
  [CharP k 2] [IsAlgClosed k] [CharZero K]
  {d : Q3Block → k[X]}

/-- The specified B2 inputs on the original nine-block decomposition. -/
structure B2Before
    (root : PrimeRegularRootEmbedding 2 k K X)
    (Msys : ModularSystem 2 K O k)
    (calibration : RootResidueCompatible Msys root)
    [HasEnoughRootsOfUnity K (Nat.card X)]
    (blocks : BlockIdempotentDecomposition d)
    (brauerMap : LiteralBrauerOutputMap root) where
  ordinary : PhysicalOrdinarySource blocks Msys root
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root)
  D : Subgroup X
  defect : Navarro411DefectRepresentative (p := 2) blocks .B2 D
  table : PhysicalTableSource blocks Msys root
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root) ordinary D
  classification : OrderEightClassificationSource D
  heightZero : AbelianHeightZeroSource blocks Msys root calibration
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root) ordinary D defect
  quaternion : QuaternionTwoBrauerSource blocks Msys root calibration
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root) ordinary D defect
  outerClass : (MulAut X)ᵐᵒᵖ →* Equiv.Perm (Fin 2)
  outer : (MulAut X)ᵐᵒᵖ
  outer_nontrivial : outerClass outer ≠ 1
  outerClass_ker : outerClass.ker =
    (RepresentationWeight.innerInverseOpHom (G := X)).range
  outerValues : TypeBQ3B2Matching.B2OuterBrauerActionSource root brauerMap outer
  sectorOne : centralSector matrixSource freeSource
    (primitiveBlockOfLabel blocks .B2) = 1

/-- The specified B3 inputs before its dominated block is constructed. -/
structure B3Before (blocks : BlockIdempotentDecomposition d) where
  D : Subgroup X
  defect : Navarro411DefectRepresentative (p := 2) blocks .B3 D
  cardD : Nat.card D = 2
  sectorOne : centralSector matrixSource freeSource
    (primitiveBlockOfLabel blocks .B3) = 1

/-- The B2 sources on the constructed block and the displayed specified system. -/
structure B2After
    (Msys : ModularSystem 2 K O k)
    (rootDown : PrimeRegularRootEmbedding 2 k K G3)
    (calibrationDown : RootResidueCompatible Msys rootDown)
    [HasEnoughRootsOfUnity K (Nat.card G3)]
    (blocks : BlockIdempotentDecomposition d)
    (D : Subgroup X)
    (defect : Navarro411DefectRepresentative (p := 2) blocks .B2 D)
    (R : OmegaWeightSource (k := k) (K := K) (ZMod 3))
    (b : LiteralPrimitiveBlock k G3)
    (ambientAt : R.operations.ambientBlockData.blockIdempotent b = b.val)
    (image : algebraMapOf (q matrixSource freeSource) (d .B2) = b.val)
    (navarro : ∀ W : CharacterWeight 2 K G3,
      letI := localOrdinaryRoots (K := K) W.subgroup
      ScopedDefectZeroReductionSource Msys (localQuotientRoot rootDown W.subgroup)
        (localRoot_residueCanonical Msys rootDown calibrationDown W.subgroup))
    (physical : GuardedBlockCompatibility rootDown R.operations) : Prop where
  defectImage : TypeBQ3B2DefectDescent.Navarro99cDefectImageSource
    matrixSource freeSource blocks D defect R b ambientAt image
  census : TypeBQ3B2DownstairsWeights.SambaleKessarOrderSource
    Msys rootDown calibrationDown navarro R physical b ambientAt

/-- The B3 local source uses the image of its own displayed defect group. -/
structure B3After
    (Msys : ModularSystem 2 K O k)
    (rootDown : PrimeRegularRootEmbedding 2 k K G3)
    (calibrationDown : RootResidueCompatible Msys rootDown)
    [HasEnoughRootsOfUnity K (Nat.card G3)]
    (blocks : BlockIdempotentDecomposition d)
    (D : Subgroup X)
    (defect : Navarro411DefectRepresentative (p := 2) blocks .B3 D)
    (cardD : Nat.card D = 2)
    (R : OmegaWeightSource (k := k) (K := K) (ZMod 3))
    (b : LiteralPrimitiveBlock k G3)
    (ambientAt : R.operations.ambientBlockData.blockIdempotent b = b.val)
    (image : algebraMapOf (q matrixSource freeSource) (d .B3) = b.val)
    (navarro : ∀ W : CharacterWeight 2 K G3,
      letI := localOrdinaryRoots (K := K) W.subgroup
      ScopedDefectZeroReductionSource Msys (localQuotientRoot rootDown W.subgroup)
        (localRoot_residueCanonical Msys rootDown calibrationDown W.subgroup))
    (physical : GuardedBlockCompatibility rootDown R.operations) where
  defectImage : TypeBQ3B3DefectImage.Navarro99cDefectImageSource
    matrixSource freeSource blocks D defect R b ambientAt image
  localSource : TypeBQ3B3NilpotentWeights.LocalSource
    Msys rootDown calibrationDown navarro R physical b ambientAt
    (D.map (q matrixSource freeSource))
    (TypeBQ3B3DefectImage.mappedDefect
      matrixSource freeSource blocks D defect R b ambientAt image defectImage)
    (TypeBQ3B3DefectImage.mappedDefect_card_two
      matrixSource freeSource blocks D defect cardD)

end ModularRep.PaperProofs.TypeBQ3AssemblyBranchSources


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
