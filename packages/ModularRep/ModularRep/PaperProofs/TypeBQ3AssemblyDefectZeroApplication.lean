import ModularRep.PaperProofs.TypeBQ3B45CriterionApplication
import ModularRep.PaperProofs.TypeBQ3AssemblyQuotientPresentation

/-!
The two defect-zero cases are applied on their constructed primitive images.
Only the selected ordinary reduction, specified local rows and one ambient
catalogue/root seed are grouped below. The named branch theorem constructs
the character and weight correspondence and all extension clauses internally.
The resulting witness retains the exact q, root, block image and deflation.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBQ3AssemblyDefectZeroApplication

open ModularRep CharacterWeight FDRepSimpleClassKZero
open Formalisation.ComputationArithmetic
open TypeBQ3TripleCoverCarrier TypeBRankThreePrincipalCountBinding
open TypeBCentralKernelBlockSource TypeBCentralKernelInertia
open TypeBExceptionalQ3Proposition416Actual TypeBQ3PrincipalCriterionDominatedBlock
open TypeBLocalReductionInstantiation TypeBQ3B45CentralDescent
open TypeBFixedRootDefinitionFamily TypeBQ3FaithfulLocalReduction
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open TypeBCentralKernelTripleCertificate (PhysicalBlocks)
open SporadicCompleteCollapseLemma52Actual (GlobalDefectZeroCharacter)
open SporadicCompleteCollapseLemma52ConcreteLocal (IsBrauerReduction)
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open SporadicFi24P3Definition44NamedCarrierQuotientBlockAlgebra

local instance groupFintype (Y : Type) [Group Y] [Finite Y] : Fintype Y :=
  Fintype.ofFinite Y
local instance twoPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {k K O : Type} [Field k] [Field K] [CommRing O] [IsDomain O]
  [Algebra O K] [CharP k 2] [IsAlgClosed k] [CharZero K]

/-- Subordinate inputs on the already constructed singleton reference.
No criterion, matching or extension packet is a field. -/
structure After
    (root : PrimeRegularRootEmbedding 2 k K G3)
    (R : OmegaWeightSource (k := k) (K := K) (ZMod 3))
    (b : LiteralPrimitiveBlock k G3) (reference : BrauerFibre root b) where
  ordinary : GlobalDefectZeroCharacter (p := 2) (K := K) (X := G3)
  reduction : IsBrauerReduction root ordinary.val reference.val
  regular_unique : ∀ ordinary' : GlobalDefectZeroCharacter (p := 2) (K := K) (X := G3),
    (∀ g : PrimeRegularElement (G := G3) 2,
      ordinary'.val g.val = ordinary.val g.val) → ordinary' = ordinary
  rawTrivial : ∀ W : CharacterWeight 2 K G3,
    R.operations.rawWeightBlock W = b → W.subgroup = ⊥
  ambientBlocks : PhysicalBlocks k (ActualAutAmbient root reference.val)
  ambientSeed : PrimeRegularRootEmbedding 2 k K (ActualAutAmbient root reference.val)

variable (matrixSource : MatrixExceptionalSource)
  (freeSource : TypeBExceptionalCanonicalCover.FreePresentationCoverSource)
  [Finite X]

/-- Apply a named defect-zero branch, keeping its sources on its derived image. -/
theorem defectZero_criterion
    (root : PrimeRegularRootEmbedding 2 k K X)
    (Msys : ModularSystem 2 K O k)
    (calibration : RootResidueCompatible Msys root)
    [ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card X)]
    (d : Q3Block → k[X]) (blocks : BlockIdempotentDecomposition d)
    (dictionary : LiteralBrauerOutputMap root)
    (complete : Function.Surjective dictionary.character)
    (compatible : BrauerBlockFibreCompatible root
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root) blocks dictionary)
    (i : Block45)
    (sectorOne : centralSector matrixSource freeSource (upBlock blocks i) = 1)
    (R : OmegaWeightSource (k := k) (K := K) (ZMod 3))
    (literal : ∀ c, R.operations.ambientBlockData.blockIdempotent c = c.val)
    (primitive : CentralPrimeToPrimitiveImageSource (k := k)
      (q matrixSource freeSource) (q_surjective matrixSource freeSource) root.prime
      (q_kernel_le_center matrixSource freeSource) (q_kernel_primeToTwo matrixSource freeSource))
    (automorphisms : TypeBQ3TripleCoverAutomorphisms.MatrixAutomorphismSource)
    (indexTwo : (G (ZMod 3)).index = 2)
    (principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} 2 k)
    (fieldSource : SpathCoefficientField 2 k Nat.prime_two) :
    let rootDown := downRoot root matrixSource freeSource
    letI := TypeBQ3B2RootDescent.downOrdinaryRoots (K := K) matrixSource freeSource
    let calibrationDown :=
      TypeBQ3B2RootDescent.downRoot_residue matrixSource freeSource root Msys calibration
    ∃ (b : LiteralPrimitiveBlock k G3) (reference : BrauerFibre rootDown b),
      ∀ (navarro : ∀ W : CharacterWeight 2 K G3,
          letI := localOrdinaryRoots (K := K) W.subgroup
          ScopedDefectZeroReductionSource Msys (localQuotientRoot rootDown W.subgroup)
            (localRoot_residueCanonical Msys rootDown calibrationDown W.subgroup))
        (physical : GuardedBlockCompatibility rootDown R.operations)
        (_ : After rootDown R b reference),
        Nonempty (TypeBQ3AssemblyQuotientPresentation.Witness matrixSource freeSource
          root (upBlock blocks i) (q matrixSource freeSource) rootDown R) := by
  let rootDown := downRoot root matrixSource freeSource
  letI := TypeBQ3B2RootDescent.downOrdinaryRoots (K := K) matrixSource freeSource
  let calibrationDown :=
    TypeBQ3B2RootDescent.downRoot_residue matrixSource freeSource root Msys calibration
  obtain ⟨b, reference, deflation, image, _, pullback, kernels, _, _, _, finish⟩ :=
    TypeBQ3B45CriterionApplication.actualTripleCover_B4_B5_criterion
      matrixSource freeSource root Msys calibration d blocks dictionary complete compatible
      i sectorOne R primitive
  refine ⟨b, reference, ?_⟩
  intro navarro physical after
  let physicalRows : TypeBQ3B45PhysicalInputs.ScopedInputs
      Msys rootDown calibrationDown matrixSource R b after.ordinary := {
    navarro := fun W _ => navarro W
    normalizer_block_of_reduction := fun W _ => physical.normalizer_block_of_reduction W
  }
  obtain ⟨omega, clauses⟩ := finish after.ordinary after.reduction
    after.regular_unique (literal b) after.rawTrivial physicalRows
    automorphisms indexTwo after.ambientBlocks principle after.ambientSeed fieldSource
  exact ⟨{
    surjective := q_surjective matrixSource freeSource
    kernel_eq_common := (TypeBQ3B2CentralQuotient.sectorKernel_eq_qker
      matrixSource freeSource (upBlock blocks i) sectorOne).symm
    downBlock := b
    block_image := image
    deflation := deflation
    deflation_pullback := pullback
    ownKernel_eq := kernels
    matching := omega
    centralFaithful := TypeBQ3AssemblyQuotientPresentation.centralFaithful_G3
      matrixSource rootDown b
    clauses := TypeBQ3AssemblyCriterionData.of_b2 rootDown R b omega clauses
  }⟩

end ModularRep.PaperProofs.TypeBQ3AssemblyDefectZeroApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
