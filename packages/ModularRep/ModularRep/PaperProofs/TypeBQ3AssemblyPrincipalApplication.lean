import ModularRep.PaperProofs.TypeBQ3PrincipalCriterionApplication
import ModularRep.PaperProofs.TypeBQ3AssemblyPrincipalIdentification
import ModularRep.PaperProofs.TypeBQ3AssemblyQuotientPresentation

/-!
The principal branch is invoked on its original specified inputs. Its actual
seed, complete deflation and selected raw representatives are retained when
the named B1 block is identified. Only the specified catalogues at those
selected pairs remain before the common-quotient witness is returned.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBQ3AssemblyPrincipalApplication

open ModularRep CharacterWeight FDRepSimpleClassKZero
open Formalisation.ComputationArithmetic
open TypeBQ3TripleCoverCarrier TypeBRankThreePrincipalCountBinding
open TypeBCentralKernelBlockSource TypeBCentralKernelInertia
open TypeBCentralKernelTripleCertificate (PhysicalBlocks)
open TypeBExceptionalQ3Proposition416Actual
open TypeBQ3PrincipalWeightInflation TypeBQ3PrincipalTripleCoverApplication
open TypeBQ3PrincipalCriterionDominatedBlock TypeBQ3PrincipalPairBlockChoice
open TypeBQ3AssemblyQuotientPresentation
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierActualNormalizerBase
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open Representation.Extension NavarroBrauerRestrictionCovering

variable {k K O : Type}
  [Field k] [Field K] [CommRing O] [IsDomain O] [Algebra O K]
  [CharP k 2] [IsAlgClosed k] [CharZero K]

local instance groupFintype (Y : Type) [Group Y] [Finite Y] : Fintype Y :=
  Fintype.ofFinite Y
local instance twoPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable (matrixSource : MatrixExceptionalSource)
  (freeSource : TypeBExceptionalCanonicalCover.FreePresentationCoverSource)
  [Finite X]
  (rootX : PrimeRegularRootEmbedding 2 k K X)
  (Msys : ModularSystem 2 K O k)
  (R : OmegaWeightSource (k := k) (K := K) (ZMod 3))
  (literal : ∀ c, R.operations.ambientBlockData.blockIdempotent c = c.val)
  (indexTwo : (G (ZMod 3)).index = 2)
  (primitive : CentralPrimeToPrimitiveImageSource (k := k)
    (q matrixSource freeSource) (q_surjective matrixSource freeSource) rootX.prime
    (q_kernel_le_center matrixSource freeSource) (q_kernel_primeToTwo matrixSource freeSource))

/-- The existing specified principal inputs before any matching is constructed. -/
structure PhysicalPrincipalInput where
  SX : CoverWeightSource (k := k) (K := K) X
  literalX : ∀ c, SX.operations.ambientBlockData.blockIdempotent c = c.val
  bX : LiteralPrimitiveBlock k X
  principalX : IsPrincipal bX
  b : LiteralPrimitiveBlock k G3
  principal : IsPrincipal b
  weightSource :
    letI : Fintype (LiteralPrimitiveBlock k X) := SX.operations.ambientBlockData.fintypeBlock
    letI : Fintype (LiteralPrimitiveBlock k G3) := R.operations.ambientBlockData.fintypeBlock
    FLZ23Source
      (q matrixSource freeSource) (q_surjective matrixSource freeSource)
      (q_kernel_le_center matrixSource freeSource) (q_kernel_primeToTwo matrixSource freeSource)
      SX literalX R literal rootX bX principalX b principal
      (TypeBQ3PrincipalBrauerInflation.principal_image
        (q matrixSource freeSource) (q_surjective matrixSource freeSource)
        (q_kernel_le_center matrixSource freeSource) (q_kernel_primeToTwo matrixSource freeSource)
        rootX (omegaDecomposition (ZMod 3) R literal) bX principalX b principal primitive)
  [ordinaryRootsH : HasEnoughRootsOfUnity K (Nat.card (H (ZMod 3)))]
  delta : H (ZMod 3)
  outside : delta ∉ G (ZMod 3)
  SH : SOWeightSource (k := k) (K := K) (ZMod 3)
  literalH : ∀ c, SH.operations.ambientBlockData.blockIdempotent c = c.val
  bH : LiteralPrimitiveBlock k (H (ZMod 3))
  principalH : IsPrincipal bH
  [fintypeBrauer : Fintype (OmegaBrauer (ZMod 3) (rootDown matrixSource freeSource rootX) b)]
  [decidableBrauer : DecidableEq (OmegaBrauer (ZMod 3) (rootDown matrixSource freeSource rootX) b)]
  [fintypeOmegaWeight : Fintype (OmegaWeight (ZMod 3) R b)]
  [decidableOmegaWeight : DecidableEq (OmegaWeight (ZMod 3) R b)]
  [fintypeSOWeight : Fintype (SOWeight (ZMod 3) SH bH)]
  [decidableSOWeight : DecidableEq (SOWeight (ZMod 3) SH bH)]
  dgn : TypeBWeightCoveringSplittingSource.DGNSource (G (ZMod 3)) Msys
  brauerSource : TypeBQ3PrincipalBrauerBinding.LiteralSource
    R literal (rootDown matrixSource freeSource rootX) b principal delta indexTwo outside
  covering : TypeBQ3PrincipalWeightBinding.PublishedWeightCovering
    R literal b principal delta indexTwo outside SH literalH bH principalH Msys dgn

/-- Only the selected principal pairs require these specified catalogues. -/
structure PrincipalCatalogues
    (root : PrimeRegularRootEmbedding 2 k K G3)
    (R : OmegaWeightSource (k := k) (K := K) (ZMod 3))
    (b : LiteralPrimitiveBlock k G3)
    (selected : (phi : BrauerFibre root b) →
      {W : CharacterWeight 2 K G3 // R.operations.rawWeightBlock W = b}) where
  ambientBlocks : ∀ phi : BrauerFibre root b,
    PhysicalBlocks k (ActualAutAmbient root phi.val)
  localBlocks : ∀ phi : BrauerFibre root b, PhysicalBlocks k
    (embeddedNormalizer (innerEmbedding root phi.val) (selected phi).val.subgroup)
  S414 : ∀ phi : BrauerFibre root b,
    letI := (localBlocks phi).blockFintype
    Navarro414IntervalCentralCharacterSource
      (TypeBQ3PrincipalPairBaseInduction.embeddedRadicalInterval
        root phi.val (selected phi).val)
      (localBlocks phi).decomposition (localBlocks phi).catalogue

/-- Invoke the sealed principal construction and retain its actual quotient
presentation and matching for the named B1 block. -/
theorem principal_branch
    (automorphisms : TypeBQ3TripleCoverAutomorphisms.MatrixAutomorphismSource)
    {d : Q3Block → k[X]} (blocks : BlockIdempotentDecomposition d)
    (brauerMap : LiteralBrauerOutputMap rootX)
    (map_injective : Function.Injective brauerMap.character)
    (map_surjective : Function.Surjective brauerMap.character)
    (compatible : BrauerBlockFibreCompatible rootX
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding rootX) blocks brauerMap)
    (input : PhysicalPrincipalInput matrixSource freeSource rootX Msys R literal indexTwo primitive)
    (principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} 2 k)
    (fieldSource : SpathCoefficientField 2 k Nat.prime_two)
    (S9295 : Navarro9295BrauerRestrictionCoveringPrinciple 2 k K)
    (S96 : Navarro96PGroupCoveringUniquenessPrinciple 2 k) :
    ∃ b : LiteralPrimitiveBlock k G3,
    ∃ selected : (phi : BrauerFibre (rootDown matrixSource freeSource rootX) b) →
        {W : CharacterWeight 2 K G3 // R.operations.rawWeightBlock W = b},
      ∀ catalogues : PrincipalCatalogues (rootDown matrixSource freeSource rootX) R b selected,
        Nonempty (Witness matrixSource freeSource rootX (primitiveBlockOfLabel blocks .B1)
          (q matrixSource freeSource) (rootDown matrixSource freeSource rootX) R) := by
  letI : Fintype (LiteralPrimitiveBlock k X) :=
    input.SX.operations.ambientBlockData.fintypeBlock
  letI : Fintype (LiteralPrimitiveBlock k G3) := R.operations.ambientBlockData.fintypeBlock
  letI := input.ordinaryRootsH
  letI := input.fintypeBrauer
  letI := input.decidableBrauer
  letI := input.fintypeOmegaWeight
  letI := input.decidableOmegaWeight
  letI := input.fintypeSOWeight
  letI := input.decidableSOWeight
  have identified := TypeBQ3AssemblyPrincipalIdentification.principal_eq_B1
    matrixSource freeSource rootX blocks brauerMap map_injective map_surjective compatible
    R literal input.bX input.principalX input.b input.principal input.delta indexTwo
    input.outside primitive input.brauerSource
  have previous :=
    @TypeBQ3PrincipalCriterionApplication.exists_principalTripleCover_dominatedPrincipalCriterion
      matrixSource freeSource k K O
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      automorphisms rootX input.SX input.literalX R literal input.bX input.principalX
      input.b input.principal primitive input.weightSource input.ordinaryRootsH
      input.delta indexTwo input.outside input.SH input.literalH input.bH input.principalH
      input.fintypeBrauer input.decidableBrauer input.fintypeOmegaWeight
      input.decidableOmegaWeight input.fintypeSOWeight input.decidableSOWeight
      Msys input.dgn input.brauerSource input.covering
  obtain ⟨seed, lifted, seedSO, weightSquare, inflation, liftedAut, radical,
    partition, localEquivalences, tails, sectorOne, sector, sectorKernel, kernels,
    image, selected, selectedClass, finish⟩ := previous
  refine ⟨input.b, selected, ?_⟩
  intro catalogues
  rw [← identified]
  have completed := finish catalogues.ambientBlocks catalogues.localBlocks
    principle fieldSource S9295 S96 catalogues.S414
  exact ⟨{
    surjective := q_surjective matrixSource freeSource
    kernel_eq_common := sectorKernel.symm
    downBlock := input.b
    block_image := image
    deflation := brauerDeflation matrixSource freeSource rootX input.SX input.literalX
      R literal input.bX input.principalX input.b input.principal primitive
    deflation_pullback := by
      intro phi
      exact TypeBQ3PrincipalBrauerInflation.principalBrauerDeflation_pullback
        (q matrixSource freeSource) (q_surjective matrixSource freeSource)
        (q_kernel_le_center matrixSource freeSource) (q_kernel_primeToTwo matrixSource freeSource)
        rootX (coverDecomposition input.SX input.literalX) (omegaDecomposition (ZMod 3) R literal)
        input.bX input.principalX input.b input.principal primitive phi
    ownKernel_eq := kernels
    matching := seed
    centralFaithful := completed.1
    clauses := TypeBQ3AssemblyCriterionData.of_principalClauses
      (rootDown matrixSource freeSource rootX) R input.b literal input.principal seed completed.2
  }⟩

end ModularRep.PaperProofs.TypeBQ3AssemblyPrincipalApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
