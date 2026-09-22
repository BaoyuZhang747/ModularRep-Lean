import ModularRep.PaperProofs.TypeBQ3AssemblyPrincipalApplication
import ModularRep.PaperProofs.TypeBQ3AssemblyNonprincipalApplication
import ModularRep.PaperProofs.TypeBQ3AssemblyFaithfulApplication
import ModularRep.PaperProofs.TypeBQ3AssemblyDefectZeroApplication

/-!
The final nine-block deduction in prop:type-b-q3. Every branch is invoked
from its specified and published subordinate inputs before the complete
primitive-block decomposition is exhausted. No family of block criteria is
an external input. The common central quotient is presented by the same q
for B1--B5 and by identity for B6--B9, with the complete specified character
and weight criterion on that displayed group.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBQ3AssemblyApplication

open ModularRep CharacterWeight FDRepSimpleClassKZero
open Formalisation.ComputationArithmetic
open TypeBQ3TripleCoverCarrier TypeBRankThreePrincipalCountBinding
open TypeBCentralKernelBlockSource TypeBCentralKernelInertia
open TypeBExceptionalQ3Proposition416Actual TypeBQ3PrincipalWeightInflation
open TypeBFixedRootDefinitionFamily TypeBLocalReductionInstantiation
open TypeBQ3FaithfulLocalReduction TypeBQ3PrincipalCriterionDominatedBlock
open TypeBQ3PrincipalPairBlockChoice
open TypeBQ3AssemblyQuotientPresentation TypeBQ3AssemblyBranchSources
open TypeBQ3AssemblyPrincipalApplication TypeBQ3AssemblyNonprincipalApplication
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open SporadicFi24P3Definition44NamedCarrierQuotientBlockAlgebra
open Representation.Extension NavarroBrauerRestrictionCovering

local instance groupFintype (Y : Type) [Group Y] [Finite Y] : Fintype Y :=
  Fintype.ofFinite Y
local instance twoPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {k K O : Type} [Field k] [Field K] [CommRing O] [IsDomain O]
  [Algebra O K] [CharP k 2] [IsAlgClosed k] [CharZero K]

/-- The complete criterion on one of the actual natural central quotient
presentations. Each witness also determines the canonical quotient square,
complete deflation and own-character quotient values. This is an output. -/
def ActualBlockCriterion
    (matrixSource : MatrixExceptionalSource)
    (freeSource : TypeBExceptionalCanonicalCover.FreePresentationCoverSource)
    [Finite X]
    (root : PrimeRegularRootEmbedding 2 k K X)
    (R : OmegaWeightSource (k := k) (K := K) (ZMod 3))
    (RX : CoverWeightSource (k := k) (K := K) X)
    (bX : LiteralPrimitiveBlock k X) : Prop :=
  Nonempty (Witness matrixSource freeSource root bX (q matrixSource freeSource)
    (TypeBQ3B2CentralQuotient.downRoot matrixSource freeSource root) R) ∨
  Nonempty (Witness matrixSource freeSource root bX (MonoidHom.id X) root RX)

/-- Every actual primitive block has its complete criterion, after the
displayed subordinate sources on constructed blocks and selected pairs.
All nine branch criteria are deductions inside this proof. -/
theorem actualTripleCover_allBlocks_criterion
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
      (dictionary : LiteralBrauerOutputMap root)
      (injective : Function.Injective dictionary.character)
      (complete : Function.Surjective dictionary.character)
      (compatible : BrauerBlockFibreCompatible root
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root) blocks dictionary)
      (R : OmegaWeightSource (k := k) (K := K) (ZMod 3))
      (literal : ∀ c, R.operations.ambientBlockData.blockIdempotent c = c.val)
      (primitive : CentralPrimeToPrimitiveImageSource (k := k)
        (q matrixSource freeSource) (q_surjective matrixSource freeSource) root.prime
        (q_kernel_le_center matrixSource freeSource) (q_kernel_primeToTwo matrixSource freeSource))
      (principal : PhysicalPrincipalInput matrixSource freeSource root Msys R
        literal indexTwo primitive)
      (before2 : B2Before matrixSource freeSource root Msys calibration blocks dictionary)
      (before3 : B3Before matrixSource freeSource blocks)
      (faithful : TypeBQ3AssemblyFaithfulApplication.Inputs
        matrixSource freeSource root Msys calibration blocks dictionary)
      (sector4 : centralSector matrixSource freeSource (primitiveBlockOfLabel blocks .B4) = 1)
      (sector5 : centralSector matrixSource freeSource (primitiveBlockOfLabel blocks .B5) = 1),
      let rootDown := TypeBQ3B2CentralQuotient.downRoot matrixSource freeSource root
      letI := TypeBQ3B2RootDescent.downOrdinaryRoots (K := K) matrixSource freeSource
      let calibrationDown :=
        TypeBQ3B2RootDescent.downRoot_residue matrixSource freeSource root Msys calibration
      ∃ (b1 b2 b3 b4 b5 : LiteralPrimitiveBlock k G3)
        (image2 : algebraMapOf (q matrixSource freeSource) (d .B2) = b2.val)
        (image3 : algebraMapOf (q matrixSource freeSource) (d .B3) = b3.val)
        (reference4 : BrauerFibre rootDown b4) (reference5 : BrauerFibre rootDown b5)
        (selected1 : (phi : BrauerFibre rootDown b1) →
          {W : CharacterWeight 2 K G3 // R.operations.rawWeightBlock W = b1}),
        ∀ (navarro : ∀ W : CharacterWeight 2 K G3,
            letI := localOrdinaryRoots (K := K) W.subgroup
            ScopedDefectZeroReductionSource Msys (localQuotientRoot rootDown W.subgroup)
              (localRoot_residueCanonical Msys rootDown calibrationDown W.subgroup))
          (physical : GuardedBlockCompatibility rootDown R.operations)
          (after2 : B2After matrixSource freeSource Msys rootDown calibrationDown
            blocks before2.D before2.defect R b2 (literal b2) image2 navarro physical)
          (after3 : B3After matrixSource freeSource Msys rootDown calibrationDown
            blocks before3.D before3.defect before3.cardD R b3 (literal b3) image3 navarro physical)
          (after4 : TypeBQ3AssemblyDefectZeroApplication.After
            rootDown R b4 reference4)
          (after5 : TypeBQ3AssemblyDefectZeroApplication.After
            rootDown R b5 reference5),
          ∃ (selected2 : (phi : BrauerFibre rootDown b2) →
              {W : CharacterWeight 2 K G3 // R.operations.rawWeightBlock W = b2})
            (selected3 : (phi : BrauerFibre rootDown b3) →
              {W : CharacterWeight 2 K G3 // R.operations.rawWeightBlock W = b3}),
            ∀ (catalogues1 : PrincipalCatalogues rootDown R b1 selected1)
              (catalogues2 : ExtensionCatalogues rootDown R b2 selected2)
              (catalogues3 : ExtensionCatalogues rootDown R b3 selected3)
              (bX : LiteralPrimitiveBlock k X),
              ActualBlockCriterion matrixSource freeSource root R faithful.R bX := by
  letI : Finite X := finite_X matrixSource
  intro root Msys calibration ordinaryRoots d blocks dictionary injective complete compatible
    R literal primitive principal before2 before3 faithful sector4 sector5
  let rootDown := TypeBQ3B2CentralQuotient.downRoot matrixSource freeSource root
  letI := TypeBQ3B2RootDescent.downOrdinaryRoots (K := K) matrixSource freeSource
  let calibrationDown :=
    TypeBQ3B2RootDescent.downRoot_residue matrixSource freeSource root Msys calibration
  obtain ⟨b1, selected1, finish1⟩ := principal_branch matrixSource freeSource root
    Msys R literal indexTwo primitive automorphisms blocks dictionary injective complete
    compatible principal principle fieldSource S9295 S96
  obtain ⟨b2, image2, finish2⟩ := b2_criterion matrixSource freeSource automorphisms
    indexTwo principle fieldSource S9295 S96 root Msys calibration d blocks dictionary
    injective complete compatible R primitive before2
  obtain ⟨b3, image3, finish3⟩ := b3_criterion matrixSource freeSource automorphisms
    indexTwo principle fieldSource S9295 S96 root Msys calibration d blocks dictionary
    injective complete compatible R primitive before3
  obtain ⟨b4, reference4, finish4⟩ :=
    TypeBQ3AssemblyDefectZeroApplication.defectZero_criterion matrixSource freeSource
      root Msys calibration d blocks dictionary complete compatible
      TypeBQ3B45CentralDescent.four sector4 R literal primitive automorphisms indexTwo principle fieldSource
  obtain ⟨b5, reference5, finish5⟩ :=
    TypeBQ3AssemblyDefectZeroApplication.defectZero_criterion matrixSource freeSource
      root Msys calibration d blocks dictionary complete compatible
      TypeBQ3B45CentralDescent.five sector5 R literal primitive automorphisms indexTwo principle fieldSource
  have faithfulRows := TypeBQ3AssemblyFaithfulApplication.exists_witnesses
    matrixSource freeSource root Msys calibration blocks dictionary
    injective complete compatible fieldSource faithful
  refine ⟨b1, b2, b3, b4, b5, image2, image3, reference4, reference5, selected1, ?_⟩
  intro navarro physical after2 after3 after4 after5
  obtain ⟨selected2, complete2⟩ := finish2 (literal b2) navarro physical after2
  obtain ⟨selected3, complete3⟩ := finish3 (literal b3) navarro physical after3
  refine ⟨selected2, selected3, ?_⟩
  intro catalogues1 catalogues2 catalogues3 bX
  obtain ⟨i, rfl⟩ := (primitiveBlockEquiv blocks).surjective bX
  cases i with
  | B1 => exact Or.inl (finish1 catalogues1)
  | B2 => exact Or.inl (complete2 catalogues2)
  | B3 => exact Or.inl (complete3 catalogues3)
  | B4 => exact Or.inl (finish4 navarro physical after4)
  | B5 => exact Or.inl (finish5 navarro physical after5)
  | B6 => exact Or.inr (faithfulRows .B6 (Or.inl rfl))
  | B7 => exact Or.inr (faithfulRows .B7 (Or.inr (Or.inl rfl)))
  | B8 => exact Or.inr (faithfulRows .B8 (Or.inr (Or.inr (Or.inl rfl))))
  | B9 => exact Or.inr (faithfulRows .B9 (Or.inr (Or.inr (Or.inr rfl))))

end ModularRep.PaperProofs.TypeBQ3AssemblyApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
