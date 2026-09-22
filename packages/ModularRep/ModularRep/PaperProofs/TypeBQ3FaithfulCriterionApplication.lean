import ModularRep.PaperProofs.TypeBQ3FaithfulCriterionAssembly
import ModularRep.PaperProofs.TypeBQ3FaithfulCentralSector
import ModularRep.PaperProofs.TypeBQ3FaithfulDihedralCounts
import ModularRep.PaperProofs.TypeBLiteralBlockReindex

/-! The four faithful blocks on the actual retained triple cover.
The table dictionaries construct the matching; the two D8 sources supply
only their guarded numerical consequences. Scoped Navarro reductions and
the specified local selector law construct each extension clause with A=X.
The sector and character kernels are proved trivial on this same carrier.
No criterion, matching or extension packet is an external source field. -/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBQ3FaithfulCriterionApplication

open ModularRep CharacterWeight
open TypeBCentralKernelBlockSource TypeBCentralKernelInertia
open TypeBQ3TripleCoverCarrier TypeBQ3PrincipalWeightInflation
open TypeBQ3PrincipalCriterionDominatedBlock TypeBQ3FaithfulCentralSector
open TypeBQ3FaithfulCriterionAssembly TypeBQ3FaithfulDihedralCounts
open TypeBExceptionalQ3Proposition416Actual TypeBExceptionalQ3CanonicalInnerRangeActual
open TypeBLocalReductionInstantiation TypeBFixedRootDefinitionFamily
open TypeBQ3FaithfulLocalReduction
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open Formalisation.ComputationArithmetic
open ModularRep.FDRepSimpleClassKZero

variable (matrixSource : MatrixExceptionalSource)
  (freeSource : TypeBExceptionalCanonicalCover.FreePresentationCoverSource)

local instance groupFintype (Y : Type) [Group Y] [Finite Y] : Fintype Y :=
  Fintype.ofFinite Y
local instance twoPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {k K O : Type}
  [Field k] [Field K] [CommRing O] [IsDomain O] [Algebra O K]
  [CharP k 2] [IsAlgClosed k] [CharZero K]

/-- Complete centre-faithful fixed-block criteria for B6--B9, conditional
only on the displayed specified carrier, published, and table inputs. -/
theorem exists_faithfulTripleCover_criteria :
  letI : Finite X := finite_X matrixSource
  ∀ (root : PrimeRegularRootEmbedding 2 k K X)
    (Msys : ModularSystem 2 K O k)
    (calibration : RootResidueCompatible Msys root)
    [ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card X)]
    (navarro : ∀ W : CharacterWeight 2 K X,
      letI := localOrdinaryRoots (K := K) W.subgroup
      ScopedDefectZeroReductionSource Msys (localQuotientRoot root W.subgroup)
        (localRoot_residueCanonical Msys root calibration W.subgroup))
    (d : Q3Block → k[X]) (blocks : BlockIdempotentDecomposition d)
    (R : CoverWeightSource (k := k) (K := K) X)
    (outerSource : CanonicalInnerRangeOuterInput blocks)
    (physical : GuardedBlockCompatibility root R.operations)
    (literalAt : ∀ i : Q3Block, (i = .B6 ∨ i = .B7 ∨ i = .B8 ∨ i = .B9) →
      R.operations.ambientBlockData.blockIdempotent (primitiveBlockOfLabel blocks i) = d i)
    (sectorNontrivial : ∀ i : Q3Block, (i = .B6 ∨ i = .B7 ∨ i = .B8 ∨ i = .B9) →
      centralSector matrixSource freeSource (primitiveBlockOfLabel blocks i) ≠ 1)
    (brauerMap : LiteralBrauerOutputMap root)
    (brauerMap_injective : Function.Injective brauerMap.character)
    (brauerMap_surjective : Function.Surjective brauerMap.character)
    (brauerBlock_compatible : BrauerBlockFibreCompatible root
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root) blocks brauerMap)
    (weightMap : LiteralWeightOutputMap (K := K) (X := X))
    (weightMap_injective : Function.Injective weightMap.classOfLabel)
    (weightMap_surjective : Function.Surjective weightMap.classOfLabel)
    (sector_compatible : canonicalWeightRoutingSectorCompatibleUpToFaithfulSwap
      blocks R weightMap)
    (macgregor : MacgregorD8DefectSource blocks)
    (sambaleEight : SambaleD8CountSource Msys root calibration navarro
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root) blocks R physical
      .B8 (literalAt .B8 (Or.inr (Or.inr (Or.inl rfl)))))
    (sambaleNine : SambaleD8CountSource Msys root calibration navarro
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root) blocks R physical
      .B9 (literalAt .B9 (Or.inr (Or.inr (Or.inr rfl)))))
    (fieldSource : SpathCoefficientField 2 k Nat.prime_two),
    Function.Surjective (q matrixSource freeSource) ∧
    (q matrixSource freeSource).ker = Subgroup.center X ∧
    Nat.card (Subgroup.center X) = 3 ∧
    commutator X = ⊤ ∧
    ∀ i : Q3Block, (i = .B6 ∨ i = .B7 ∨ i = .B8 ∨ i = .B9) →
      (centralSector matrixSource freeSource (primitiveBlockOfLabel blocks i)).ker.map
          (Subgroup.center X).subtype = ⊥ ∧
      (∀ phi : BrauerFibre root (primitiveBlockOfLabel blocks i),
        TypeBBSCentralCharacterQuotient.centralKernel root phi.val = ⊥) ∧
      ∃ omega : BrauerFibre root (primitiveBlockOfLabel blocks i) ≃
          CoverWeight R (primitiveBlockOfLabel blocks i),
        CompleteClauses root (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root)
          blocks i R omega := by
  letI : Finite X := finite_X matrixSource
  intro root Msys calibration ordinaryRoots navarro d blocks R outerSource physical
    literalAt sectorNontrivial brauerMap brauerMap_injective brauerMap_surjective
    brauerBlock_compatible weightMap weightMap_injective weightMap_surjective
    sector_compatible macgregor sambaleEight sambaleNine fieldSource
  let hinj := irreducibleBrauerCharacterInjectivity_of_rootEmbedding root
  letI : Fintype (LiteralPrimitiveBlock k X) :=
    R.operations.ambientBlockData.fintypeBlock
  let D := TypeBLiteralBlockReindex.literalBlocks blocks
  have smallCounts := weight_fibre_cards Msys root calibration navarro hinj blocks R
    physical (literalAt .B8 (Or.inr (Or.inr (Or.inl rfl))))
    (literalAt .B9 (Or.inr (Or.inr (Or.inr rfl))))
    brauerMap brauerMap_injective brauerMap_surjective brauerBlock_compatible
    macgregor sambaleEight sambaleNine
  have matchingExists := TypeBQ3FaithfulMatching.exists_faithful_actualFibreEquivs
    blocks root hinj outerSource R brauerMap brauerMap_injective brauerMap_surjective
    brauerBlock_compatible weightMap weightMap_injective weightMap_surjective
    sector_compatible smallCounts.1 smallCounts.2
  refine ⟨q_surjective matrixSource freeSource, q_kernel_eq_center matrixSource freeSource,
    center_X_card matrixSource freeSource, perfect_X matrixSource freeSource, ?_⟩
  intro i hi
  refine ⟨mappedSectorKernel_eq_bot matrixSource freeSource
    (primitiveBlockOfLabel blocks i) (sectorNontrivial i hi), ?_, ?_⟩
  · exact supportedBrauer_centralKernel_eq_bot matrixSource freeSource root D
      (primitiveBlockOfLabel blocks i) (sectorNontrivial i hi)
  · obtain ⟨matching, matchingEquivariant⟩ := matchingExists i hi
    have blockInner : actualBlockStabilizer blocks i ≤
        (RepresentationWeight.innerInverseOpHom (G := X)).range :=
      faithful_actualBlockStabilizer_le_inner blocks
        (CanonicalInnerRangeOuterInput.toC2OuterQuotientInput blocks outerSource)
        (fun alpha halpha b => innerInverseOpRange_fixes_blocks alpha halpha b)
        outerSource.outer outerSource.outer_nontrivial outerSource.computed_outer_block_action i hi
    have centrePrimeTo : Nat.Coprime 2 (Nat.card (Subgroup.center X)) := by
      rw [center_X_card matrixSource freeSource]
      decide
    let reductions := fun (W : CharacterWeight 2 K X)
        (_ : R.operations.rawWeightBlock W = primitiveBlockOfLabel blocks i) =>
      of_scoped Msys root calibration W (navarro W)
    obtain ⟨omega, sameMatching, clauses⟩ := of_matching root hinj blocks i R
      matching matchingEquivariant blockInner centrePrimeTo (literalAt i hi)
      reductions (fun W support => normalizerBlock_of_guarded physical W (reductions W support))
      fieldSource
    exact ⟨omega, clauses⟩

end ModularRep.PaperProofs.TypeBQ3FaithfulCriterionApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
