import ModularRep.PaperProofs.TypeBQ3FaithfulCriterionApplication
import ModularRep.PaperProofs.TypeBQ3AssemblyFaithfulNormalization
import ModularRep.PaperProofs.TypeBQ3AssemblyQuotientPresentation

/-!
The faithful branch sources are indexed by the common specified group, root,
modular system and named decomposition. The accepted branch constructs its
matching and complete clauses. Their natural quotient presentation is the
identity on the same group, since the common central kernel is trivial.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBQ3AssemblyFaithfulApplication

open ModularRep CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open TypeBCentralKernelBlockSource TypeBCentralKernelInertia
open TypeBQ3TripleCoverCarrier TypeBQ3PrincipalWeightInflation
open TypeBQ3PrincipalCriterionDominatedBlock
open TypeBExceptionalQ3Proposition416Actual TypeBExceptionalQ3CanonicalInnerRangeActual
open TypeBQ3FaithfulDihedralCounts
open TypeBLocalReductionInstantiation TypeBFixedRootDefinitionFamily
open TypeBQ3FaithfulLocalReduction
open TypeBQ3AssemblyQuotientPresentation
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

variable (root : PrimeRegularRootEmbedding 2 k K X)
  (Msys : ModularSystem 2 K O k)
  (calibration : RootResidueCompatible Msys root)
  [ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card X)]
  {d : Q3Block → k[X]} (blocks : BlockIdempotentDecomposition d)

/-- The faithful branch's subordinate sources on the common fixed data. -/
structure Inputs (brauerMap : LiteralBrauerOutputMap root) where
  R : CoverWeightSource (k := k) (K := K) X
  navarro : ∀ W : CharacterWeight 2 K X,
    letI := localOrdinaryRoots (K := K) W.subgroup
    ScopedDefectZeroReductionSource Msys (localQuotientRoot root W.subgroup)
      (localRoot_residueCanonical Msys root calibration W.subgroup)
  outerSource : CanonicalInnerRangeOuterInput blocks
  physical : GuardedBlockCompatibility root R.operations
  literalAt : ∀ i : Q3Block, (i = .B6 ∨ i = .B7 ∨ i = .B8 ∨ i = .B9) →
    R.operations.ambientBlockData.blockIdempotent (primitiveBlockOfLabel blocks i) = d i
  sectorNontrivial : ∀ i : Q3Block, (i = .B6 ∨ i = .B7 ∨ i = .B8 ∨ i = .B9) →
    centralSector matrixSource freeSource (primitiveBlockOfLabel blocks i) ≠ 1
  weightMap : LiteralWeightOutputMap (K := K) (X := X)
  weightMap_injective : Function.Injective weightMap.classOfLabel
  weightMap_surjective : Function.Surjective weightMap.classOfLabel
  sector_compatible : canonicalWeightRoutingSectorCompatibleUpToFaithfulSwap
    blocks R weightMap
  macgregor : MacgregorD8DefectSource blocks
  sambaleEight : SambaleD8CountSource Msys root calibration navarro
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root) blocks R physical
    .B8 (literalAt .B8 (Or.inr (Or.inr (Or.inl rfl))))
  sambaleNine : SambaleD8CountSource Msys root calibration navarro
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root) blocks R physical
    .B9 (literalAt .B9 (Or.inr (Or.inr (Or.inr rfl))))

variable (brauerMap : LiteralBrauerOutputMap root)

/-- Each faithful named block has its constructed criterion on the identity
presentation of its common central quotient. -/
theorem exists_witnesses
    (brauerMap_injective : Function.Injective brauerMap.character)
    (brauerMap_surjective : Function.Surjective brauerMap.character)
    (brauerBlock_compatible : BrauerBlockFibreCompatible root
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root) blocks brauerMap)
    (fieldSource : SpathCoefficientField 2 k Nat.prime_two)
    (source : Inputs matrixSource freeSource root Msys calibration blocks brauerMap) :
    ∀ i : Q3Block, (i = .B6 ∨ i = .B7 ∨ i = .B8 ∨ i = .B9) →
      Nonempty (Witness matrixSource freeSource root (primitiveBlockOfLabel blocks i)
        (MonoidHom.id X) root source.R) := by
  have accepted :=
    TypeBQ3FaithfulCriterionApplication.exists_faithfulTripleCover_criteria
      matrixSource freeSource root Msys calibration source.navarro d blocks source.R
      source.outerSource source.physical source.literalAt source.sectorNontrivial
      brauerMap brauerMap_injective brauerMap_surjective brauerBlock_compatible
      source.weightMap source.weightMap_injective source.weightMap_surjective
      source.sector_compatible source.macgregor source.sambaleEight source.sambaleNine
      fieldSource
  intro i hi
  have branch := accepted.2.2.2.2 i hi
  have common : commonKernel matrixSource freeSource
      (primitiveBlockOfLabel blocks i) = ⊥ := branch.1
  refine Exists.elim branch.2.2 ?_
  intro omega clauses
  refine ⟨{
    surjective := Function.surjective_id
    kernel_eq_common := (MonoidHom.ker_id).trans common.symm
    downBlock := primitiveBlockOfLabel blocks i
    block_image := ?_
    deflation := Equiv.refl _
    deflation_pullback := ?_
    ownKernel_eq := ?_
    centralFaithful := branch.2.1
    matching := omega
    clauses := TypeBQ3AssemblyFaithfulNormalization.of_faithfulClauses
      root (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root)
      blocks i source.R omega clauses
  }⟩
  · simp only [algebraMapOf, MonoidAlgebra.mapDomainAlgHom_id, AlgHom.id_apply]
  · intro phi
    apply PrimeRegularClassFunction.ext
    intro x
    rfl
  · intro phi
    exact (branch.2.1 phi).trans (MonoidHom.ker_id).symm

end ModularRep.PaperProofs.TypeBQ3AssemblyFaithfulApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
