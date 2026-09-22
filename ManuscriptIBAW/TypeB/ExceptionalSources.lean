import ManuscriptIBAW.TypeB.DefectEight
import ModularRep.PaperProofs.TypeBCurrentQ3Inputs

/-!
# Exceptional block sources with direct quaternion exclusion

The inputs on the nine actual blocks use the direct exclusion of two
Brauer characters for a quaternion defect group. The numerical implication
needed by the retained construction is derived from that exclusion. No
retained raw source carrying the numerical implication is an input.

The dependent local sources refer to the blocks and representatives chosen
by the same proved construction. The principal quotient application reuses
the resulting full family in `ExceptionalPrincipalDescent`.
-/

noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
open scoped MonoidAlgebra

namespace ManuscriptIBAW.TypeB.Exceptional

open ModularRep ModularRep.PaperProofs CharacterWeight FDRepSimpleClassKZero
open Formalisation.ComputationArithmetic
open TypeBQ3TripleCoverCarrier TypeBRankThreePrincipalCountBinding
open TypeBCentralKernelBlockSource TypeBCentralKernelInertia
open TypeBExceptionalQ3Proposition416Actual TypeBQ3PrincipalWeightInflation
open TypeBFixedRootDefinitionFamily TypeBLocalReductionInstantiation
open TypeBQ3FaithfulLocalReduction TypeBQ3PrincipalCriterionDominatedBlock
open TypeBQ3PrincipalPairBlockChoice
open TypeBQ3AssemblyQuotientPresentation TypeBQ3AssemblyBranchSources
open TypeBQ3AssemblyPrincipalApplication TypeBQ3AssemblyNonprincipalApplication
open TypeBQ3AssemblyApplication
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open SporadicFi24P3Definition44NamedCarrierQuotientBlockAlgebra
open Representation.Extension NavarroBrauerRestrictionCovering
open TypeBQ3B2DihedralDefect TypeBExceptionalQ3Proposition416Relative

local instance groupFintype (Y : Type) [Group Y] [Finite Y] : Fintype Y :=
  Fintype.ofFinite Y
local instance twoPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {k K O : Type} [Field k] [Field K] [CommRing O] [IsDomain O]
  [Algebra O K] [CharP k 2] [IsAlgClosed k] [CharZero K]

variable (matrixSource : MatrixExceptionalSource)
  (freeSource : TypeBExceptionalCanonicalCover.FreePresentationCoverSource)
  [Finite X] [HasEnoughRootsOfUnity K (Nat.card X)]

variable {d : Q3Block → k[X]}

/-- Sources on B2, requiring the direct quaternion exclusion. -/
structure B2Sources
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
  quaternionExclusion : DefectEight.QuaternionExclusionSource blocks Msys root calibration
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root) D defect
  outerClass : (MulAut X)ᵐᵒᵖ →* Equiv.Perm (Fin 2)
  outer : (MulAut X)ᵐᵒᵖ
  outer_nontrivial : outerClass outer ≠ 1
  outerClass_ker : outerClass.ker =
    (RepresentationWeight.innerInverseOpHom (G := X)).range
  outerValues : TypeBQ3B2Matching.B2OuterBrauerActionSource root brauerMap outer
  sectorOne : centralSector matrixSource freeSource
    (primitiveBlockOfLabel blocks .B2) = 1

variable {matrixSource freeSource}

/-- Derive the retained numerical implication from an impossible quaternion
case, preserving every other source field. -/
def B2Sources.toLegacy
    {root : PrimeRegularRootEmbedding 2 k K X}
    {Msys : ModularSystem 2 K O k}
    {calibration : RootResidueCompatible Msys root}
    {blocks : BlockIdempotentDecomposition d}
    {brauerMap : LiteralBrauerOutputMap root}
    (B : B2Sources matrixSource freeSource root Msys calibration blocks brauerMap) :
    TypeBQ3AssemblyBranchSources.B2Before
      matrixSource freeSource root Msys calibration blocks brauerMap where
  ordinary := B.ordinary
  D := B.D
  defect := B.defect
  table := B.table
  classification := B.classification
  heightZero := B.heightZero
  outerClass := B.outerClass
  outer := B.outer
  outer_nontrivial := B.outer_nontrivial
  outerClass_ker := B.outerClass_ker
  outerValues := B.outerValues
  sectorOne := B.sectorOne
  quaternion := DefectEight.QuaternionExclusionSource.toNumerical
    blocks Msys root calibration
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root)
    B.ordinary B.D B.defect B.quaternionExclusion

variable (matrixSource freeSource)

/-- Sources supplied before the block and weight representatives are chosen. -/
structure BeforeSources where
  automorphisms : TypeBQ3TripleCoverAutomorphisms.MatrixAutomorphismSource
  indexTwo : (G (ZMod 3)).index = 2
  principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} 2 k
  fieldSource : SpathCoefficientField 2 k Nat.prime_two
  S9295 : Navarro9295BrauerRestrictionCoveringPrinciple 2 k K
  S96 : Navarro96PGroupCoveringUniquenessPrinciple 2 k
  root : PrimeRegularRootEmbedding 2 k K X
  Msys : ModularSystem 2 K O k
  calibration : RootResidueCompatible Msys root
  d : Q3Block → k[X]
  blocks : BlockIdempotentDecomposition d
  dictionary : LiteralBrauerOutputMap root
  injective : Function.Injective dictionary.character
  complete : Function.Surjective dictionary.character
  compatible : BrauerBlockFibreCompatible root
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root) blocks dictionary
  R : OmegaWeightSource (k := k) (K := K) (ZMod 3)
  literal : ∀ c, R.operations.ambientBlockData.blockIdempotent c = c.val
  primitive : CentralPrimeToPrimitiveImageSource (k := k)
    (q matrixSource freeSource) (q_surjective matrixSource freeSource) root.prime
    (q_kernel_le_center matrixSource freeSource) (q_kernel_primeToTwo matrixSource freeSource)
  principal : PhysicalPrincipalInput matrixSource freeSource root Msys R
    literal indexTwo primitive
  before2 : B2Sources matrixSource freeSource root Msys calibration blocks dictionary
  before3 : B3Before matrixSource freeSource blocks
  faithful : TypeBQ3AssemblyFaithfulApplication.Inputs
    matrixSource freeSource root Msys calibration blocks dictionary
  sector4 : centralSector matrixSource freeSource (primitiveBlockOfLabel blocks .B4) = 1
  sector5 : centralSector matrixSource freeSource (primitiveBlockOfLabel blocks .B5) = 1

variable {matrixSource freeSource}

/-- Reconstruct the retained source record, deriving its quaternion field. -/
def BeforeSources.toLegacy
    (B : BeforeSources (k := k) (K := K) (O := O) matrixSource freeSource) :
    TypeBCurrentQ3Inputs.BeforeInputs (k := k) (K := K) (O := O)
      matrixSource freeSource where
  automorphisms := B.automorphisms
  indexTwo := B.indexTwo
  principle := B.principle
  fieldSource := B.fieldSource
  S9295 := B.S9295
  S96 := B.S96
  root := B.root
  Msys := B.Msys
  calibration := B.calibration
  d := B.d
  blocks := B.blocks
  dictionary := B.dictionary
  injective := B.injective
  complete := B.complete
  compatible := B.compatible
  R := B.R
  literal := B.literal
  primitive := B.primitive
  principal := B.principal
  before2 := B.before2.toLegacy
  before3 := B.before3
  faithful := B.faithful
  sector4 := B.sector4
  sector5 := B.sector5

/-- The later sources are indexed by the choices made from the converted
first-stage sources. No completed block criterion is an input. -/
structure RawInputs where
  beforeSources : BeforeSources (k := k) (K := K) (O := O) matrixSource freeSource
  after : TypeBCurrentQ3Inputs.AfterInputs beforeSources.toLegacy
    (TypeBCurrentQ3Inputs.firstSelection beforeSources.toLegacy)
  catalogues : TypeBCurrentQ3Inputs.CatalogueInputs beforeSources.toLegacy
    (TypeBCurrentQ3Inputs.firstSelection beforeSources.toLegacy)
    (TypeBCurrentQ3Inputs.secondSelection beforeSources.toLegacy after)

/-- The retained first-stage record is derived data. -/
def RawInputs.before
    (D : RawInputs (k := k) (K := K) (O := O)
      (matrixSource := matrixSource) (freeSource := freeSource)) :
    TypeBCurrentQ3Inputs.BeforeInputs (k := k) (K := K) (O := O)
      matrixSource freeSource := D.beforeSources.toLegacy

/-- Compatibility with the proved nine-block construction. -/
def RawInputs.toLegacy
    (D : RawInputs (k := k) (K := K) (O := O)
      (matrixSource := matrixSource) (freeSource := freeSource)) :
    TypeBCurrentQ3Inputs.Inputs (k := k) (K := K) (O := O)
      (matrixSource := matrixSource) (freeSource := freeSource) where
  before := D.before
  after := D.after
  catalogues := D.catalogues

/-- The natural block criteria are proved after the direct exclusion has
supplied the retained compatibility implication. -/
theorem RawInputs.allBlocks
    (D : RawInputs (k := k) (K := K) (O := O)
      (matrixSource := matrixSource) (freeSource := freeSource)) :
    TypeBCurrentQ3Inputs.AllBlocksCertificate D.before := D.toLegacy.allBlocks
end ManuscriptIBAW.TypeB.Exceptional

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
this package's formalisation report and source records.
-/
