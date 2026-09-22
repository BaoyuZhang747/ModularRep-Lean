import ModularRep.PaperProofs.TypeBQ3AssemblyApplication

/-!
# Dependent source interface for the exceptional nine-block case

This file packages the exact subordinate-input telescope of the established
`actualTripleCover_allBlocks_criterion`. First the existing theorem chooses
the five dominated blocks and principal representatives. The local inputs
are then supplied on those choices, after which the theorem chooses the B2
and B3 representatives. Only those selected representatives require the
final specified catalogues. Neither a family of completed criteria nor a
matching is an input. The output retains the existing natural presentations
`q : X → G3` and `id : X → X`; it is not a `FamilyWitness` conversion.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBCurrentQ3Inputs

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
open TypeBQ3AssemblyApplication
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open SporadicFi24P3Definition44NamedCarrierQuotientBlockAlgebra
open Representation.Extension NavarroBrauerRestrictionCovering

local instance groupFintype (Y : Type) [Group Y] [Finite Y] : Fintype Y :=
  Fintype.ofFinite Y
local instance twoPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {k K O : Type} [Field k] [Field K] [CommRing O] [IsDomain O]
  [Algebra O K] [CharP k 2] [IsAlgClosed k] [CharZero K]

variable (matrixSource : MatrixExceptionalSource)
  (freeSource : TypeBExceptionalCanonicalCover.FreePresentationCoverSource)
  [Finite X] [HasEnoughRootsOfUnity K (Nat.card X)]

/-- The original inputs occurring before the first existential in the
accepted nine-block application. Every field is an existing subordinate
source or an exact specified/carrier identification. -/
structure BeforeInputs where
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
  before2 : B2Before matrixSource freeSource root Msys calibration blocks dictionary
  before3 : B3Before matrixSource freeSource blocks
  faithful : TypeBQ3AssemblyFaithfulApplication.Inputs
    matrixSource freeSource root Msys calibration blocks dictionary
  sector4 : centralSector matrixSource freeSource (primitiveBlockOfLabel blocks .B4) = 1
  sector5 : centralSector matrixSource freeSource (primitiveBlockOfLabel blocks .B5) = 1

variable {matrixSource freeSource}

namespace BeforeInputs

variable (B : BeforeInputs (k := k) (K := K) (O := O) matrixSource freeSource)

/-- The root embedding on the same actual quotient, derived upstairs. -/
def rootDown : PrimeRegularRootEmbedding 2 k K G3 :=
  TypeBQ3B2CentralQuotient.downRoot matrixSource freeSource B.root

/-- Residue calibration descends with the same quotient/root choice. -/
theorem calibrationDown : RootResidueCompatible B.Msys B.rootDown :=
  TypeBQ3B2RootDescent.downRoot_residue matrixSource freeSource B.root B.Msys B.calibration

end BeforeInputs

/-- The first stage contains output data, never external block choices. -/
structure FirstSelection
    (B : BeforeInputs (k := k) (K := K) (O := O) matrixSource freeSource) where
  b1 : LiteralPrimitiveBlock k G3
  b2 : LiteralPrimitiveBlock k G3
  b3 : LiteralPrimitiveBlock k G3
  b4 : LiteralPrimitiveBlock k G3
  b5 : LiteralPrimitiveBlock k G3
  image2 : algebraMapOf (q matrixSource freeSource) (B.d .B2) = b2.val
  image3 : algebraMapOf (q matrixSource freeSource) (B.d .B3) = b3.val
  reference4 : BrauerFibre B.rootDown b4
  reference5 : BrauerFibre B.rootDown b5
  selected1 : (phi : BrauerFibre B.rootDown b1) →
    {W : CharacterWeight 2 K G3 // B.R.operations.rawWeightBlock W = b1}

/-- Postdescent sources on the constructed blocks and exact image
equations. The ordinary root guard is derived from the upstairs guard,
and both calibrations and B2/B3 defect data are retained literally. -/
structure AfterInputs
    (B : BeforeInputs (k := k) (K := K) (O := O) matrixSource freeSource)
    (first : FirstSelection B) where
  navarro :
    letI := TypeBQ3B2RootDescent.downOrdinaryRoots (K := K) matrixSource freeSource
    ∀ W : CharacterWeight 2 K G3,
      letI := localOrdinaryRoots (K := K) W.subgroup
      ScopedDefectZeroReductionSource B.Msys (localQuotientRoot B.rootDown W.subgroup)
        (localRoot_residueCanonical B.Msys B.rootDown B.calibrationDown W.subgroup)
  physical : GuardedBlockCompatibility B.rootDown B.R.operations
  after2 :
    letI := TypeBQ3B2RootDescent.downOrdinaryRoots (K := K) matrixSource freeSource
    B2After matrixSource freeSource B.Msys B.rootDown B.calibrationDown
      B.blocks B.before2.D B.before2.defect B.R first.b2 (B.literal first.b2)
      first.image2 navarro physical
  after3 :
    letI := TypeBQ3B2RootDescent.downOrdinaryRoots (K := K) matrixSource freeSource
    B3After matrixSource freeSource B.Msys B.rootDown B.calibrationDown
      B.blocks B.before3.D B.before3.defect B.before3.cardD B.R first.b3
      (B.literal first.b3) first.image3 navarro physical
  after4 : TypeBQ3AssemblyDefectZeroApplication.After
    B.rootDown B.R first.b4 first.reference4
  after5 : TypeBQ3AssemblyDefectZeroApplication.After
    B.rootDown B.R first.b5 first.reference5

/-- B2 and B3 representatives selected only after their local sources
have been applied. These selections are produced by the existing proof. -/
structure SecondSelection
    (B : BeforeInputs (k := k) (K := K) (O := O) matrixSource freeSource)
    (first : FirstSelection B) where
  selected2 : (phi : BrauerFibre B.rootDown first.b2) →
    {W : CharacterWeight 2 K G3 // B.R.operations.rawWeightBlock W = first.b2}
  selected3 : (phi : BrauerFibre B.rootDown first.b3) →
    {W : CharacterWeight 2 K G3 // B.R.operations.rawWeightBlock W = first.b3}

/-- Specified catalogues and interval sources for precisely the three
selected representative families. No new arbitrary-matching quantifier. -/
structure CatalogueInputs
    (B : BeforeInputs (k := k) (K := K) (O := O) matrixSource freeSource)
    (first : FirstSelection B) (second : SecondSelection B first) where
  principal : PrincipalCatalogues B.rootDown B.R first.b1 first.selected1
  extension2 : ExtensionCatalogues B.rootDown B.R first.b2 second.selected2
  extension3 : ExtensionCatalogues B.rootDown B.R first.b3 second.selected3

/-- The fixed output on every actual block, in the accepted natural
central quotient presentations. The faithful operations are those of the
same before-input source. -/
def AllBlocksCertificate
    (B : BeforeInputs (k := k) (K := K) (O := O) matrixSource freeSource) : Prop :=
  ∀ bX : LiteralPrimitiveBlock k X,
    ActualBlockCriterion matrixSource freeSource B.root B.R B.faithful.R bX

/-- Repackage the accepted proof's exact existential/universal order.
Every completed criterion below comes from that proof, not from a source
field; all nine branch deductions remain its established internal work. -/
theorem staged_assembly
    (B : BeforeInputs (k := k) (K := K) (O := O) matrixSource freeSource) :
    ∃ first : FirstSelection B, ∀ after : AfterInputs B first,
      ∃ second : SecondSelection B first,
        CatalogueInputs B first second → AllBlocksCertificate B := by
  letI := TypeBQ3B2RootDescent.downOrdinaryRoots (K := K) matrixSource freeSource
  obtain ⟨b1, b2, b3, b4, b5, image2, image3, reference4, reference5, selected1, finish⟩ :=
    actualTripleCover_allBlocks_criterion matrixSource freeSource B.automorphisms
      B.indexTwo B.principle B.fieldSource B.S9295 B.S96 B.root B.Msys B.calibration
      B.d B.blocks B.dictionary B.injective B.complete B.compatible B.R B.literal
      B.primitive B.principal B.before2 B.before3 B.faithful B.sector4 B.sector5
  refine ⟨⟨b1, b2, b3, b4, b5, image2, image3, reference4, reference5, selected1⟩, ?_⟩
  intro after
  obtain ⟨selected2, selected3, finish⟩ :=
    finish after.navarro after.physical after.after2 after.after3 after.after4 after.after5
  refine ⟨⟨selected2, selected3⟩, ?_⟩
  intro catalogues
  exact finish catalogues.principal catalogues.extension2 catalogues.extension3

/-- Fix the constructed first stage before asking for its dependent
local sources. This is a choice from a proved theorem. -/
def firstSelection
    (B : BeforeInputs (k := k) (K := K) (O := O) matrixSource freeSource) : FirstSelection B :=
  Classical.choose (staged_assembly B)

theorem firstSelection_spec
    (B : BeforeInputs (k := k) (K := K) (O := O) matrixSource freeSource)
    (after : AfterInputs B (firstSelection B)) :
    ∃ second : SecondSelection B (firstSelection B),
      CatalogueInputs B (firstSelection B) second → AllBlocksCertificate B :=
  Classical.choose_spec (staged_assembly B) after

/-- Fix the B2/B3 choices produced from those local sources. -/
def secondSelection
    (B : BeforeInputs (k := k) (K := K) (O := O) matrixSource freeSource)
    (after : AfterInputs B (firstSelection B)) : SecondSelection B (firstSelection B) :=
  Classical.choose (firstSelection_spec B after)

theorem secondSelection_spec
    (B : BeforeInputs (k := k) (K := K) (O := O) matrixSource freeSource)
    (after : AfterInputs B (firstSelection B)) :
    CatalogueInputs B (firstSelection B) (secondSelection B after) → AllBlocksCertificate B :=
  Classical.choose_spec (firstSelection_spec B after)

/-- The compact exact source package. Its late fields refer to the
constructed choices above, so no source family on arbitrarily nominated
blocks, weights, or matchings is added. No criterion is an input field. -/
structure Inputs where
  before : BeforeInputs (k := k) (K := K) (O := O) matrixSource freeSource
  after : AfterInputs before (firstSelection before)
  catalogues : CatalogueInputs before (firstSelection before) (secondSelection before after)

/-- The exceptional q=3 all-block conclusion from its complete subordinate
source package, preserving the actual natural presentations. -/
theorem Inputs.allBlocks
    (source : Inputs (k := k) (K := K) (O := O) (matrixSource := matrixSource)
      (freeSource := freeSource)) : AllBlocksCertificate source.before :=
  secondSelection_spec source.before source.after source.catalogues

end ModularRep.PaperProofs.TypeBCurrentQ3Inputs


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
