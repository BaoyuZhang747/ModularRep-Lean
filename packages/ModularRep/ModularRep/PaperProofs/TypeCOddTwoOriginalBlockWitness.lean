import ModularRep.PaperProofs.TypeCOddTwoOriginalIntermediateTransport
import ModularRep.PaperProofs.TypeCOddTwoOriginalTrivialNormalization
import ModularRep.PaperProofs.TypeBFullBlockCondition

/-!
# The actual complete block witness from one original chosen packet

The relative witness and its SAME matching are constructed here. No block
witness, fibre equality or desired matching is an input. The specified
quotient operations retain only the existing individual primitive dictionary
and the guarded own-reduction block law. Five named finite-root conditions
refer to the actual chosen packets; the separate coherent-root construction
supplies them, rather than any new published target assumption.

The resulting omega is definitionally blockEquiv D b. Both quotient fibres,
their reverse maps, own-character transport and quotient graph covariance
are the existing computed maps. The same-extension Q=1 normalization is
retained. The all-block choice and final family construction remain separate.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeCOddTwoOriginalBlockWitness

open ModularRep CharacterWeight FDRepSimpleClassKZero
open CyclicOuterLemma37ActualBlockFibres CyclicOuterLemma37Concrete
open EvenFieldFLZSourceConditions EvenFieldFLZBAWGoodFamily
open EvenFieldFLZCentrelessCentralKernel EvenFieldFLZQuotientBlockFibre
open OddTwoLiteralSpathTarget OddTwoGroupEquivWeightBlocks
open TypeCOddTwoOriginalBlockMatching TypeCOddTwoOriginalReferenceAmbient
open TypeCOddTwoOriginalChosenExtensions TypeCOddTwoOriginalIntermediateTransport
open TypeBFullBlockCondition TypeBFixedRootDefinitionFamily

universe u

variable {n : ℕ} {F : Type u} [Field F] [Finite F]
variable {P : Problem n F} (D : Definition41 P) (b : P.Block)
variable (reference : Definition35Brauer (P.blockProblem b))

local instance originalBlockWitnessQuotientFintype :
    Fintype (CentralCharacterQuotient (P.blockProblem b) reference) :=
  Fintype.ofFinite _

local instance originalBlockWitnessSubgroupFintype
    {G : Type u} [Group G] [Finite G] (H : Subgroup G) :
    Fintype H := Fintype.ofFinite _

/-- The block action is the canonical restriction of the original full action. -/
theorem blockEquiv_equivariant :
    Definition35Equivariant (P.blockProblem b) (blockEquiv D b) := by
  letI := definition35BrauerAction (P.blockProblem b)
  letI := definition35WeightAction (P.blockProblem b)
  intro a psi
  apply Subtype.ext
  exact D.map.equivariant (inverseOpHom (P.blockGamma b) a) psi.1

/-- All dependent local, ambient and intermediate data are the already
computed transports of the SAME original selected matched packet. -/
def matchedTail (psi : Definition35Brauer (P.blockProblem b)) :
    SpathMatchedBlockConditionTail (P.blockProblem b) reference psi
      (blockEquiv D b psi) (referenceSource P b reference psi) where
  weight := quotientPacket D b reference psi
  localInflation := localInflation D b reference psi
  ambient := selectedReferenceAmbient D b reference psi
  extensions := referenceExtensions D b reference psi
  intermediateBlocks := intermediateSource D b reference psi

def matched (psi : Definition35Brauer (P.blockProblem b)) :
    SpathMatchedBlockCondition (P.blockProblem b) reference psi (blockEquiv D b psi) where
  quotient := referenceSource P b reference psi
  tail := matchedTail D b reference psi

/-- The actual transported primitive catalogue contains the same descended
character in the same original block label. -/
theorem descended_liesInBlock (psi : Definition35Brauer (P.blockProblem b)) :
    letI := P.blockSource.operations.ambientBlockData.fintypeBlock
    irreducibleBrauerCharacterBlock
        (referenceSource P b reference psi).iota
        (referenceSource P b reference psi).irreducibleBrauerInjective
        (TypeCOddTwoOriginalQuotientFibres.quotientBlocks P b reference)
        (referenceSource P b reference psi).brauer = b := by
  letI := P.blockSource.operations.ambientBlockData.fintypeBlock
  exact (irreducibleBrauerCharacterBlock_alongMulEquiv P.iota P.injective
    (referenceQuotientEquiv b reference)
    (TypeCOddTwoOriginalQuotientFibres.quotientInjective P b reference)
    P.blockSource.operations.ambientBlockData.blocks psi.1).trans psi.2

/-- Construct the existing relative target, including its actual matched
packets. The quotient catalogue is computed directly, before OH is supplied. -/
def relative : RelativeBlockConditionWitness (family P) (familyCover P) b := by
  letI := P.blockSource.operations.ambientBlockData.fintypeBlock
  exact
    { automorphismStabilizer := stabilizerAdapter P b
      omega := blockEquiv D b
      equivariant := blockEquiv_equivariant D b
      reference := reference
      commonCentralKernel := fun psi =>
        centralCharacterKernel_eq_of_centerless (P.blockProblem b)
          P.center_eq_bot psi reference
      quotientCover := centerlessCentralQuotientCoverSource
        (family P) (familyCover P) P.center_eq_bot b reference
      QuotientBlock := P.Block
      fintypeQuotientBlock := P.blockSource.operations.ambientBlockData.fintypeBlock
      quotientBlockIdempotent :=
        TypeCOddTwoOriginalQuotientFibres.quotientIdempotent P b reference
      quotientBlocks := TypeCOddTwoOriginalQuotientFibres.quotientBlocks P b reference
      quotientBlock := b
      matched := matched D b reference
      descendedBrauer_liesInQuotientBlock := descended_liesInBlock b reference }

@[simp] theorem relative_omega : (relative D b reference).omega = blockEquiv D b := rfl

@[simp] theorem relative_matched (psi : Definition35Brauer (P.blockProblem b)) :
    (relative D b reference).matched psi = matched D b reference psi := rfl

@[simp] theorem relative_extensions (psi : Definition35Brauer (P.blockProblem b)) :
    ((relative D b reference).matched psi).extensions =
      referenceExtensions D b reference psi := rfl

/-- The constructed relative witness stores the same quotient root everywhere. -/
def fixedRoots : FixedQuotientRootSource (relative D b reference) where
  matchedRoot_eq_reference _ := rfl

@[simp] theorem fixedRoot_eq : fixedQuotientRoot (relative D b reference) =
    TypeCOddTwoOriginalQuotientFibres.quotientRoot P b reference := rfl

theorem fixedDescended_eq (psi : Definition35Brauer (P.blockProblem b)) :
    fixedDescendedBrauer (relative D b reference) (fixedRoots D b reference) psi =
      TypeCOddTwoOriginalQuotientFibres.descendedBrauer P b reference psi.1 := by
  apply Subtype.ext
  exact fixedDescendedBrauer_val (relative D b reference) (fixedRoots D b reference) psi

/-- The complete target's raw quotient weight is the original OWN packet. -/
@[simp] theorem quotientRawWeight_eq (psi : Definition35Brauer (P.blockProblem b)) :
    quotientRawWeight (relative D b reference) psi = quotientPair D b reference psi := rfl

@[simp] theorem quotientWeightClass_eq (psi : Definition35Brauer (P.blockProblem b)) :
    quotientWeightClass (relative D b reference) psi =
      OddTwoSelectedWeightAutomorphismCoordinates.weightClass
        (quotientPair D b reference psi) := rfl

variable (OH : LocalBlockInductionOperations
  (p := 2) (k := P.k) (K := P.K)
  (G := CentralCharacterQuotient (P.blockProblem b) reference) (Block := P.Block))
variable (dictionary : PrimitiveDictionary P.blockSource.operations OH
  (referenceQuotientEquiv b reference))

/-- The apparently source-shaped reverse field is constructed from the
actual full Brauer-fibre equivalence and literal catalogue equality. -/
def brauerReverse : QuotientBlockFibreReverseSource
    (relative D b reference) (fixedRoots D b reference) where
  of_quotientBlock phi hphi := by
    letI := P.blockSource.operations.ambientBlockData.fintypeBlock
    have hOwn : TypeCOddTwoOriginalQuotientFibres.quotientBrauerBlock
        P b reference OH phi = b :=
      (TypeCOddTwoOriginalQuotientFibres.quotientBrauerBlock_eq_computed
        P b reference OH dictionary phi).trans hphi
    obtain ⟨psi, hpsi⟩ := TypeCOddTwoOriginalQuotientFibres.brauer_reverse
      P b reference OH dictionary ⟨phi, hOwn⟩
    exact ⟨psi, (fixedDescended_eq D b reference psi).trans hpsi⟩

include dictionary in
theorem quotient_block_transport :
    letI : Fintype (relative D b reference).QuotientBlock :=
      (relative D b reference).fintypeQuotientBlock
    letI : MulAction (MulAut (QuotientCarrier (relative D b reference)))ᵐᵒᵖ
        (relative D b reference).QuotientBlock :=
      transportedBlockAction (G := X n F) (Block := P.Block)
        (referenceQuotientEquiv b reference)
    ∀ (alpha : (MulAut (QuotientCarrier (relative D b reference)))ᵐᵒᵖ)
      (phi : IBr (fixedQuotientRoot (relative D b reference))),
    irreducibleBrauerCharacterBlock
        (fixedQuotientRoot (relative D b reference))
        (fixedQuotientBrauerInjective (relative D b reference))
        (relative D b reference).quotientBlocks (alpha • phi) =
      alpha • irreducibleBrauerCharacterBlock
        (fixedQuotientRoot (relative D b reference))
        (fixedQuotientBrauerInjective (relative D b reference))
        (relative D b reference).quotientBlocks phi := by
  letI := transportedBlockAction (G := X n F) (Block := P.Block)
    (referenceQuotientEquiv b reference)
  letI := P.blockSource.operations.ambientBlockData.fintypeBlock
  intro alpha phi
  let alphaActual :
      (MulAut (CentralCharacterQuotient (P.blockProblem b) reference))ᵐᵒᵖ := alpha
  let phiActual : IBr (TypeCOddTwoOriginalQuotientFibres.quotientRoot
      P b reference) := phi
  exact (TypeCOddTwoOriginalQuotientFibres.quotientBrauerBlock_eq_computed
      P b reference OH dictionary (alphaActual • phiActual)).symm.trans
    ((TypeCOddTwoOriginalQuotientFibres.quotientBrauerBlock_transport
      P b reference OH dictionary alphaActual phiActual).trans
      (congrArg (fun c : P.Block => alphaActual • c)
        (TypeCOddTwoOriginalQuotientFibres.quotientBrauerBlock_eq_computed
          P b reference OH dictionary phiActual)))

/-! These five conditional parameters are the exact finite-domain guards
on the displayed original packets. The separate coherent-root module
derives them from its chosen metadata; they contain no desired witness. -/

variable (weightRoots : ∀ psi : Definition35Brauer (P.blockProblem b),
  QuotientRootAgreement (TypeCOddTwoOriginalQuotientFibres.quotientRoot P b reference)
    (quotientRadical (P.blockProblem b) reference (blockEquiv D b psi))
    (quotientPacket D b reference psi).iota)
variable (inflationRoots : ∀ psi : Definition35Brauer (P.blockProblem b),
  NormalizerRootAgreement (TypeCOddTwoOriginalQuotientFibres.quotientRoot P b reference)
    (quotientRadical (P.blockProblem b) reference (blockEquiv D b psi))
    (localInflation D b reference psi).iota)
variable (ambientRoots : ∀ psi : Definition35Brauer (P.blockProblem b),
  RootLiftAgreement (referenceSource P b reference psi).iota
    (referenceExtensions D b reference psi).ambientRoot)
variable (localRoots : ∀ psi : Definition35Brauer (P.blockProblem b),
  RootLiftAgreement (referenceExtensions D b reference psi).localAmbientRoot
    (referenceExtensions D b reference psi).ambientRoot)
variable (intermediateRoots : ∀ (psi : Definition35Brauer (P.blockProblem b))
    (J : Subgroup (selectedReferenceAmbient D b reference psi).A)
    (hJ : (selectedReferenceAmbient D b reference psi).base ≤ J),
  RootLiftAgreement
      ((intermediateSource D b reference psi).equalityAt J hJ).globalRoot
      (referenceExtensions D b reference psi).ambientRoot ∧
    RootLiftAgreement
      ((intermediateSource D b reference psi).equalityAt J hJ).localRoot
      (referenceExtensions D b reference psi).ambientRoot)
variable (physical :
  letI := transportedBlockAction (G := X n F) (Block := P.Block)
    (referenceQuotientEquiv b reference)
  GuardedBlockCompatibility
    (TypeCOddTwoOriginalQuotientFibres.quotientRoot P b reference) OH)

/-- Construct the complete BlockWitness, using the already constructed
relative witness and computed full quotient fibres. No W is supplied. -/
def blockWitness : BlockWitness (family P) (familyCover P) b := by
  letI := transportedBlockAction (G := X n F) (Block := P.Block)
    (referenceQuotientEquiv b reference)
  refine
    { relative := relative D b reference
      roots := fixedRoots D b reference
      brauerReverse := brauerReverse D b reference OH dictionary
      quotientBlockAction := transportedBlockAction (G := X n F) (Block := P.Block)
        (referenceQuotientEquiv b reference)
      quotientBlockSource := TypeCOddTwoOriginalQuotientFibres.quotientSource
        P b reference OH dictionary
      quotientBlockIdempotent :=
        TypeCOddTwoOriginalQuotientFibres.quotientOperation_idempotent
          P b reference OH dictionary
      quotientBlockCompatibility := physical
      quotientRoots_agree := fun z =>
        TypeCOddTwoOriginalQuotientFibres.quotientRoot_lift P b reference _
      quotientWeight_roots := weightRoots
      quotientInflation_roots := inflationRoots
      quotientAmbient_roots := ambientRoots
      localAmbient_roots := localRoots
      intermediate_roots := intermediateRoots
      quotientBrauerBlock_transport := quotient_block_transport D b reference OH dictionary
      weight_liesInQuotientBlock :=
        TypeCOddTwoOriginalQuotientFibres.quotientPair_liesInBlock
          P b reference OH dictionary D
      weight_injective := quotientPair_class_injective D b reference
      weight_reverse := TypeCOddTwoOriginalQuotientFibres.weight_reverse
        P b reference OH dictionary D
      quotient_equivariant := ?_ }
  intro alpha psi chi h
  let alphaActual :
      (MulAut (CentralCharacterQuotient (P.blockProblem b) reference))ᵐᵒᵖ := alpha
  have hActual : TypeCOddTwoOriginalQuotientFibres.descendedBrauer P b reference chi.1 =
      alphaActual • TypeCOddTwoOriginalQuotientFibres.descendedBrauer P b reference psi.1 :=
    (fixedDescended_eq D b reference chi).symm.trans
      (h.trans (congrArg
        (fun phi : IBr (TypeCOddTwoOriginalQuotientFibres.quotientRoot P b reference) =>
          alphaActual • phi) (fixedDescended_eq D b reference psi)))
  exact TypeCOddTwoOriginalQuotientFibres.quotient_graph_equivariant
    P b reference D alphaActual psi chi hActual

@[simp] theorem blockWitness_relative :
    (blockWitness D b reference OH dictionary weightRoots inflationRoots ambientRoots
      localRoots intermediateRoots physical).relative = relative D b reference := rfl

@[simp] theorem blockWitness_omega :
    (blockWitness D b reference OH dictionary weightRoots inflationRoots ambientRoots
      localRoots intermediateRoots physical).relative.omega = blockEquiv D b := rfl

/-- The OTHER Q=1 clause is the original equality of the SAME extensions,
carried through the actual reference coordinates, independently of root guards. -/
theorem relative_trivial_extensions :
    TrivialExtensionNormalization (relative D b reference) := by
  intro psi hQ
  exact TypeCOddTwoOriginalTrivialNormalization.reference_trivial_extensions
    D b reference psi hQ

theorem blockWitness_trivial_extensions :
    TrivialExtensionNormalization
      (blockWitness D b reference OH dictionary weightRoots inflationRoots ambientRoots
        localRoots intermediateRoots physical).relative :=
  relative_trivial_extensions D b reference

end ModularRep.PaperProofs.TypeCOddTwoOriginalBlockWitness


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
