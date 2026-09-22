import ModularRep.PaperProofs.TypeCOddTwoOriginalBlockWitness
import ModularRep.PaperProofs.TypeCOddTwoOriginalGlobalClauses

/-!
# Complete family combined from the original chosen odd-two packets

Every block witness is constructed from its actual reference, quotient
operations and specified dictionary. The five finite-root guards concern
the SAME original chosen packets; the coherent-metadata consumer proves
them separately. No BlockWitness, FamilyWitness, new correspondence or
equivariance of reference choices is an input.

The global and radical clauses use the original map. Both Q=1 clauses
remain: its own ordinary reduction and the equality of its SAME chosen
extensions. This K construction introduces no additional published source.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeCOddTwoOriginalFamilyWitness

open ModularRep CharacterWeight FDRepSimpleClassKZero
open CyclicOuterLemma37Concrete EvenFieldFLZSourceConditions
open EvenFieldFLZBAWGoodFamily OddTwoLiteralSpathTarget
open OddTwoGroupEquivWeightBlocks TypeBFullBlockCondition
open TypeBFixedRootDefinitionFamily
open TypeCOddTwoOriginalBlockMatching TypeCOddTwoOriginalReferenceAmbient
open TypeCOddTwoOriginalChosenExtensions TypeCOddTwoOriginalIntermediateTransport

universe u

variable {n : ℕ} {F : Type u} [Field F] [Finite F]
variable {P : Problem n F} (D : Definition41 P)

local instance originalFamilyWitnessQuotientFintype (b : P.Block)
    (ref : Definition35Brauer (P.blockProblem b)) :
    Fintype (CentralCharacterQuotient (P.blockProblem b) ref) := Fintype.ofFinite _

local instance originalFamilyWitnessSubgroupFintype
    {G : Type u} [Group G] [Finite G] (H : Subgroup G) :
    Fintype H := Fintype.ofFinite _

/-- Pointwise reference choice requires only actual nonemptiness of each
specified Brauer fibre, not a completed block or an equivariant choice. -/
def chooseReferences
    (nonempty : ∀ b : P.Block, Nonempty (Definition35Brauer (P.blockProblem b))) :
    ∀ b : P.Block, Definition35Brauer (P.blockProblem b) :=
  fun b => Classical.choice (nonempty b)

variable (reference : ∀ b : P.Block, Definition35Brauer (P.blockProblem b))
variable (OH : ∀ b : P.Block, LocalBlockInductionOperations
  (p := 2) (k := P.k) (K := P.K)
  (G := CentralCharacterQuotient (P.blockProblem b) (reference b)) (Block := P.Block))
variable (dictionary : ∀ b : P.Block,
  PrimitiveDictionary P.blockSource.operations (OH b)
    (referenceQuotientEquiv b (reference b)))

variable (weightRoots : ∀ (b : P.Block) (psi : Definition35Brauer (P.blockProblem b)),
  QuotientRootAgreement
    (TypeCOddTwoOriginalQuotientFibres.quotientRoot P b (reference b))
    (quotientRadical (P.blockProblem b) (reference b) (blockEquiv D b psi))
    (quotientPacket D b (reference b) psi).iota)
variable (inflationRoots : ∀ (b : P.Block) (psi : Definition35Brauer (P.blockProblem b)),
  NormalizerRootAgreement
    (TypeCOddTwoOriginalQuotientFibres.quotientRoot P b (reference b))
    (quotientRadical (P.blockProblem b) (reference b) (blockEquiv D b psi))
    (localInflation D b (reference b) psi).iota)
variable (ambientRoots : ∀ (b : P.Block) (psi : Definition35Brauer (P.blockProblem b)),
  RootLiftAgreement (referenceSource P b (reference b) psi).iota
    (referenceExtensions D b (reference b) psi).ambientRoot)
variable (localRoots : ∀ (b : P.Block) (psi : Definition35Brauer (P.blockProblem b)),
  RootLiftAgreement (referenceExtensions D b (reference b) psi).localAmbientRoot
    (referenceExtensions D b (reference b) psi).ambientRoot)
variable (intermediateRoots : ∀ (b : P.Block)
    (psi : Definition35Brauer (P.blockProblem b))
    (J : Subgroup (selectedReferenceAmbient D b (reference b) psi).A)
    (hJ : (selectedReferenceAmbient D b (reference b) psi).base ≤ J),
  RootLiftAgreement
      ((intermediateSource D b (reference b) psi).equalityAt J hJ).globalRoot
      (referenceExtensions D b (reference b) psi).ambientRoot ∧
    RootLiftAgreement
      ((intermediateSource D b (reference b) psi).equalityAt J hJ).localRoot
      (referenceExtensions D b (reference b) psi).ambientRoot)
variable (physical : ∀ b : P.Block,
  letI := transportedBlockAction (G := X n F) (Block := P.Block)
    (referenceQuotientEquiv b (reference b))
  GuardedBlockCompatibility
    (TypeCOddTwoOriginalQuotientFibres.quotientRoot P b (reference b)) (OH b))

/-- The blocks are outputs of the actual original-packet constructor. -/
def blocks : ∀ b : P.Block, BlockWitness (family P) (familyCover P) b :=
  fun b => TypeCOddTwoOriginalBlockWitness.blockWitness D b (reference b)
    (OH b) (dictionary b) (weightRoots b) (inflationRoots b)
    (ambientRoots b) (localRoots b) (intermediateRoots b) (physical b)

@[simp] theorem blocks_omega (b : P.Block) :
    (blocks D reference OH dictionary weightRoots inflationRoots ambientRoots
      localRoots intermediateRoots physical b).relative.omega = blockEquiv D b := rfl

/-- Combine the fixed complete target from the SAME original map and its
constructed blocks. The two trivial-radical normalizations are both retained. -/
def familyWitness : FamilyWitness (family P) (familyCover P) := by
  let W := blocks D reference OH dictionary weightRoots inflationRoots ambientRoots
    localRoots intermediateRoots physical
  have hOmega : ∀ b : P.Block, (W b).relative.omega = blockEquiv D b := fun _ => rfl
  exact
    { blocks := W
      naturality := TypeCOddTwoOriginalGlobalClauses.naturality D W hOmega
      global_bijective := TypeCOddTwoOriginalGlobalClauses.global_bijective D W hOmega
      global_equivariant := TypeCOddTwoOriginalGlobalClauses.global_equivariant D W hOmega
      radicalEquiv := TypeCOddTwoOriginalGlobalClauses.radicalEquiv D W hOmega
      radical_matches := TypeCOddTwoOriginalGlobalClauses.radical_matches D W hOmega
      radical_transport := TypeCOddTwoOriginalGlobalClauses.radical_transport D W hOmega
      central_values := TypeCOddTwoOriginalGlobalClauses.central_values D W hOmega
      trivial_reduction := TypeCOddTwoOriginalGlobalClauses.trivial_reduction D W hOmega
      trivial_extensions := fun b =>
        TypeCOddTwoOriginalBlockWitness.blockWitness_trivial_extensions
          D b (reference b) (OH b) (dictionary b) (weightRoots b) (inflationRoots b)
          (ambientRoots b) (localRoots b) (intermediateRoots b) (physical b) }

@[simp] theorem familyWitness_omega (b : P.Block) :
    ((familyWitness D reference OH dictionary weightRoots inflationRoots ambientRoots
      localRoots intermediateRoots physical).blocks b).relative.omega = blockEquiv D b := rfl

/-- Recombining the constructed block maps gives the original global map. -/
theorem familyWitness_globalWeight (psi : IBr P.iota) :
    globalWeight (family := family P) (cover := familyCover P)
        (familyWitness D reference OH dictionary weightRoots inflationRoots ambientRoots
          localRoots intermediateRoots physical).blocks psi = D.map.equiv psi :=
  TypeCOddTwoOriginalGlobalClauses.globalWeight_eq D
    (blocks D reference OH dictionary weightRoots inflationRoots ambientRoots
      localRoots intermediateRoots physical) (fun _ => rfl) psi

end ModularRep.PaperProofs.TypeCOddTwoOriginalFamilyWitness


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
