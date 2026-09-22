import ModularRep.PaperProofs.TypeCOddTwoOriginalFamilyWitness
import ModularRep.PaperProofs.TypeCOddTwoOriginalRootGuards

/-!
# Apply the joint original source to the complete coherent family

Specified inputs contain only actual reference characters, quotient block
operations and their individual standard dictionaries. All five finite-root
guards are computed from the SAME jointly chosen original witness. No
BlockWitness, FamilyWitness, correspondence equality or finite-root guard
is accepted as a published-source premise by the final application.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeCOddTwoCoherentFamilyApplication

open ModularRep CharacterWeight FDRepSimpleClassKZero
open CyclicOuterLemma37Concrete EvenFieldFLZSourceConditions EvenFieldFLZBAWGoodFamily
open OddTwoLiteralSpathTarget TypeCCoherentFiniteRootConvention
open TypeCOddTwoCoherentTargetData TypeCOddTwoChosenRootMetadata
open TypeCOddTwoOriginalBlockMatching OddTwoGroupEquivWeightBlocks
open TypeBFullBlockCondition TypeBFixedRootDefinitionFamily
open OddTwoFinalBlockOrbitCentralCoverDescentWindow OddTwoFengMalleForwardSourceJoin

universe u

private abbrev HasConventionRoot
    {p : ℕ} {k K G : Type u} [Field k] [Field K] [Group G] [Finite G]
    (C : Convention p k K) (r : PrimeRegularRootEmbedding p k K G) : Prop :=
  r = C.rootAt G

variable {n : ℕ} {F : Type u} [Field F] [Finite F]

local instance applicationQuotientFintype {P : Problem n F}
    (b : P.Block) (ref : Definition35Brauer (P.blockProblem b)) :
    Fintype (CentralCharacterQuotient (P.blockProblem b) ref) := Fintype.ofFinite _

/-- Existing individual specified inputs, fixed before selecting D. Reference
choice is just a character in each actual specified block. The block-operation
law concerns an own reduction in its authentic fixed modular system. -/
structure PhysicalInputs (P : Problem n F) where
  reference : ∀ b : P.Block, Definition35Brauer (P.blockProblem b)
  operations : ∀ b : P.Block, LocalBlockInductionOperations
    (p := 2) (k := P.k) (K := P.K)
    (G := CentralCharacterQuotient (P.blockProblem b) (reference b)) (Block := P.Block)
  dictionary : ∀ b : P.Block,
    PrimitiveDictionary P.blockSource.operations (operations b)
      (referenceQuotientEquiv b (reference b))
  compatibility : ∀ b : P.Block,
    letI := transportedBlockAction (G := X n F) (Block := P.Block)
      (referenceQuotientEquiv b (reference b))
    GuardedBlockCompatibility
      (TypeCOddTwoOriginalQuotientFibres.quotientRoot P b (reference b)) (operations b)

section Original

variable {P : Problem n F} (D : Definition41 P) (C : Convention 2 P.k P.K)
variable (hRoot : P.iota = C.rootAt (X n F))
variable (hSelected : ∀ (b : P.Block)
  (w : CyclicOuterLemma37LiteralLocalExtension.LiteralWeightFibre P.blockSource b),
  HasConventionRoot C (P.localReduction b w).iota)
variable (metadata : ChosenRootMetadata C D) (physical : PhysicalInputs P)

/-- The complete original family with every finite-domain guard discharged
by the actual coherent convention and metadata of this SAME D. -/
def coherentFamilyWitness : FamilyWitness (family P) (familyCover P) :=
  TypeCOddTwoOriginalFamilyWitness.familyWitness D physical.reference
    physical.operations physical.dictionary
    (fun b psi => TypeCOddTwoOriginalRootGuards.quotientWeight_roots
      D C hRoot hSelected b (physical.reference b) psi)
    (fun b psi => TypeCOddTwoOriginalRootGuards.quotientInflation_roots
      D C hRoot metadata b (physical.reference b) psi)
    (fun b psi => TypeCOddTwoOriginalRootGuards.quotientAmbient_roots
      D C hRoot metadata b (physical.reference b) psi)
    (fun b psi => TypeCOddTwoOriginalRootGuards.localAmbient_roots
      D C metadata b (physical.reference b) psi)
    (fun b psi J hJ => TypeCOddTwoOriginalRootGuards.intermediate_roots
      D C metadata b (physical.reference b) psi J hJ)
    physical.compatibility

@[simp] theorem coherentFamilyWitness_omega (b : P.Block) :
    ((coherentFamilyWitness D C hRoot hSelected metadata physical).blocks b).relative.omega =
      blockEquiv D b := rfl

end Original

section PublishedApplication

variable (P : LiteralFengMalleProblem n F) (O : LiteralDiagonalFieldRealisation n F)
variable (C : Convention 2 P.k P.K) (S : CanonicalTargetData P C)
variable (admissible : P.iota = C.rootAt (LiteralSp n F))
variable (physical : PhysicalInputs (S.targetData admissible).toProblem)
variable (source : JointFengMalleProposition34Source P O C S admissible)

/-- The existing literal FM hypothesis builder is applied to the actual
input Sp map. The source returns ONE original PSp witness with metadata;
all complete-family fields and guards are then constructed in K. -/
def familyWitnessFromFengMalle
    (input : InputSemantics P) (omega : LiteralGlobalMap P)
    (corollary46 : LiteralFengMalleCorollary46Certificate P O) :
    FamilyWitness (family (S.targetData admissible).toProblem)
      (familyCover (S.targetData admissible).toProblem) := by
  let chosen := source.chooseOfLiteralGlobalMap input omega corollary46
  exact coherentFamilyWitness chosen.1 C rfl (fun _ _ => rfl) chosen.2 physical

include source physical in
/-- Conditional complete output at the literal computed target. The
specified/source inputs retain their authenticated E1/E2 interpretation. -/
theorem complete_original_family
    (input : InputSemantics P) (omega : LiteralGlobalMap P)
    (corollary46 : LiteralFengMalleCorollary46Certificate P O) :
    Nonempty (FamilyWitness (family (S.targetData admissible).toProblem)
      (familyCover (S.targetData admissible).toProblem)) :=
  ⟨familyWitnessFromFengMalle P O C S admissible physical source input omega corollary46⟩

end PublishedApplication

end ModularRep.PaperProofs.TypeCOddTwoCoherentFamilyApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
