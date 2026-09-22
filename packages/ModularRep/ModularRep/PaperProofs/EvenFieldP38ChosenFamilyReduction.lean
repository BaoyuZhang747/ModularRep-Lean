import ModularRep.PaperProofs.EvenFieldClassifiedP38FamilyPacket
import ModularRep.PaperProofs.TypeCSelectedPairGroupEquivCoordinates
import ModularRep.PaperProofs.TypeCChosenPairRootTransport

/-!
# The P38 chosen quotient table from the fixed family's own table

The inverse actual weight-fibre map fixes the family weight. Actual class
equality determines an inner correction sending its whole selected pair to
the concrete selected pair. The quotient table is transported through that
computed map before the protected P38 endgame is applied. One admissible
own-normalizer packet retains both the fixed ambient and quotient squares.

This is a choice of compatible input data, not an identification with an
independently stored concrete table or a relation-forward source.
-/

noncomputable section

namespace ModularRep.PaperProofs.EvenFieldP38ChosenFamilyReduction

open ModularRep CharacterWeight
open CyclicOuterLemma37Concrete CyclicOuterLemma37ActualBlockFibres
open CyclicOuterLemma37LiteralLocalExtension
open EvenFieldConcreteTypeC EvenFieldFLZDefinition35Family EvenFieldFLZSourceConditions
open EvenFieldClassifiedP38FamilyPacket
open OddTwoSelectedWeightAutomorphismCoordinates
open TypeCSelectedPairGroupEquivCoordinates
open TypeCChosenPairRootTransport
open OddTwoActualStabilizerTriple OddTwoActualCentralInflationPacket
open OddTwoActualLocalBlockSupport OddTwoDefinition35OwnReduction

local instance chosenFamilySubgroupFintype {A : Type} [Group A] [Finite A]
    (Q : Subgroup A) : Fintype Q := Fintype.ofFinite Q

variable {ell r a : ℕ} (family : Definition35Family.{0} ell)
variable (ha : 0 < a) [Fintype (FiniteSymplecticFixed r a)]
variable (e : family.H ≃* FiniteSymplecticFixed r a) (b : family.Block)
variable (source : FamilyInputs family ha e b)
variable (dictionary : PhysicalDictionary family ha e b source)

abbrev ConcreteWeight := LiteralWeightFibre source.blockSource
  (FamilyInputs.toP38 family ha e b source).block

/-- The actual inverse fibre map chooses the family weight before any
normalizer or quotient reduction is transported. -/
def familyWeight (v : ConcreteWeight family ha e b source) :
    Definition35Weight (family.problem b) :=
  (FamilyInputs.weightFibreEquiv family ha e b source dictionary).symm v

def familyPair (v : ConcreteWeight family ha e b source) :
    CharacterWeight ell family.K family.H :=
  selectedCharacterWeight family.blockSource b
    (familyWeight family ha e b source dictionary v)

def concretePair (v : ConcreteWeight family ha e b source) :
    CharacterWeight ell family.K (FiniteSymplecticFixed r a) :=
  selectedCharacterWeight source.blockSource
    (FamilyInputs.toP38 family ha e b source).block v

/-- The whole-pair class premise follows from the existing two selections
and the inverse of the computed specified fibre equivalence. -/
theorem selected_class (v : ConcreteWeight family ha e b source) :
    weightClass (concretePair family ha e b source v) =
      weightClass ((familyPair family ha e b source dictionary v).mapGroupEquiv e) := by
  have hc := selectedCharacterWeight_spec source.blockSource
    (FamilyInputs.toP38 family ha e b source).block v
  have hf := selectedCharacterWeight_spec family.blockSource b
    (familyWeight family ha e b source dictionary v)
  have hi := congrArg Subtype.val
    ((FamilyInputs.weightFibreEquiv family ha e b source dictionary).apply_symm_apply v)
  change weightClass (concretePair family ha e b source v) = v.1 at hc
  change weightClass (familyPair family ha e b source dictionary v) =
    (familyWeight family ha e b source dictionary v).1 at hf
  change conjugacyClassGroupEquiv e
    (familyWeight family ha e b source dictionary v).1 = v.1 at hi
  change weightClass (concretePair family ha e b source v) =
    conjugacyClassGroupEquiv e (weightClass (familyPair family ha e b source dictionary v))
  exact hc.trans (hi.symm.trans (congrArg (conjugacyClassGroupEquiv e) hf).symm)

theorem exists_selected_pair (v : ConcreteWeight family ha e b source) :
    ∃ g : FiniteSymplecticFixed r a,
      (familyPair family ha e b source dictionary v).mapGroupEquiv (correctedEquiv e g) =
        concretePair family ha e b source v :=
  exists_corrected_pair (familyPair family ha e b source dictionary v)
    (concretePair family ha e b source v) e
    (selected_class family ha e b source dictionary v)

def selectedConjugator (v : ConcreteWeight family ha e b source) :
    FiniteSymplecticFixed r a :=
  Classical.choose (exists_selected_pair family ha e b source dictionary v)

def selectedEquiv (v : ConcreteWeight family ha e b source) :
    family.H ≃* FiniteSymplecticFixed r a :=
  correctedEquiv e (selectedConjugator family ha e b source dictionary v)

theorem selectedEquiv_pair (v : ConcreteWeight family ha e b source) :
    (familyPair family ha e b source dictionary v).mapGroupEquiv
        (selectedEquiv family ha e b source dictionary v) =
      concretePair family ha e b source v :=
  Classical.choose_spec (exists_selected_pair family ha e b source dictionary v)

def selectedNormalizerEquiv (v : ConcreteWeight family ha e b source) :
    Subgroup.normalizer ((familyPair family ha e b source dictionary v).subgroup : Set family.H) ≃*
      Subgroup.normalizer ((concretePair family ha e b source v).subgroup :
        Set (FiniteSymplecticFixed r a)) :=
  pairNormalizerEquiv (familyPair family ha e b source dictionary v)
    (concretePair family ha e b source v) (selectedEquiv family ha e b source dictionary v)
    (selectedEquiv_pair family ha e b source dictionary v)

def selectedQuotientEquiv (v : ConcreteWeight family ha e b source) :
    NormalizerQuotient (familyPair family ha e b source dictionary v).subgroup ≃*
      NormalizerQuotient (concretePair family ha e b source v).subgroup :=
  pairQuotientEquiv (familyPair family ha e b source dictionary v)
    (concretePair family ha e b source v) (selectedEquiv family ha e b source dictionary v)
    (selectedEquiv_pair family ha e b source dictionary v)

theorem selectedNormalizerEquiv_coe (v : ConcreteWeight family ha e b source)
    (x : Subgroup.normalizer
      ((familyPair family ha e b source dictionary v).subgroup : Set family.H)) :
    (selectedNormalizerEquiv family ha e b source dictionary v x : FiniteSymplecticFixed r a) =
      selectedEquiv family ha e b source dictionary v (x : family.H) :=
  pairNormalizerEquiv_coe (familyPair family ha e b source dictionary v)
    (concretePair family ha e b source v) (selectedEquiv family ha e b source dictionary v)
    (selectedEquiv_pair family ha e b source dictionary v) x

theorem selectedQuotientEquiv_mk (v : ConcreteWeight family ha e b source)
    (x : Subgroup.normalizer
      ((familyPair family ha e b source dictionary v).subgroup : Set family.H)) :
    selectedQuotientEquiv family ha e b source dictionary v (QuotientGroup.mk x) =
      QuotientGroup.mk (selectedNormalizerEquiv family ha e b source dictionary v x) :=
  pairQuotientEquiv_mk (familyPair family ha e b source dictionary v)
    (concretePair family ha e b source v) (selectedEquiv family ha e b source dictionary v)
    (selectedEquiv_pair family ha e b source dictionary v) x

theorem selectedQuotientEquiv_ownValues (v : ConcreteWeight family ha e b source)
    (x : NormalizerQuotient (familyPair family ha e b source dictionary v).subgroup) :
    (concretePair family ha e b source v).localCharacter
        (selectedQuotientEquiv family ha e b source dictionary v x) =
      (familyPair family ha e b source dictionary v).localCharacter x :=
  pairQuotientEquiv_ownValues (familyPair family ha e b source dictionary v)
    (concretePair family ha e b source v) (selectedEquiv family ha e b source dictionary v)
    (selectedEquiv_pair family ha e b source dictionary v) x

/-- This is literally the family's existing selected quotient packet. -/
def fixedFamilyReduction (v : ConcreteWeight family ha e b source) :
    SelectedLocalReductionSource family.blockSource b
      (familyWeight family ha e b source dictionary v) :=
  family.localReduction b (familyWeight family ha e b source dictionary v)

/-- The concrete chosen quotient reduction is computed from the exact
family table through the corrected WHOLE-pair quotient equivalence. -/
def chosenReduction (v : ConcreteWeight family ha e b source) :
    SelectedLocalReductionSource source.blockSource
      (FamilyInputs.toP38 family ha e b source).block v where
  iota := pairQuotientRoot (familyPair family ha e b source dictionary v)
    (concretePair family ha e b source v) (selectedEquiv family ha e b source dictionary v)
    (selectedEquiv_pair family ha e b source dictionary v)
    (fixedFamilyReduction family ha e b source dictionary v).iota
  brauer := pairQuotientBrauer (familyPair family ha e b source dictionary v)
    (concretePair family ha e b source v) (selectedEquiv family ha e b source dictionary v)
    (selectedEquiv_pair family ha e b source dictionary v)
    (fixedFamilyReduction family ha e b source dictionary v).iota
    (fixedFamilyReduction family ha e b source dictionary v).brauer
  reduction := pairQuotientBrauer_reduction (familyPair family ha e b source dictionary v)
    (concretePair family ha e b source v) (selectedEquiv family ha e b source dictionary v)
    (selectedEquiv_pair family ha e b source dictionary v)
    (fixedFamilyReduction family ha e b source dictionary v).iota
    (fixedFamilyReduction family ha e b source dictionary v).brauer
    (fixedFamilyReduction family ha e b source dictionary v).reduction

@[simp] theorem chosenReduction_root (v : ConcreteWeight family ha e b source) :
    (chosenReduction family ha e b source dictionary v).iota =
      (fixedFamilyReduction family ha e b source dictionary v).iota.alongMulEquiv
        (selectedQuotientEquiv family ha e b source dictionary v) := rfl

theorem chosenReduction_values (v : ConcreteWeight family ha e b source)
    (x : PrimeRegularElement
      (G := NormalizerQuotient (concretePair family ha e b source v).subgroup) ell) :
    (chosenReduction family ha e b source dictionary v).brauer.1 x =
      (fixedFamilyReduction family ha e b source dictionary v).brauer.1
        (PrimeRegularElement.map
          (selectedQuotientEquiv family ha e b source dictionary v).symm.toMonoidHom x) := rfl

/-- One chosen admissible family own-normalizer reduction transports through
the SAME whole-pair map. This constructor asserts no source root existence. -/
def chosenOwnReduction (v : ConcreteWeight family ha e b source)
    (R : OwnNormalizerReduction (k := family.k)
      (familyPair family ha e b source dictionary v)) :
    OwnNormalizerReduction (k := family.k) (concretePair family ha e b source v) :=
  pairOwnReduction (familyPair family ha e b source dictionary v)
    (concretePair family ha e b source v) (selectedEquiv family ha e b source dictionary v)
    (selectedEquiv_pair family ha e b source dictionary v) R

theorem chosenOwnReduction_horizontal (v : ConcreteWeight family ha e b source)
    (R : OwnNormalizerReduction (k := family.k)
      (familyPair family ha e b source dictionary v)) :
    RootCompatibleAlong
      (ownReductionRoot (concretePair family ha e b source v)
        (chosenOwnReduction family ha e b source dictionary v R))
      (ownReductionRoot (familyPair family ha e b source dictionary v) R)
      (selectedNormalizerEquiv family ha e b source dictionary v).toMonoidHom :=
  pairOwnReduction_horizontal (familyPair family ha e b source dictionary v)
    (concretePair family ha e b source v) (selectedEquiv family ha e b source dictionary v)
    (selectedEquiv_pair family ha e b source dictionary v) R

/-- The exact chosen quotient table, not an independent target table, is
compatible with the transported own-normalizer packet. -/
theorem chosenOwnReduction_quotientCompatible (v : ConcreteWeight family ha e b source)
    (R : OwnNormalizerReduction (k := family.k)
      (familyPair family ha e b source dictionary v))
    (compatible : RootCompatibleAlong
      (fixedFamilyReduction family ha e b source dictionary v).iota
      (ownReductionRoot (familyPair family ha e b source dictionary v) R)
      (normalizerProjection (familyPair family ha e b source dictionary v).subgroup)) :
    RootCompatibleAlong (chosenReduction family ha e b source dictionary v).iota
      (ownReductionRoot (concretePair family ha e b source v)
        (chosenOwnReduction family ha e b source dictionary v R))
      (normalizerProjection (concretePair family ha e b source v).subgroup) :=
  pairOwnReduction_quotientCompatible (familyPair family ha e b source dictionary v)
    (concretePair family ha e b source v) (selectedEquiv family ha e b source dictionary v)
    (selectedEquiv_pair family ha e b source dictionary v)
    (R := R) (rootQ := (fixedFamilyReduction family ha e b source dictionary v).iota)
    compatible

/-- The same chosen packet is compatible with the fixed P38 ambient root.
The generic K adapter removes only the inner correction from that root. -/
theorem chosenOwnReduction_ambientCompatible
    (v : ConcreteWeight family ha e b source)
    (R : OwnNormalizerReduction (k := family.k)
      (familyPair family ha e b source dictionary v))
    (compatible : RootCompatibleAlong family.iota
      (ownReductionRoot (familyPair family ha e b source dictionary v) R)
      (Subgroup.normalizer
        ((familyPair family ha e b source dictionary v).subgroup : Set family.H)).subtype) :
    RootCompatibleAlong (concreteRoot family e)
      (ownReductionRoot (concretePair family ha e b source v)
        (chosenOwnReduction family ha e b source dictionary v R))
      (Subgroup.normalizer ((concretePair family ha e b source v).subgroup :
        Set (FiniteSymplecticFixed r a))).subtype :=
  pairOwnReduction_correctedAmbientCompatible (familyPair family ha e b source dictionary v)
    (concretePair family ha e b source v) e
    (selectedConjugator family ha e b source dictionary v)
    (selectedEquiv_pair family ha e b source dictionary v) R family.iota compatible

/-- Replace only the freely chosen local quotient table, before applying
P38. No other literature input depends on that table. -/
def alignedInputs : FamilyInputs family ha e b :=
  { source with localReduction := chosenReduction family ha e b source dictionary }

/-- Both specified sources, catalogues and actions are literally unchanged. -/
def alignedDictionary : PhysicalDictionary family ha e b
    (alignedInputs family ha e b source dictionary) where
  familyAmbient := dictionary.familyAmbient
  ownNormalizerPrimitive := dictionary.ownNormalizerPrimitive
  familyAction := dictionary.familyAction
  concreteAction := dictionary.concreteAction

@[simp] theorem alignedInputs_localReduction
    (v : ConcreteWeight family ha e b source) :
    (alignedInputs family ha e b source dictionary).localReduction v =
      chosenReduction family ha e b source dictionary v := rfl

@[simp] theorem alignedInputs_toP38_localReduction
    (v : ConcreteWeight family ha e b source) :
    (FamilyInputs.toP38 family ha e b
        (alignedInputs family ha e b source dictionary)).localReduction v =
      chosenReduction family ha e b source dictionary v := rfl

/-- The protected bridge is applied to the computed table. Its existential
choice is not asserted equal to the former unrelated-table endgame. -/
def alignedFamilyBijection :
    Definition35Brauer (family.problem b) ≃ Definition35Weight (family.problem b) :=
  FamilyInputs.familyBijection family ha e b
    (alignedInputs family ha e b source dictionary)
    (alignedDictionary family ha e b source dictionary)

/-- Exact own-fibre composition for THIS rebuilt P38 endgame. -/
theorem alignedFamilyBijection_formula (psi : Definition35Brauer (family.problem b)) :
    letI := source.finiteFieldOpp
    letI := source.cyclicFieldOpp
    letI := source.finiteField
    letI := source.cyclicField
    FamilyInputs.weightFibreEquiv family ha e b source dictionary
        (alignedFamilyBijection family ha e b source dictionary psi) =
      (FamilyInputs.toP38 family ha e b
          (alignedInputs family ha e b source dictionary)).endgame.omega.toEquiv
        (FamilyInputs.brauerFibreEquiv family ha e b source psi) := by
  letI := source.finiteFieldOpp
  letI := source.cyclicFieldOpp
  letI := source.finiteField
  letI := source.cyclicField
  exact FamilyInputs.familyBijection_formula family ha e b
    (alignedInputs family ha e b source dictionary)
    (alignedDictionary family ha e b source dictionary) psi

end ModularRep.PaperProofs.EvenFieldP38ChosenFamilyReduction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
