import ModularRep.PaperProofs.EvenFieldProposition39HighRankU0
import ModularRep.PaperProofs.EvenFieldPhysicalBlockFibreReindexing

/-!
# Proposition 3.8 on the classified family's own coefficients and block

The input below fixes k, K and the concrete root before any P38 data are
supplied: they are the given family's coefficients and its root transported
along the actual group equivalence. The concrete block is also computed
from the two specified catalogues. There is no independent P38 packet plus
an asserted equality of coefficient fields, roots or selected blocks.

The existing protected P38 bridge supplies the concrete bijection. Its
composition with the two computed specified fibre maps yields a bijection
on the SAME family block. Both local block sources remain the supplied
ones. No selected-pair/reduction identification or Definition 3.5 relation
is assumed or produced. The chosen-packet and SAME-standard joins remain
separate from the coefficient/specified-fibre application completed here.
-/

noncomputable section

open scoped MonoidAlgebra Pointwise

namespace ModularRep.PaperProofs.EvenFieldClassifiedP38FamilyPacket

open Formalisation ModularRep ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero ModularRep.IBrBlockBasicSetBridge
open ModularRep.IBrBlockBasicSetBridge.RestrictedIntegralBasicSetOnIBrBlock
open ModularRep.IntegralBasicSetBridge
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.ManuscriptVerification.EvenUnipotentCorrespondence
open ModularRep.OrdinaryIrreducibleCharacter
open CyclicOuterLemma37ActualBlockFibres CyclicOuterLemma37Concrete
open CyclicOuterLemma37LiteralLocalExtension
open EvenFieldConcreteLemma35 EvenFieldConcreteProposition38Actual
open EvenFieldConcreteTypeC EvenFieldEJGCPairActual EvenFieldFMZGenericPair
open EvenFieldFLZDefinition35Family EvenFieldFLZFullHG EvenFieldFLZSourceConditions
open EvenFieldLemma35E1E4Providers EvenFieldLemmas35_36Actual
open EvenFieldOrdinaryCharacters EvenFieldProposition38Lemma37Bridge
open ModularRep.PaperProofs.EvenFieldProposition39HighRankU0
open ModularRep.PaperProofs.EvenFieldProposition39Relative
open EvenFieldPhysicalBlockFibreReindexing EvenFieldBlockGroupEquivCoordinates
open OddTwoGroupEquivWeightBlocks

section FixedCoefficients

variable {ell r a : ℕ} (family : Definition35Family.{0} ell)
variable (ha : 0 < a) [Fintype (FiniteSymplecticFixed r a)]
variable (e : family.H ≃* FiniteSymplecticFixed r a) (b : family.Block)

/-- The actual concrete root, with exactly the family's coefficient instances. -/
def concreteRoot : PrimeRegularRootEmbedding ell family.k family.K
    (FiniteSymplecticFixed r a) := family.iota.alongMulEquiv e

def concreteInjectivity : IrreducibleBrauerCharacterInjectivity (concreteRoot family e) :=
  irreducibleBrauerCharacterInjectivity_of_rootEmbedding (concreteRoot family e)

/-- Exact P38 source inputs with coefficients, ambient root and block fixed
by the classified family's specified coordinates. The remaining fields are
the original P38 E1/E2 playlist, not an endgame or relation witness. -/
structure FamilyInputs where
  A : Type
  Dual : Type
  CitedRelativeWeylGroup : Type
  O : Type
  Block : Type
  [groupDual : Group Dual]
  [fintypeDual : Fintype Dual]
  [groupCitedRelativeWeylGroup : Group CitedRelativeWeylGroup]
  [commRingO : CommRing O]
  [isDomainO : IsDomain O]
  [algebraOK : Algebra O family.K]
  [finiteFieldOpp : Finite (FieldGroup a)ᵐᵒᵖ]
  [cyclicFieldOpp : IsCyclic (FieldGroup a)ᵐᵒᵖ]
  [finiteField : Finite (FieldGroup a)]
  [cyclicField : IsCyclic (FieldGroup a)]
  [mulActionA : MulAction (MulAut (FiniteSymplecticFixed r a)) A]
  [fintypeBlock : Fintype Block]
  [mulActionBlock : MulAction (MulAut (FiniteSymplecticFixed r a))ᵐᵒᵖ Block]
  blockIdempotent : Block → family.k[FiniteSymplecticFixed r a]
  blocks : BlockIdempotentDecomposition blockIdempotent
  D : Definitions ℂ (FiniteSymplecticFixed r a) A Block
  coherence : InnerCoherence D
  S35 : Inputs (A := A) (Block := Block) (Dual := Dual)
    r a ell ha D coherence (blockLabelEquiv family.blocks blocks e b)
  pairs : PairClassSource ell family.k D
  initial : pairs.RestrictedPair (blockLabelEquiv family.blocks blocks e b)
  GeneralisedSeries : Set (Irr ℂ (FiniteSymplecticFixed r a))
  [fintypeW : Fintype (W D coherence (blockLabelEquiv family.blocks blocks e b))]
  [fintypeDefectZeroUnion :
    Fintype (pairs.DefectZeroUnion (blockLabelEquiv family.blocks blocks e b))]
  cited : EvenFieldLemmas35_36Actual.CitedData
    (CitedRelativeWeylGroup := CitedRelativeWeylGroup)
    ell (S35.e1e4.toExactProvider r a ell ha).inBlock
    (S35.e1e4.toExactProvider r a ell ha).globalSeries.series
    D coherence (blockLabelEquiv family.blocks blocks e b)
    pairs initial GeneralisedSeries
  blockSource : LocalBlockInductionSource
    (p := ell) (k := family.k) (K := family.K)
    (G := FiniteSymplecticFixed r a) (Block := Block)
  alignment : AmbientBlockAlignment D pairs blockIdempotent blockSource
  T : FibreTransportSource (concreteRoot family e) (concreteInjectivity family e)
    blocks (fieldAction r a ha) (blockLabelEquiv family.blocks blocks e b)
  Msys : ModularSystem ell family.K O family.k
  hcompat : StableReductionBrauerCharacterCompatibility Msys (concreteRoot family e)
  basicSet : RestrictedIntegralBasicSetOnIBrBlock
    (concreteRoot family e) (concreteInjectivity family e) blocks
    (blockLabelEquiv family.blocks blocks e b)
    (↑(XC ell (S35.e1e4.toExactProvider r a ell ha).inBlock
      (S35.e1e4.toExactProvider r a ell ha).globalSeries.series))
    (decompositionMapOfStableReduction Msys (concreteRoot family e) hcompat)
  [finiteXC : Finite (↑(XC ell
    (S35.e1e4.toExactProvider r a ell ha).inBlock
    (S35.e1e4.toExactProvider r a ell ha).globalSeries.series))]
  fmz62 :
    let hfixed := oppositeFieldBlock_fixed_of_fibreTransport
      (ha := ha) (iota := concreteRoot family e)
      (hinj := concreteInjectivity family e) (blocks := blocks)
      (block := blockLabelEquiv family.blocks blocks e b) (T := T)
    FMZ62TypeCRestrictedApplication r a ell ha D coherence
      (blockLabelEquiv family.blocks blocks e b) S35 pairs blockSource alignment hfixed
  conlon : PaperProofs.ConlonBasicSet.PadicConlonMarkDetection.{0, 0}
    (p := 2) (A := (FieldGroup a)ᵐᵒᵖ)
  burnside : PaperProofs.ConlonBasicSet.PublishedBurnsideMarkInjectivity.{0, 0}
    (A := (FieldGroup a)ᵐᵒᵖ)
  principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} ell family.k
  localReduction : ∀ w : LiteralWeightFibre blockSource
      (blockLabelEquiv family.blocks blocks e b),
    SelectedLocalReductionSource blockSource (blockLabelEquiv family.blocks blocks e b) w
  ordinary :
    let fixation := EvenFieldLemmas35_36Actual.lemma_3_5_actual
      r a ell ha D coherence (blockLabelEquiv family.blocks blocks e b) S35
    let _ : MulAction (FieldGroup a)ᵐᵒᵖ
        (↑(XC ell (S35.e1e4.toExactProvider r a ell ha).inBlock
          (S35.e1e4.toExactProvider r a ell ha).globalSeries.series)) :=
      characterOppositeMulAction fixation
    OrdinaryTwistCompatibleLabels basicSet (oppositeFieldAction r a ha)

attribute [instance]
  FamilyInputs.groupDual FamilyInputs.fintypeDual
  FamilyInputs.groupCitedRelativeWeylGroup FamilyInputs.commRingO
  FamilyInputs.isDomainO FamilyInputs.algebraOK
  FamilyInputs.mulActionA FamilyInputs.fintypeBlock FamilyInputs.mulActionBlock
  FamilyInputs.fintypeW FamilyInputs.fintypeDefectZeroUnion FamilyInputs.finiteXC

variable (source : FamilyInputs family ha e b)

/-- Rebuild the old protected packet from the fixed data, rather than cast
an unrelated packet using claimed coefficient/root equalities. -/
def FamilyInputs.toP38 : P38LiteralBridgeInputs r a ell ha where
  A := source.A
  Dual := source.Dual
  CitedRelativeWeylGroup := source.CitedRelativeWeylGroup
  K := family.K
  O := source.O
  k := family.k
  ι := source.Block
  groupDual := source.groupDual
  fintypeDual := source.fintypeDual
  groupCitedRelativeWeylGroup := source.groupCitedRelativeWeylGroup
  fieldK := family.fieldK
  commRingO := source.commRingO
  isDomainO := source.isDomainO
  fieldk := family.fieldk
  algebraOK := source.algebraOK
  charZeroK := family.charZeroK
  charPk := family.charPk
  algClosedk := family.algClosedk
  fintypeFixed := inferInstance
  finiteFieldOpp := source.finiteFieldOpp
  cyclicFieldOpp := source.cyclicFieldOpp
  finiteField := source.finiteField
  cyclicField := source.cyclicField
  mulActionA := source.mulActionA
  fintypeBlock := source.fintypeBlock
  mulActionBlock := source.mulActionBlock
  D := source.D
  coherence := source.coherence
  block := blockLabelEquiv family.blocks source.blocks e b
  S35 := source.S35
  pairs := source.pairs
  initial := source.initial
  GeneralisedSeries := source.GeneralisedSeries
  fintypeW := source.fintypeW
  fintypeDefectZeroUnion := source.fintypeDefectZeroUnion
  cited := source.cited
  iota := concreteRoot family e
  hinj := concreteInjectivity family e
  blockIdempotent := source.blockIdempotent
  blocks := source.blocks
  blockSource := source.blockSource
  alignment := source.alignment
  T := source.T
  Msys := source.Msys
  hcompat := source.hcompat
  basicSet := source.basicSet
  finiteXC := source.finiteXC
  fmz62 := source.fmz62
  conlon := source.conlon
  burnside := source.burnside
  principle := source.principle
  localReduction := source.localReduction
  ordinary := source.ordinary

@[simp] theorem FamilyInputs.toP38_k : (FamilyInputs.toP38 family ha e b source).k = family.k := rfl
@[simp] theorem FamilyInputs.toP38_K : (FamilyInputs.toP38 family ha e b source).K = family.K := rfl

@[simp] theorem FamilyInputs.toP38_root :
    (FamilyInputs.toP38 family ha e b source).iota = family.iota.alongMulEquiv e := rfl

/-- The chosen concrete block is the actual image primitive of b. -/
theorem FamilyInputs.selected_primitive :
    source.blockIdempotent (FamilyInputs.toP38 family ha e b source).block =
      MonoidAlgebra.domCongr family.k family.k e (family.blockIdempotent b) :=
  blockLabelEquiv_primitive family.blocks source.blocks e b

/-- The fixed original family root is the source of this actual fibre map;
its inverse returns to that same root, without double-transport equality. -/
def FamilyInputs.brauerFibreEquiv :
    Definition35Brauer (family.problem b) ≃
      BrauerFibre (concreteRoot family e) (concreteInjectivity family e)
        source.blocks (FamilyInputs.toP38 family ha e b source).block :=
  brauerEquiv family.blocks source.blocks e family.iota
    family.irreducibleBrauerInjective (concreteInjectivity family e) b

@[simp] theorem FamilyInputs.brauerFibreEquiv_values
    (psi : Definition35Brauer (family.problem b))
    (x : PrimeRegularElement (G := FiniteSymplecticFixed r a) ell) :
    (FamilyInputs.brauerFibreEquiv family ha e b source psi).1.1 x =
      psi.1.1 (PrimeRegularElement.map e.symm.toMonoidHom x) := rfl

/-- Underlying actual character action through the same e and root. -/
theorem FamilyInputs.brauerFibreEquiv_twist
    (psi : Definition35Brauer (family.problem b)) (g : (MulAut family.H)ᵐᵒᵖ) :
    IrreducibleBrauerCharacter.equivAlongMulEquiv family.iota e
        (@HSMul.hSMul (MulAut family.H)ᵐᵒᵖ (IBr family.iota) (IBr family.iota)
          inferInstance g psi.1) =
      @HSMul.hSMul (MulAut (FiniteSymplecticFixed r a))ᵐᵒᵖ
        (IBr (concreteRoot family e)) (IBr (concreteRoot family e)) inferInstance
        (oppositeAutEquiv e g) (FamilyInputs.brauerFibreEquiv family ha e b source psi).1 :=
  IrreducibleBrauerCharacter.equivAlongMulEquiv_op_smul family.iota e psi.1 g

/-- Only individual specified source laws. The concrete ambient equation
is already part of source.alignment and is not supplied a second time. -/
structure PhysicalDictionary : Prop where
  familyAmbient : ∀ c : family.Block,
    family.blockSource.operations.ambientBlockData.blockIdempotent c =
      family.blockIdempotent c
  ownNormalizerPrimitive : ∀ W : CharacterWeight ell family.K family.H,
    MonoidAlgebra.domCongr family.k family.k (normalizerEquiv e W.subgroup)
        (ownNormalizerBlock family.blockSource.operations W).1 =
      (ownNormalizerBlock source.blockSource.operations (W.mapGroupEquiv e)).1
  familyAction : PhysicalBlockAction family.blockIdempotent
  concreteAction : PhysicalBlockAction source.blockIdempotent

variable (dictionary : PhysicalDictionary family ha e b source)

/-- Restrict the same whole-pair map to the actual family and concrete
sources at the computed specified block. -/
def FamilyInputs.weightFibreEquiv :
    Definition35Weight (family.problem b) ≃
      LiteralWeightFibre source.blockSource (FamilyInputs.toP38 family ha e b source).block :=
  weightEquiv family.blocks source.blocks e family.blockSource source.blockSource
    dictionary.familyAmbient (fun c => (source.alignment.brauer_idempotent c).symm)
    dictionary.ownNormalizerPrimitive b

@[simp] theorem FamilyInputs.weightFibreEquiv_val
    (w : Definition35Weight (family.problem b)) :
    (FamilyInputs.weightFibreEquiv family ha e b source dictionary w).1 =
      conjugacyClassGroupEquiv e w.1 := rfl

/-- Underlying whole-pair class action, retaining both actual block sources. -/
theorem FamilyInputs.weightFibreEquiv_twist
    (w : Definition35Weight (family.problem b)) (g : (MulAut family.H)ᵐᵒᵖ) :
    conjugacyClassGroupEquiv e
        (@HSMul.hSMul (MulAut family.H)ᵐᵒᵖ
          (CharacterWeight.ConjugacyClass (p := ell) (K := family.K) (G := family.H))
          (CharacterWeight.ConjugacyClass (p := ell) (K := family.K) (G := family.H))
          inferInstance g w.1) =
      @HSMul.hSMul (MulAut (FiniteSymplecticFixed r a))ᵐᵒᵖ
        (CharacterWeight.ConjugacyClass (p := ell) (K := family.K)
          (G := FiniteSymplecticFixed r a))
        (CharacterWeight.ConjugacyClass (p := ell) (K := family.K)
          (G := FiniteSymplecticFixed r a)) inferInstance (oppositeAutEquiv e g)
        (FamilyInputs.weightFibreEquiv family ha e b source dictionary w).1 :=
  conjugacyClassGroupEquiv_op_smul e g w.1

/-- Actual full BLOCK stabilizers; no principal-block/full-Aut shortcut. -/
def FamilyInputs.blockStabilizerEquiv :
    MulAction.stabilizer (MulAut family.H)ᵐᵒᵖ b ≃*
      MulAction.stabilizer (MulAut (FiniteSymplecticFixed r a))ᵐᵒᵖ
        (FamilyInputs.toP38 family ha e b source).block :=
  stabilizerEquiv family.blocks source.blocks e
    dictionary.familyAction dictionary.concreteAction b

@[simp] theorem FamilyInputs.blockStabilizerEquiv_coe
    (g : MulAction.stabilizer (MulAut family.H)ᵐᵒᵖ b) :
    (FamilyInputs.blockStabilizerEquiv family ha e b source dictionary g).1 =
      oppositeAutEquiv e g.1 := rfl

/-- Existing family Gamma presentation, followed by the computed actual
block-stabilizer map. The adapter is separate from family.automorphisms. -/
def FamilyInputs.gammaToConcreteStabilizer
    (adapter : Definition35AutomorphismStabilizerAdapter (family.problem b)) :
    (family.problem b).Gamma ≃*
      MulAction.stabilizer (MulAut (FiniteSymplecticFixed r a))ᵐᵒᵖ
        (FamilyInputs.toP38 family ha e b source).block :=
  adapter.equiv.trans (FamilyInputs.blockStabilizerEquiv family ha e b source dictionary)

theorem FamilyInputs.gammaToConcreteStabilizer_coe
    (adapter : Definition35AutomorphismStabilizerAdapter (family.problem b))
    (g : (family.problem b).Gamma) :
    (FamilyInputs.gammaToConcreteStabilizer family ha e b source dictionary adapter g).1 =
      oppositeAutEquiv e (inverseOpHom (family.problem b).gamma g) := by
  change oppositeAutEquiv e (adapter.equiv g).1 = _
  exact congrArg (oppositeAutEquiv e) (adapter.equiv_coe g)

/-- The existing protected P38--Lemma37 endgame, not a new conclusion field. -/
def FamilyInputs.familyBijection :
    Definition35Brauer (family.problem b) ≃ Definition35Weight (family.problem b) := by
  letI := source.finiteFieldOpp
  letI := source.cyclicFieldOpp
  letI := source.finiteField
  letI := source.cyclicField
  exact (FamilyInputs.brauerFibreEquiv family ha e b source).trans
    ((FamilyInputs.toP38 family ha e b source).endgame.omega.toEquiv.trans
      (FamilyInputs.weightFibreEquiv family ha e b source dictionary).symm)

/-- The family output uses exactly the protected concrete omega on the
transported input, followed by the inverse actual whole-pair map. -/
theorem FamilyInputs.familyBijection_formula
    (psi : Definition35Brauer (family.problem b)) :
    letI := source.finiteFieldOpp
    letI := source.cyclicFieldOpp
    letI := source.finiteField
    letI := source.cyclicField
    FamilyInputs.weightFibreEquiv family ha e b source dictionary
        (FamilyInputs.familyBijection family ha e b source dictionary psi) =
      (FamilyInputs.toP38 family ha e b source).endgame.omega.toEquiv
        (FamilyInputs.brauerFibreEquiv family ha e b source psi) := by
  letI := source.finiteFieldOpp
  letI := source.cyclicFieldOpp
  letI := source.finiteField
  letI := source.cyclicField
  exact (FamilyInputs.weightFibreEquiv family ha e b source dictionary).apply_symm_apply _

end FixedCoefficients

section ClassifiedApplication

variable {ell : ℕ} {scope : FLZFullHGUniverse 2 ell}
variable {coverage : FullHGDefinition35Coverage scope}
variable {classification : FullHGTypeCClassificationSource scope}
variable (pair : FullHG scope) (parameter : HighRankParameter)
variable (hcase : classification.structuralCase coverage pair =
  .typeC (.rankAtLeastFour parameter))
variable (model : HighRankPairConcreteModelU0 classification pair parameter hcase)
variable (b : (coverage.presentation pair).family.Block)

/-- Classified inputs use the exact own rank, positive field exponent,
family and fixed-point presentation. This is a typed source packet, not an
alias for an arbitrary model map or an arbitrary old P38 packet. -/
abbrev ClassifiedInputs :=
  letI := finiteSymplecticFixedFintype parameter.rank parameter.fieldExponent
    parameter.positiveFieldExponent
  FamilyInputs (coverage.presentation pair).family parameter.positiveFieldExponent
    (model.familyToConcrete (coverage.presentation pair)) b

/-- Concrete consumption on the classified family's selected specified
block. This has no relation, selected-root or final iBAW premise/output. -/
def classifiedFamilyBijection (source : ClassifiedInputs pair parameter hcase model b)
    (dictionary :
      letI := finiteSymplecticFixedFintype parameter.rank parameter.fieldExponent
        parameter.positiveFieldExponent
      PhysicalDictionary (coverage.presentation pair).family
        parameter.positiveFieldExponent
        (model.familyToConcrete (coverage.presentation pair)) b source) :
    Definition35Brauer ((coverage.presentation pair).family.problem b) ≃
      Definition35Weight ((coverage.presentation pair).family.problem b) := by
  letI := finiteSymplecticFixedFintype parameter.rank parameter.fieldExponent
    parameter.positiveFieldExponent
  exact FamilyInputs.familyBijection (coverage.presentation pair).family
    parameter.positiveFieldExponent
    (model.familyToConcrete (coverage.presentation pair)) b source dictionary

end ClassifiedApplication

end ModularRep.PaperProofs.EvenFieldClassifiedP38FamilyPacket


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
