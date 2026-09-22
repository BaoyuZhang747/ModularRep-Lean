import ModularRep.PaperProofs.EvenFieldAmbientExtensionBridge
import ModularRep.PaperProofs.EvenFieldAlgebraicTorusLabelFixation
import ModularRep.PaperProofs.EvenFieldGenericLeviSeries
import ModularRep.PaperProofs.EvenFieldGenericOrbitUnified
import ModularRep.PaperProofs.EvenFieldLemma35Conclusion
import ModularRep.PaperProofs.EvenFieldUnifiedRationalLeviFMZ

/-!
# Full relative form of Lemma 3.6

This module gives source structures and the full relative theorem.  None of
the source fields states fixation of a selected character, a generic pair, or
an orbit.  The rational Levi, Weyl representative, and Lang element are
chosen once for each valid representative.  Their compatibility with the
individual field automorphisms is universally quantified over the typed
field group.

The field group acts homomorphically on the finite fixed-point group.  Its
lifts to the ambient algebraic group are deliberately only a pointwise
family of automorphisms.  For a field group of order `a`, the usual lift of
its generator is the Frobenius map `F₂`, but `F₂ ^ a = F'` is not the identity
on the algebraic group even though its restriction to the `F'`-fixed points
is the identity.  Thus a homomorphic lift of the finite cyclic action to the
algebraic group is neither required here nor generally available.
-/

namespace ModularRep.PaperProofs.EvenFieldLemma35Relative

open ModularRep.PaperProofs.CharacterInductionEquivariance
open ModularRep.ManuscriptVerification.EvenFieldFixed
open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPair
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusLabelFixation
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPairAssembly
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPairInertiaBridge
open ModularRep.PaperProofs.EvenFieldAmbientExtension
open ModularRep.PaperProofs.EvenFieldGallagherFormula
open ModularRep.PaperProofs.EvenFieldFMZGenericPair
open ModularRep.PaperProofs.EvenFieldGenericLeviSeries
open ModularRep.PaperProofs.EvenFieldGenericOrbitUnified
open ModularRep.PaperProofs.EvenFieldLangInnerTwist
open ModularRep.PaperProofs.EvenFieldLemma35Conclusion
open ModularRep.PaperProofs.EvenFieldLeviTorus
open ModularRep.PaperProofs.EvenFieldLocalCharacterFormula
open ModularRep.PaperProofs.EvenFieldRelativeDifferenceAdapter
open ModularRep.PaperProofs.EvenFieldSourceShaped
open ModularRep.PaperProofs.EvenFieldUnifiedRationalLevi

universe u

variable {k Gbar A Block E Dual : Type u}
    [Field k] [CharZero k] [Group Gbar] [Group E] [Group Dual]

/-- The part of a rational-Levi witness which is independent of the chosen
element of the field-automorphism group.  It packages E6--E7 once for one
generic representative. -/
structure StaticRationalLeviSource
    (F : Gbar →* Gbar) (algebraicLift : E → MulAut Gbar)
    (commute : ∀ (sigma : E) (x : Gbar),
      F (algebraicLift sigma x) = algebraicLift sigma (F x)) where
  standardLevi : Subgroup Gbar
  standardLevi_F_stable : standardLevi.map F = standardLevi
  standardLevi_sigma_stable : ∀ sigma : E,
    standardLevi.map (algebraicLift sigma).toMonoidHom = standardLevi
  representative : Gbar
  representative_normalises :
    representative ∈ Subgroup.normalizer (standardLevi : Set Gbar)
  representative_fixed : ∀ sigma : E,
    algebraicLift sigma representative = representative
  langElement : Gbar
  langEquation : langElement⁻¹ * F langElement = representative

/-- The unified witness for one field automorphism.  All fields not involving
that automorphism are inherited from the same static source. -/
def StaticRationalLeviSource.unified
    {F : Gbar →* Gbar} {algebraicLift : E → MulAut Gbar}
    {commute : ∀ (sigma : E) (x : Gbar),
      F (algebraicLift sigma x) = algebraicLift sigma (F x)}
    (R : StaticRationalLeviSource F algebraicLift commute) (sigma : E) :
    EvenFieldUnifiedRationalLevi.Data F (algebraicLift sigma) (commute sigma) where
  standardLevi := R.standardLevi
  standardLevi_F_stable := R.standardLevi_F_stable
  standardLevi_sigma_stable := R.standardLevi_sigma_stable sigma
  representative := R.representative
  representative_normalises := R.representative_normalises
  representative_fixed := R.representative_fixed sigma
  langElement := R.langElement
  langEquation := R.langEquation

variable (F : Gbar →* Gbar) (algebraicLift : E → MulAut Gbar)
  (commute : ∀ (sigma : E) (x : Gbar),
    F (algebraicLift sigma x) = algebraicLift sigma (F x))

abbrev H := frobeniusFixedSubgroup F

/-- Global source data for the fixed block.  `fieldAction` is the genuine
homomorphic action on the finite fixed-point group.  `fieldAction_coe` says
that, one element at a time, it is the restriction of the chosen pointwise
algebraic lift.  The remaining fields are E1--E4 and the
characteristic-torus realisation used in the checked deduction. -/
structure GlobalInputs
    [MulAction (MulAut (H F)) A]
    (ell : ℕ) (InBlock : Irr k (H F) → Prop)
    (Series : Irr k (H F) → Dual → Prop)
    (D : Definitions k (H F) A Block) (C : Block) where
  fieldAction : E →* MulAut (H F)
  fieldAction_coe : ∀ (sigma : E) (x : H F),
    ((fieldAction sigma x : H F) : Gbar) = algebraicLift sigma (x : Gbar)
  blockSeries :
    EvenFieldOrdinaryCharacters.E1BlockEllSeriesInput ell InBlock Series
  seriesDisjoint :
    EvenFieldOrdinaryCharacters.E2CommonSeriesLabelsConjugateInput Series
  fieldFixesIdentitySeries :
    EvenFieldOrdinaryCharacters.E3StandardFieldFixesUnipotentInput
      Series fieldAction
  blockLabel : Block → Dual
  blockLabel_eq_one : blockLabel C = 1
  selectedSeries : (T : A) → Irr k (D.levi T) → Dual → Prop
  labelComparison :
    E4GenericLabelComparisonInput D C blockLabel selectedSeries
  centralSylow : Subgroup Gbar → Subgroup Gbar
  centralSylow_natural : CharacteristicTorusNatural centralSylow
  realise : A → Subgroup Gbar
  realise_injective : Function.Injective realise

/-- Source data for one valid FMZ representative.  The carrier of the Weyl
normaliser and the rational-Levi data are chosen once.  The E5 identification,
the E8 representative data, the standard rational-series predicate, and E3
are then required uniformly for every element of the typed field group. -/
structure PairGeometrySource
    [MulAction (MulAut (H F)) A]
    {ell : ℕ} {InBlock : Irr k (H F) → Prop}
    {Series : Irr k (H F) → Dual → Prop}
    {D : Definitions k (H F) A Block} {coherence : InnerCoherence D}
    {C : Block}
    (global : GlobalInputs F algebraicLift ell InBlock Series D C)
    (v : GenericPair D coherence C) where
  generic : GenericWitness D C v.1
  rational : StaticRationalLeviSource F algebraicLift commute
  realise_selected :
    global.realise v.1.1 =
      global.centralSylow
        (conjugateSubgroup rational.standardLevi rational.langElement)
  realise_transport : ∀ sigma : E,
    global.realise
        ((rational.unified sigma).langData.tau • v.1.1) =
      (global.realise v.1.1).map
        (innerTwistedAut (algebraicLift sigma) rational.langElement).toMonoidHom
  fmz : ∀ sigma : E,
    FMZIdentification (rational.unified sigma) D v.1
  WeylNormalizer : Type u
  [weylNormalizerGroup : Group WeylNormalizer]
  WeylLevi : Subgroup WeylNormalizer
  weyl : ∀ sigma : E,
    WeylRepresentativeData
      (rational.unified sigma).twistedFrobenius
      (algebraicLift sigma).toMonoidHom
      (rational.unified sigma).commute_twistedFrobenius
      (rational.unified sigma).standardFixedNormalizer
      (rational.unified sigma).standardFixedNormalizer_stable
      (rational.unified sigma).standardLevi
      WeylNormalizer WeylLevi
  standardSeries :
    Irr k (rational.unified (1 : E)).standardFiniteLevi → Dual → Prop
  standardFieldAction :
    E →* MulAut (rational.unified (1 : E)).standardFiniteLevi
  standardFieldAction_eq : ∀ sigma : E,
    (rational.unified sigma).standardFieldAut = standardFieldAction sigma
  seriesTransport : ∀ (sigma : E)
      (chi : Irr k (rational.unified sigma).standardFiniteLevi) (s : Dual),
    standardSeries chi s ↔
      global.selectedSeries v.1.1
        (transportIrr (fmz sigma).standardFiniteLeviEquivFMZ chi) s
  fieldFixesStandardSeries :
    EvenFieldOrdinaryCharacters.E3StandardFieldFixesUnipotentInput
      standardSeries standardFieldAction

attribute [instance] PairGeometrySource.weylNormalizerGroup

/-- The coherent E8 package derived from the static rational-Levi source,
the E5 identification, and the E8 Weyl data. -/
noncomputable def PairGeometrySource.e8
    [MulAction (MulAut (H F)) A]
    {ell : ℕ} {InBlock : Irr k (H F) → Prop}
    {Series : Irr k (H F) → Dual → Prop}
    {D : Definitions k (H F) A Block} {coherence : InnerCoherence D}
    {C : Block}
    {global : GlobalInputs F algebraicLift ell InBlock Series D C}
    {v : GenericPair D coherence C}
    (geometry : PairGeometrySource F algebraicLift commute global v)
    (sigma : E) :=
  (geometry.fmz sigma).e8Data geometry.WeylNormalizer geometry.WeylLevi
    (geometry.weyl sigma)

/-- Character-theoretic E9--E11 data for one valid representative.  The
normality instance is intended to be the theorem `fmzLevi_normal` derived
from the E5 identification, not an additional external source. -/
structure PairCharacterSource
    [MulAction (MulAut (H F)) A]
    {ell : ℕ} {InBlock : Irr k (H F) → Prop}
    {Series : Irr k (H F) → Dual → Prop}
    {D : Definitions k (H F) A Block} {coherence : InnerCoherence D}
    {C : Block}
    {global : GlobalInputs F algebraicLift ell InBlock Series D C}
    {v : GenericPair D coherence C}
    (geometry : PairGeometrySource F algebraicLift commute global v)
    [baseNormal : (D.levi v.1.1).Normal]
    [finiteNormalizerFintype : Fintype
      (finiteNormalizer (H := H F) (A := A) v.1.1)] where
  AmbientGroup : Type u
  [ambientGroup : Group AmbientGroup]
  ambient : EvenFieldAmbientExtension.Data
    (D.levi v.1.1) geometry.generic.lambda AmbientGroup
  ambientConjugation : ∀ (sigma : E)
      (label_fixed :
        (geometry.rational.unified sigma).langData.tau • v.1.1 = v.1.1)
      (lambda_fixed :
        twist k (D.levi v.1.1) geometry.generic.lambda
          (restrictAut (D.levi v.1.1)
            (inducedFiniteNormalizerAut
              (geometry.rational.unified sigma).langData.tau v.1.1
              label_fixed)
            (subgroup_stable_of_difference (D.levi v.1.1)
              (inducedFiniteNormalizerAut
                (geometry.rational.unified sigma).langData.tau v.1.1
                label_fixed)
              ((geometry.fmz sigma).relativeDifference_of_weylData
                geometry.WeylNormalizer geometry.WeylLevi
                (geometry.weyl sigma) label_fixed))) =
          geometry.generic.lambda),
    EvenFieldAmbientExtension.ConjugationWitness ambient
      (restrictAut
        (characterInertia (D.levi v.1.1) geometry.generic.lambda)
        (inducedFiniteNormalizerAut
          (geometry.rational.unified sigma).langData.tau v.1.1 label_fixed)
        (characterInertia_stable_of_difference
          (D.levi v.1.1) geometry.generic.lambda
          (inducedFiniteNormalizerAut
            (geometry.rational.unified sigma).langData.tau v.1.1 label_fixed)
          ((geometry.fmz sigma).relativeDifference_of_weylData
            geometry.WeylNormalizer geometry.WeylLevi
            (geometry.weyl sigma) label_fixed)
          lambda_fixed))
  kappa : Irr k
    (characterInertia (D.levi v.1.1) geometry.generic.lambda)
  gallagher : HasGallagherFactorisation
    (baseInInertia (D.levi v.1.1) geometry.generic.lambda)
    ambient.extensionIrr kappa
  clifford : HasCliffordInduction
    (characterInertia (D.levi v.1.1) geometry.generic.lambda)
    kappa v.1.2

/-- Install the normality proof derived from E5 before asking for E9--E11
character data.  Finiteness of the literal finite normaliser is structural
source data, not a character or orbit conclusion. -/
structure CharacterSourceFor
    [MulAction (MulAut (H F)) A]
    {ell : ℕ} {InBlock : Irr k (H F) → Prop}
    {Series : Irr k (H F) → Dual → Prop}
    {D : Definitions k (H F) A Block} {coherence : InnerCoherence D}
    {C : Block}
    {global : GlobalInputs F algebraicLift ell InBlock Series D C}
    {v : GenericPair D coherence C}
    (geometry : PairGeometrySource F algebraicLift commute global v) where
  [finiteNormalizerFintype : Fintype
    (finiteNormalizer (H := H F) (A := A) v.1.1)]
  data :
    letI : (D.levi v.1.1).Normal :=
      (geometry.fmz (1 : E)).fmzLevi_normal
    PairCharacterSource F algebraicLift commute geometry

/-- The finite field automorphism constructed from any static rational-Levi
source is the globally declared field action.  Both sides restrict the same
pointwise algebraic lift `algebraicLift sigma`. -/
theorem PairGeometrySource.langFieldAut_eq_global
    [MulAction (MulAut (H F)) A]
    {ell : ℕ} {InBlock : Irr k (H F) → Prop}
    {Series : Irr k (H F) → Dual → Prop}
    {D : Definitions k (H F) A Block} {coherence : InnerCoherence D}
    {C : Block}
    {global : GlobalInputs F algebraicLift ell InBlock Series D C}
    {v : GenericPair D coherence C}
    (geometry : PairGeometrySource F algebraicLift commute global v)
    (sigma : E) :
    (geometry.rational.unified sigma).langData.fieldAut =
      global.fieldAction sigma := by
  ext x
  change algebraicLift sigma (x : Gbar) =
    ((global.fieldAction sigma x : H F) : Gbar)
  exact (global.fieldAction_coe sigma x).symm

/-- Full relative form of manuscript Lemma 3.6.  The proof is kernel checked
after the source structures above have been instantiated.  It combines the
ordinary E1--E3 deduction with the unified E3--E11 generic-orbit deduction
for every element of the typed field group and every valid FMZ
representative. -/
theorem lemma_3_5_relative
    [MulAction (MulAut (H F)) A]
    (ell : ℕ) (InBlock : Irr k (H F) → Prop)
    (Series : Irr k (H F) → Dual → Prop)
    (D : Definitions k (H F) A Block) (coherence : InnerCoherence D)
    (C : Block)
    (global : GlobalInputs F algebraicLift ell InBlock Series D C)
    (geometry : ∀ v : GenericPair D coherence C,
      PairGeometrySource F algebraicLift commute global v)
    (characters : ∀ v : GenericPair D coherence C,
      CharacterSourceFor F algebraicLift commute (geometry v)) :
    FixationConclusion ell InBlock Series D coherence C
      global.fieldAction := by
  constructor
  · exact EvenFieldOrdinaryCharacters.XC_pointwise_fixed
      ell InBlock Series global.fieldAction global.blockSeries
      global.seriesDisjoint global.fieldFixesIdentitySeries
  · intro sigma v
    let geometryV := geometry v
    let characterV := characters v
    letI : Fintype
        (finiteNormalizer (H := H F) (A := A) v.1.1) :=
      characterV.finiteNormalizerFintype
    letI : (D.levi v.1.1).Normal :=
      (geometryV.fmz (1 : E)).fmzLevi_normal
    let characterData := characterV.data
    letI : Group characterData.AmbientGroup := characterData.ambientGroup
    have horbit :=
      genericOrbit_fixed_relative_to_E3_E11
        (k := k) (Dual := Dual) (FieldAutomorphism := E)
        F (algebraicLift sigma) (commute sigma)
        (geometryV.rational.unified sigma) D coherence C v.1
        geometryV.generic (geometryV.fmz sigma)
        global.centralSylow global.centralSylow_natural global.realise
        global.realise_injective
        (by
          change global.realise v.1.1 =
            global.centralSylow
              (conjugateSubgroup geometryV.rational.standardLevi
                geometryV.rational.langElement)
          exact geometryV.realise_selected)
        (geometryV.realise_transport sigma) geometryV.WeylLevi
        (geometryV.weyl sigma) global.blockLabel global.selectedSeries
        geometryV.standardSeries (geometryV.seriesTransport sigma)
        global.blockLabel_eq_one global.labelComparison
        geometryV.standardFieldAction sigma
        (geometryV.standardFieldAction_eq sigma)
        geometryV.fieldFixesStandardSeries characterData.ambient
        (characterData.ambientConjugation sigma) characterData.kappa
        characterData.gallagher characterData.clifford
    have hfield := PairGeometrySource.langFieldAut_eq_global
      (F := F) (algebraicLift := algebraicLift) (commute := commute)
      geometryV sigma
    rw [hfield] at horbit
    rcases horbit with ⟨hvalid, horbit⟩
    refine ⟨hvalid, horbit.trans ?_⟩
    apply congrArg
      (validConjugacyClass (innerStablePredicate D coherence C))
    apply Subtype.ext
    rfl

end ModularRep.PaperProofs.EvenFieldLemma35Relative


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
