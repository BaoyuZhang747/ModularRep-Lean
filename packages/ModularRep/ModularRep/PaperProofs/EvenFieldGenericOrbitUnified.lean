import ModularRep.PaperProofs.EvenFieldAlgebraicTorusLabelFixation
import ModularRep.PaperProofs.EvenFieldAmbientExtensionBridge
import ModularRep.PaperProofs.EvenFieldGenericLeviSeries
import ModularRep.PaperProofs.EvenFieldUnifiedRationalLeviFMZ

/-!
# The generic-orbit argument from one unified rational-Levi witness

This module is the manuscript-facing E3--E11 composition for one valid
generic-pair representative and one field automorphism.  The standard Levi,
Weyl representative, Lang element, selected finite Levi, and both normaliser
transports all come from one `EvenFieldUnifiedRationalLevi.Data` value.

The only remaining E5 input consists of the two literal FMZ subgroup
identifications.  E8 is supplied at representative level and Lean derives
the relative-difference relation.  In particular, this endpoint does not
assume normality of the FMZ Levi, an independently chosen Levi or normaliser
equivalence, a Levi intertwining equation, fixation of either character in
the pair, fixation of the pair, or equality of its orbit.
-/

namespace ModularRep.PaperProofs.EvenFieldGenericOrbitUnified

open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs.CharacterInductionEquivariance
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusLabelFixation
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPair
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPairAssembly
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPairInertiaBridge
open ModularRep.PaperProofs.EvenFieldAmbientExtension
open ModularRep.PaperProofs.EvenFieldAmbientExtensionBridge
open ModularRep.PaperProofs.EvenFieldFMZGenericPair
open ModularRep.PaperProofs.EvenFieldFixedQuotient
open ModularRep.PaperProofs.EvenFieldGallagherFormula
open ModularRep.PaperProofs.EvenFieldGenericLeviSeries
open ModularRep.PaperProofs.EvenFieldLeviTorus
open ModularRep.PaperProofs.EvenFieldLocalCharacterFormula
open ModularRep.PaperProofs.EvenFieldRelativeDifferenceAdapter
open ModularRep.PaperProofs.EvenFieldSourceShaped
open ModularRep.PaperProofs.EvenFieldUnifiedRationalLevi

universe u

variable {k Gbar A Block Dual FieldAutomorphism WeylNormalizer K : Type u}
    [Field k] [CharZero k] [Group Gbar] [Group Dual]
    [Group FieldAutomorphism] [Group WeylNormalizer] [Group K]

/-- The generic-weight half of manuscript Lemma 3.6 for one representative
and one standard field automorphism, relative to the explicitly separated
E3--E11 literature inputs.

The rational-Levi and E8 deductions are not hypotheses of this theorem.  They
are built from `U`, `identification`, and the representative-level `weyl`
input.  The final ambient-extension, Gallagher, and Clifford data remain the
published E9--E11 inputs and occur after the locally derived normality
instance in the conclusion.
-/
theorem genericOrbit_fixed_relative_to_E3_E11
    (F : Gbar →* Gbar) (sigmaBar : MulAut Gbar)
    (commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x))
    (U : EvenFieldUnifiedRationalLevi.Data F sigmaBar commute)
    [MulAction (MulAut (frobeniusFixedSubgroup F)) A]
    (D : Definitions k (frobeniusFixedSubgroup F) A Block)
    (coherence : InnerCoherence D) (C : Block)
    (P : LocalPair k (frobeniusFixedSubgroup F) A)
    [Fintype (finiteNormalizer
      (H := frobeniusFixedSubgroup F) (A := A) P.1)]
    (generic : GenericWitness D C P)
    (identification : FMZIdentification U D P)
    (centralSylow : Subgroup Gbar → Subgroup Gbar)
    (centralSylow_natural : CharacteristicTorusNatural centralSylow)
    (realise : A → Subgroup Gbar)
    (realise_injective : Function.Injective realise)
    (realise_selected :
      realise P.1 = centralSylow
        (conjugateSubgroup U.standardLevi U.langElement))
    (realise_transport :
      realise (U.langData.tau • P.1) =
        (realise P.1).map
          (innerTwistedAut sigmaBar U.langElement).toMonoidHom)
    (WeylLevi : Subgroup WeylNormalizer)
    (weyl : WeylRepresentativeData U.twistedFrobenius
      sigmaBar.toMonoidHom U.commute_twistedFrobenius
      U.standardFixedNormalizer U.standardFixedNormalizer_stable
      U.standardLevi WeylNormalizer WeylLevi)
    (BlockLabel : Block → Dual)
    (SelectedSeries :
      (T : A) → Irr k (D.levi T) → Dual → Prop)
    (StandardSeries : Irr k U.standardFiniteLevi → Dual → Prop)
    (seriesTransport : SeriesTransportAlongInput
      identification.standardFiniteLeviEquivFMZ SelectedSeries
        StandardSeries)
    (blockLabel_eq_one : BlockLabel C = 1)
    (labelComparison :
      E4GenericLabelComparisonInput D C BlockLabel SelectedSeries)
    (fieldActionLevi : FieldAutomorphism →* MulAut U.standardFiniteLevi)
    (fieldElement : FieldAutomorphism)
    (sigmaLevi_eq : U.standardFieldAut = fieldActionLevi fieldElement)
    (fieldFixesIdentitySeries :
      EvenFieldOrdinaryCharacters.E3StandardFieldFixesUnipotentInput
        StandardSeries fieldActionLevi) :
    letI : (D.levi P.1).Normal := identification.fmzLevi_normal
    ∀ (ambient : EvenFieldAmbientExtension.Data
        (D.levi P.1) generic.lambda K)
      (_ambientConjugation :
        ∀ (label_fixed : U.langData.tau • P.1 = P.1)
          (lambda_fixed :
            twist k (D.levi P.1) generic.lambda
              (restrictAut (D.levi P.1)
                (inducedFiniteNormalizerAut U.langData.tau P.1 label_fixed)
                (subgroup_stable_of_difference (D.levi P.1)
                  (inducedFiniteNormalizerAut U.langData.tau P.1 label_fixed)
                  (identification.relativeDifference_of_weylData
                    WeylNormalizer WeylLevi weyl label_fixed))) =
              generic.lambda),
          EvenFieldAmbientExtension.ConjugationWitness ambient
            (restrictAut
              (characterInertia (D.levi P.1) generic.lambda)
              (inducedFiniteNormalizerAut U.langData.tau P.1 label_fixed)
              (characterInertia_stable_of_difference
                (D.levi P.1) generic.lambda
                (inducedFiniteNormalizerAut U.langData.tau P.1 label_fixed)
                (identification.relativeDifference_of_weylData
                  WeylNormalizer WeylLevi weyl label_fixed)
                lambda_fixed)))
      (kappa : Irr k (characterInertia (D.levi P.1) generic.lambda))
      (_gallagher : HasGallagherFactorisation
        (baseInInertia (D.levi P.1) generic.lambda)
        ambient.extensionIrr kappa)
      (_clifford : HasCliffordInduction
        (characterInertia (D.levi P.1) generic.lambda) kappa P.2),
      ∃ transformed_valid : IsGenericFor D C
          (rightTransportPair P U.langData.fieldAut),
        validConjugacyClass (innerStablePredicate D coherence C)
            ⟨rightTransportPair P U.langData.fieldAut,
              transformed_valid⟩ =
          validConjugacyClass (innerStablePredicate D coherence C)
            ⟨P, generic.isGenericFor⟩ := by
  letI : (D.levi P.1).Normal := identification.fmzLevi_normal
  intro ambient ambientConjugation kappa gallagher clifford
  let label_fixed : U.langData.tau • P.1 = P.1 :=
    localPair_label_fixed_of_characteristicTorus_stable
      sigmaBar U.langElement U.standardLevi U.standardLevi_sigma_stable
      centralSylow centralSylow_natural U.langData.tau P realise
      realise_injective realise_selected realise_transport
  let relative_difference :
      ∀ x : finiteNormalizer
          (H := frobeniusFixedSubgroup F) (A := A) P.1,
        x⁻¹ * inducedFiniteNormalizerAut U.langData.tau P.1
          label_fixed x ∈ D.levi P.1 :=
    identification.relativeDifference_of_weylData
      WeylNormalizer WeylLevi weyl label_fixed
  let tauBase : MulAut (D.levi P.1) :=
    identification.fmzBaseAut WeylNormalizer WeylLevi weyl label_fixed
  have lambda_fixed :
      twist k (D.levi P.1) generic.lambda tauBase = generic.lambda :=
    selectedLambda_fixed_from_E3_E4_along generic
      identification.standardFiniteLeviEquivFMZ BlockLabel SelectedSeries
      StandardSeries seriesTransport blockLabel_eq_one labelComparison
      U.standardFieldAut fieldActionLevi fieldElement sigmaLevi_eq
      fieldFixesIdentitySeries tauBase
      (identification.standardFiniteLeviEquivFMZ_intertwines
        WeylNormalizer WeylLevi weyl label_fixed)
  have tauBase_eq :
      tauBase =
        restrictAut (D.levi P.1)
          (inducedFiniteNormalizerAut U.langData.tau P.1 label_fixed)
          (subgroup_stable_of_difference (D.levi P.1)
            (inducedFiniteNormalizerAut U.langData.tau P.1 label_fixed)
            relative_difference) := by
    rfl
  rw [tauBase_eq] at lambda_fixed
  exact genericOrbit_fixed_of_ambient_extension
    U.langData.fieldAut U.langData.tau U.langData.innerElement
    U.langData.tau_factorisation D coherence C P generic label_fixed
    relative_difference lambda_fixed ambient
    (ambientConjugation label_fixed lambda_fixed) kappa gallagher clifford

end ModularRep.PaperProofs.EvenFieldGenericOrbitUnified


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
