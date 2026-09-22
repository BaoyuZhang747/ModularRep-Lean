import ModularRep.PaperProofs.EvenFieldAlgebraicTorusLabelFixation
import ModularRep.PaperProofs.EvenFieldAlgebraicTorusPairInertiaBridge
import ModularRep.PaperProofs.EvenFieldAmbientExtensionBridge
import ModularRep.PaperProofs.EvenFieldLeviCharacterFixation
import ModularRep.PaperProofs.EvenFieldFMZGenericPair
import ModularRep.PaperProofs.EvenFieldGenericLeviSeries
import ModularRep.PaperProofs.EvenFieldGenericOrbitE8
import ModularRep.PaperProofs.EvenFieldLangInnerTwist
import ModularRep.PaperProofs.EvenFieldRationalLeviProvenance
import ModularRep.PaperProofs.EvenFieldRelativeDifferenceAdapter

/-!
# A theorem-first generic-orbit slice for the even-field lemma

This file composes the checked manuscript-specific deductions for one genuine
generic-pair representative and one field automorphism.  In particular, it
does not assume fixation of the torus label, the Levi character, the inertia
subgroup, the local character, the dependent pair, or its orbit.

The remaining hypotheses have the shapes of the published and structural
inputs used in the manuscript: a rational-Levi realisation, the universal
field invariance of unipotent characters, the universal relative-normaliser
relation, an ambient extension character, Gallagher's multiplication formula,
and Clifford's induction formula.
-/

namespace ModularRep.PaperProofs.EvenFieldGenericOrbitTheoremFirst

open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs.CharacterInductionEquivariance
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusLabelFixation
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPair
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPairAssembly
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPairCharacterBridge
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPairInertiaBridge
open ModularRep.PaperProofs.EvenFieldAmbientExtension
open ModularRep.PaperProofs.EvenFieldAmbientExtensionBridge
open ModularRep.PaperProofs.EvenFieldGallagherFormula
open ModularRep.PaperProofs.EvenFieldFMZGenericPair
open ModularRep.PaperProofs.EvenFieldGenericLeviSeries
open ModularRep.PaperProofs.EvenFieldGenericOrbitE8
open ModularRep.PaperProofs.EvenFieldLeviCharacterFixation
open ModularRep.PaperProofs.EvenFieldLeviTorus
open ModularRep.PaperProofs.EvenFieldLangInnerTwist
open ModularRep.PaperProofs.EvenFieldLocalCharacterFormula
open ModularRep.PaperProofs.EvenFieldRationalLeviProvenance
open ModularRep.PaperProofs.EvenFieldRelativeDifferenceAdapter

universe u

variable {k Gbar H A Block StandardLevi Dual FieldAutomorphism
    WeylNormalizer K : Type u}
    [Field k] [CharZero k]
    [Group Gbar] [Group H] [MulAction (MulAut H) A]
    [Group StandardLevi] [Group Dual] [Group FieldAutomorphism]
    [Group WeylNormalizer] [Group K]

/-- The complete checked generic-orbit deduction for one representative.

The proof first derives the torus-label equality from the characteristic
torus calculation.  It then transports universal unipotent-character
invariance across the rational-Levi equivalence to fix the actual base
character.  The universal relative-normaliser relation supplies stability of
the base and inertia subgroups.  Finally, the exact Gallagher and Clifford
formulas fix the local character and the inner twist gives equality of the
`H`-orbit classes.
-/
private theorem genericOrbit_fixed_from_components
    (fieldAut tauH : MulAut H) (h : H)
    (tau_factorisation : tauH = MulAut.conj h * fieldAut)
    (D : Definitions k H A Block) (coherence : InnerCoherence D)
    (C : Block)
    (P : LocalPair k H A)
    [Fintype (finiteNormalizer (H := H) (A := A) P.1)]
    (generic : GenericWitness D C P)
    [baseNormal : (D.levi P.1).Normal]
    -- The characteristic-torus and label-realisation data.
    (sigmaBar : MulAut Gbar)
    (rationalLevi :
      EvenFieldRationalLeviProvenance.Data
        (StandardLevi := StandardLevi) D P sigmaBar tauH)
    (selected_g : Gbar) (rationalLevi_g : rationalLevi.g = selected_g)
    (centralSylow : Subgroup Gbar → Subgroup Gbar)
    (centralSylow_natural : CharacteristicTorusNatural centralSylow)
    (realise : A → Subgroup Gbar)
    (realise_injective : Function.Injective realise)
    (realise_selected :
      realise P.1 = centralSylow
        (conjugateSubgroup rationalLevi.L rationalLevi.g))
    (realise_transport :
      realise (tauH • P.1) =
        (realise P.1).map
          (innerTwistedAut sigmaBar rationalLevi.g).toMonoidHom)
    -- E8 at representative level and its rational-Levi transport.
    (e8 : EvenFieldGenericOrbitE8.Data sigmaBar.toMonoidHom tauH P.1
      rationalLevi.L (D.levi P.1) WeylNormalizer)
    -- Rational-Levi transport and universal field invariance.
    (BlockLabel : Block → Dual)
    (SelectedSeries : (T : A) → Irr k (D.levi T) → Dual → Prop)
    (StandardSeries : Irr k StandardLevi → Dual → Prop)
    (seriesTransport :
      SeriesTransportInput rationalLevi SelectedSeries StandardSeries)
    (blockLabel_eq_one : BlockLabel C = 1)
    (labelComparison :
      E4GenericLabelComparisonInput D C BlockLabel SelectedSeries)
    (fieldActionLevi : FieldAutomorphism →* MulAut StandardLevi)
    (fieldElement : FieldAutomorphism)
    (sigmaLevi_eq :
      rationalLevi.sigmaLevi = fieldActionLevi fieldElement)
    (fieldFixesIdentitySeries :
      EvenFieldOrdinaryCharacters.E3StandardFieldFixesUnipotentInput
        StandardSeries fieldActionLevi)
    -- Ambient extension, Gallagher, and Clifford inputs.
    (ambient : EvenFieldAmbientExtension.Data
      (D.levi P.1) generic.lambda K)
    (ambientConjugation :
      ∀ (label_fixed : tauH • P.1 = P.1)
        (lambda_fixed :
          twist k (D.levi P.1) generic.lambda
            (restrictAut (D.levi P.1)
              (inducedFiniteNormalizerAut tauH P.1 label_fixed)
              (subgroup_stable_of_difference (D.levi P.1)
                (inducedFiniteNormalizerAut tauH P.1 label_fixed)
                (e8.relativeDifference label_fixed))) = generic.lambda),
        EvenFieldAmbientExtension.ConjugationWitness ambient
          (restrictAut (characterInertia (D.levi P.1) generic.lambda)
            (inducedFiniteNormalizerAut tauH P.1 label_fixed)
            (characterInertia_stable_of_difference
              (D.levi P.1) generic.lambda
              (inducedFiniteNormalizerAut tauH P.1 label_fixed)
              (e8.relativeDifference label_fixed) lambda_fixed)))
    (kappa : Irr k (characterInertia (D.levi P.1) generic.lambda))
    (gallagher : HasGallagherFactorisation
      (baseInInertia (D.levi P.1) generic.lambda)
      ambient.extensionIrr kappa)
    (clifford : HasCliffordInduction
      (characterInertia (D.levi P.1) generic.lambda) kappa P.2) :
    ∃ transformed_valid : IsGenericFor D C (rightTransportPair P fieldAut),
      validConjugacyClass (innerStablePredicate D coherence C)
          ⟨rightTransportPair P fieldAut, transformed_valid⟩ =
      validConjugacyClass (innerStablePredicate D coherence C)
          ⟨P, generic.isGenericFor⟩ := by
  let label_fixed : tauH • P.1 = P.1 :=
    localPair_label_fixed_of_characteristicTorus_stable
      sigmaBar selected_g rationalLevi.L rationalLevi.L_stable
      centralSylow centralSylow_natural tauH P
      realise realise_injective (by simpa [← rationalLevi_g] using realise_selected)
      (by simpa [← rationalLevi_g] using realise_transport)
  let relative_difference :
      ∀ (hlabel : tauH • P.1 = P.1)
        (x : finiteNormalizer (H := H) (A := A) P.1),
        x⁻¹ * inducedFiniteNormalizerAut tauH P.1 hlabel x ∈
          D.levi P.1 :=
    e8.relativeDifference
  let alphaN : MulAut (finiteNormalizer (H := H) (A := A) P.1) :=
    inducedFiniteNormalizerAut tauH P.1 label_fixed
  let difference : ∀ x : finiteNormalizer (H := H) (A := A) P.1,
      x⁻¹ * alphaN x ∈ D.levi P.1 :=
    relative_difference label_fixed
  let baseStable : ∀ x : finiteNormalizer (H := H) (A := A) P.1,
      x ∈ D.levi P.1 ↔ alphaN x ∈ D.levi P.1 :=
    subgroup_stable_of_difference (D.levi P.1) alphaN difference
  let tauB : MulAut (D.levi P.1) :=
    restrictAut (D.levi P.1) alphaN baseStable
  have lambda_fixed :
      twist k (D.levi P.1) generic.lambda tauB = generic.lambda :=
    selectedLambda_fixed_from_E3_E4 generic rationalLevi BlockLabel
      SelectedSeries StandardSeries seriesTransport blockLabel_eq_one
      labelComparison fieldActionLevi fieldElement sigmaLevi_eq
      fieldFixesIdentitySeries tauB
      (rationalLevi.levi_intertwines label_fixed difference)
  exact genericOrbit_fixed_of_ambient_extension fieldAut tauH h
    tau_factorisation D coherence C P generic label_fixed difference
    lambda_fixed ambient (ambientConjugation label_fixed lambda_fixed)
    kappa gallagher clifford

/-- The generic-weight half of manuscript Lemma 3.6 for one representative
and one standard field automorphism, verified relative to the source-shaped
E3--E11 inputs.

Unlike the internal composition lemma, this public endpoint does not assume
an element `h` of the finite group or the inner-twist factorisation.  The
element is constructed as `g * sigmaBar(g)⁻¹` from the Lang witness, Lean
proves that it lies in the finite fixed-point group, and both the field
automorphism and its inner twist are defined from that data. -/
theorem genericOrbit_fixed_relative_to_E3_E11
    (F : Gbar →* Gbar) (sigmaBar : MulAut Gbar)
    (commute : ∀ x : Gbar, F (sigmaBar x) = sigmaBar (F x))
    (g : Gbar) (lang : EvenFieldLangInnerTwist.Data F sigmaBar commute g)
    [MulAction
      (MulAut (EvenFieldSourceShaped.frobeniusFixedSubgroup F)) A]
    (D : Definitions k
      (EvenFieldSourceShaped.frobeniusFixedSubgroup F) A Block)
    (coherence : InnerCoherence D) (C : Block)
    (P : LocalPair k
      (EvenFieldSourceShaped.frobeniusFixedSubgroup F) A)
    [Fintype (finiteNormalizer
      (H := EvenFieldSourceShaped.frobeniusFixedSubgroup F)
      (A := A) P.1)]
    (generic : GenericWitness D C P)
    [baseNormal : (D.levi P.1).Normal]
    (rationalLevi : EvenFieldRationalLeviProvenance.Data
      (StandardLevi := StandardLevi) D P sigmaBar lang.tau)
    (rationalLevi_g : rationalLevi.g = g)
    (centralSylow : Subgroup Gbar → Subgroup Gbar)
    (centralSylow_natural : CharacteristicTorusNatural centralSylow)
    (realise : A → Subgroup Gbar)
    (realise_injective : Function.Injective realise)
    (realise_selected :
      realise P.1 = centralSylow
        (conjugateSubgroup rationalLevi.L rationalLevi.g))
    (realise_transport :
      realise (lang.tau • P.1) =
        (realise P.1).map
          (innerTwistedAut sigmaBar rationalLevi.g).toMonoidHom)
    (e8 : EvenFieldGenericOrbitE8.Data sigmaBar.toMonoidHom lang.tau P.1
      rationalLevi.L (D.levi P.1) WeylNormalizer)
    (BlockLabel : Block → Dual)
    (SelectedSeries : (T : A) → Irr k (D.levi T) → Dual → Prop)
    (StandardSeries : Irr k StandardLevi → Dual → Prop)
    (seriesTransport :
      SeriesTransportInput rationalLevi SelectedSeries StandardSeries)
    (blockLabel_eq_one : BlockLabel C = 1)
    (labelComparison :
      E4GenericLabelComparisonInput D C BlockLabel SelectedSeries)
    (fieldActionLevi : FieldAutomorphism →* MulAut StandardLevi)
    (fieldElement : FieldAutomorphism)
    (sigmaLevi_eq :
      rationalLevi.sigmaLevi = fieldActionLevi fieldElement)
    (fieldFixesIdentitySeries :
      EvenFieldOrdinaryCharacters.E3StandardFieldFixesUnipotentInput
        StandardSeries fieldActionLevi)
    (ambient : EvenFieldAmbientExtension.Data
      (D.levi P.1) generic.lambda K)
    (ambientConjugation :
      ∀ (label_fixed : lang.tau • P.1 = P.1)
        (lambda_fixed :
          twist k (D.levi P.1) generic.lambda
            (restrictAut (D.levi P.1)
              (inducedFiniteNormalizerAut lang.tau P.1 label_fixed)
              (subgroup_stable_of_difference (D.levi P.1)
                (inducedFiniteNormalizerAut lang.tau P.1 label_fixed)
                (e8.relativeDifference label_fixed))) = generic.lambda),
        EvenFieldAmbientExtension.ConjugationWitness ambient
          (restrictAut (characterInertia (D.levi P.1) generic.lambda)
            (inducedFiniteNormalizerAut lang.tau P.1 label_fixed)
            (characterInertia_stable_of_difference
              (D.levi P.1) generic.lambda
              (inducedFiniteNormalizerAut lang.tau P.1 label_fixed)
              (e8.relativeDifference label_fixed) lambda_fixed)))
    (kappa : Irr k (characterInertia (D.levi P.1) generic.lambda))
    (gallagher : HasGallagherFactorisation
      (baseInInertia (D.levi P.1) generic.lambda)
      ambient.extensionIrr kappa)
    (clifford : HasCliffordInduction
      (characterInertia (D.levi P.1) generic.lambda) kappa P.2) :
    ∃ transformed_valid : IsGenericFor D C
        (rightTransportPair P lang.fieldAut),
      validConjugacyClass (innerStablePredicate D coherence C)
          ⟨rightTransportPair P lang.fieldAut, transformed_valid⟩ =
        validConjugacyClass (innerStablePredicate D coherence C)
          ⟨P, generic.isGenericFor⟩ := by
  exact genericOrbit_fixed_from_components lang.fieldAut lang.tau
    lang.innerElement lang.tau_factorisation D coherence C P generic
    sigmaBar rationalLevi g rationalLevi_g centralSylow centralSylow_natural realise
    realise_injective realise_selected realise_transport e8 BlockLabel
    SelectedSeries StandardSeries seriesTransport blockLabel_eq_one
    labelComparison fieldActionLevi fieldElement sigmaLevi_eq
    fieldFixesIdentitySeries ambient ambientConjugation kappa gallagher
    clifford

end ModularRep.PaperProofs.EvenFieldGenericOrbitTheoremFirst


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
