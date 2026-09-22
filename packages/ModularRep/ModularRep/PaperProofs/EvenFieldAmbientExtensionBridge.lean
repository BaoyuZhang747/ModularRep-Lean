import ModularRep.PaperProofs.EvenFieldAmbientExtension
import ModularRep.PaperProofs.EvenFieldFMZGenericPair

/-!
# Feeding the ambient extension into the generic-pair argument

This module connects the certified ambient extension supplied by Späth's
theorem to the existing inertia, Gallagher, Clifford, and orbit bridge.  The
base subgroup is the finite Levi attached to the selected generic pair, and
the character being extended is literally the `lambda` stored in that
generic-pair witness.

The remaining formula inputs are Gallagher's factorisation for the
constructed extension character and Clifford induction from its actual
character inertia group.  No extension character independent of the selected
Levi character can be substituted in this interface.
-/

namespace ModularRep.PaperProofs.EvenFieldAmbientExtensionBridge

open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs.CharacterInductionEquivariance
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPair
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPairAssembly
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPairInertiaBridge
open ModularRep.PaperProofs.EvenFieldAmbientExtension
open ModularRep.PaperProofs.EvenFieldFMZGenericPair
open ModularRep.PaperProofs.EvenFieldGallagherFormula
open ModularRep.PaperProofs.EvenFieldLocalCharacterFormula

universe u

variable {k H A Block K : Type u}
    [Field k] [CharZero k]
    [Group H] [MulAction (MulAut H) A] [Group K]

/-- Späth's ambient extension certificate, Gallagher's formula, and
Clifford induction fix the orbit of the selected generic pair.

The label and base-character equalities are the preceding outputs in the
manuscript proof.  The ambient certificate extends `generic.lambda` from the
literal finite Levi `defs.levi P.1`, and its conjugation witness realises the
automorphism induced on the corresponding character inertia group. -/
theorem genericOrbit_fixed_of_ambient_extension
    (fieldAut tau : MulAut H) (h : H)
    (tau_factorisation : tau = MulAut.conj h * fieldAut)
    (defs : Definitions k H A Block) (coherence : InnerCoherence defs)
    (C : Block) (P : LocalPair k H A)
    [Fintype (finiteNormalizer (H := H) (A := A) P.1)]
    (generic : GenericWitness defs C P)
    [baseNormal : (defs.levi P.1).Normal]
    (label_fixed : tau • P.1 = P.1)
    (relative_difference :
      ∀ x : finiteNormalizer (H := H) (A := A) P.1,
        x⁻¹ * inducedFiniteNormalizerAut tau P.1 label_fixed x ∈
          defs.levi P.1)
    (lambda_fixed :
      twist k (defs.levi P.1) generic.lambda
        (restrictAut (defs.levi P.1)
          (inducedFiniteNormalizerAut tau P.1 label_fixed)
          (subgroup_stable_of_difference (defs.levi P.1)
            (inducedFiniteNormalizerAut tau P.1 label_fixed)
            relative_difference)) = generic.lambda)
    (ambient : Data (defs.levi P.1) generic.lambda K)
    (ambientConjugation : ConjugationWitness ambient
      (restrictAut
        (characterInertia (defs.levi P.1) generic.lambda)
        (inducedFiniteNormalizerAut tau P.1 label_fixed)
        (characterInertia_stable_of_difference
          (defs.levi P.1) generic.lambda
          (inducedFiniteNormalizerAut tau P.1 label_fixed)
          relative_difference lambda_fixed)))
    (kappa : Irr k (characterInertia (defs.levi P.1) generic.lambda))
    (gallagher : HasGallagherFactorisation
      (baseInInertia (defs.levi P.1) generic.lambda)
      ambient.extensionIrr kappa)
    (clifford : HasCliffordInduction
      (characterInertia (defs.levi P.1) generic.lambda) kappa P.2) :
    ∃ transformed_valid : IsGenericFor defs C
        (rightTransportPair P fieldAut),
      validConjugacyClass (innerStablePredicate defs coherence C)
          ⟨rightTransportPair P fieldAut, transformed_valid⟩ =
        validConjugacyClass (innerStablePredicate defs coherence C)
          ⟨P, generic.isGenericFor⟩ := by
  change HasGallagherFactorisation
    (baseInInertia (defs.levi P.1) generic.lambda)
    (ambient.rho.pullback ambient.inclusion).character kappa at gallagher
  exact
    validConjugacyClass_fixed_of_inertia_extension_gallagher_clifford
      fieldAut tau h tau_factorisation P label_fixed
      (innerStablePredicate defs coherence C) generic.isGenericFor
      (defs.levi P.1) generic.lambda relative_difference lambda_fixed
      ambient.rho ambient.inclusion ambientConjugation.element
      ambientConjugation.intertwines kappa gallagher clifford

end ModularRep.PaperProofs.EvenFieldAmbientExtensionBridge


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
