import ModularRep.PaperProofs.EvenFieldAlgebraicTorusPairAssembly
import ModularRep.PaperProofs.EvenFieldLocalCharacterFormula

/-!
# The local-character formula on an algebraic-torus pair

This module connects the formula-level Gallagher and Clifford argument to the
actual irreducible character stored in a two-sorted local pair.  The ambient
extension is represented by a genuine representation of an ambient group and
a homomorphism from the inertia group.  A specified ambient element induces
the same automorphism through that homomorphism as the automorphism obtained
by restricting the finite normaliser automorphism.

The base subgroup, inertia subgroup, finite normaliser, and every occurrence
of the automorphism are therefore literal shared terms.  No fixedness of the
pair character is assumed.

`EvenFieldExtensionGallagher` cannot be applied literally at this boundary:
there its intermediate group is a subgroup of the ambient extension group,
whereas here the inertia group is a subgroup of `N_H(T)`.  The homomorphism
into the ambient group and the displayed conjugation-intertwining equation
below are the exact interface needed to derive invariance of the pulled-back
trace character rather than assume it.
-/

namespace ModularRep.PaperProofs.EvenFieldAlgebraicTorusPairCharacterBridge

open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs.CharacterInductionEquivariance
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPair
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPairAssembly
open ModularRep.PaperProofs.EvenFieldGallagherFormula
open ModularRep.PaperProofs.EvenFieldLocalCharacterFormula

universe u

variable {k H A K V : Type u}
    [Field k] [Group H] [MulAction (MulAut H) A]
    [Group K] [AddCommGroup V] [Module k V]

/-- The trace character obtained by restricting an ambient representation is
fixed when an ambient element realises the prescribed automorphism of the
literal inertia subgroup. -/
theorem ambientRestrictionCharacter_fixed
    (tau : MulAut H) (P : LocalPair k H A)
    (label_fixed : tau • P.1 = P.1)
    (I : Subgroup (finiteNormalizer (H := H) (A := A) P.1))
    (stable : ∀ x : finiteNormalizer (H := H) (A := A) P.1,
      x ∈ I ↔ inducedFiniteNormalizerAut tau P.1 label_fixed x ∈ I)
    (rho : Representation k K V)
    (inclusion : I →* K)
    (z : K)
    (intertwines : ∀ x : I,
      inclusion (restrictAut I
        (inducedFiniteNormalizerAut tau P.1 label_fixed) stable x) =
          z * inclusion x * z⁻¹) :
    ∀ x : I,
      (rho.pullback inclusion).character
          (restrictAut I
            (inducedFiniteNormalizerAut tau P.1 label_fixed) stable x) =
        (rho.pullback inclusion).character x := by
  intro x
  change rho.character
      (inclusion (restrictAut I
        (inducedFiniteNormalizerAut tau P.1 label_fixed) stable x)) =
    rho.character (inclusion x)
  rw [intertwines x]
  simpa [mul_assoc] using
    rho.char_mul_comm (z⁻¹) (z * inclusion x)

/-- The extension, Gallagher factorisation, and Clifford induction formulas
fix the actual irreducible finite-normaliser character stored in `P`.

The conclusion is exactly the character hypothesis required by
`rightTransportPair_eq_of_label_character_fixed`. -/
theorem pairCharacter_fixed_of_extension_gallagher_clifford
    (tau : MulAut H) (P : LocalPair k H A)
    (label_fixed : tau • P.1 = P.1)
    [CharZero k]
    [Fintype (finiteNormalizer (H := H) (A := A) P.1)]
    (I : Subgroup (finiteNormalizer (H := H) (A := A) P.1))
    (stable : ∀ x : finiteNormalizer (H := H) (A := A) P.1,
      x ∈ I ↔ inducedFiniteNormalizerAut tau P.1 label_fixed x ∈ I)
    (B : Subgroup I) [B.Normal]
    (difference_mem : ∀ x : I,
      x⁻¹ * restrictAut I
        (inducedFiniteNormalizerAut tau P.1 label_fixed) stable x ∈ B)
    (rho : Representation k K V)
    (inclusion : I →* K)
    (z : K)
    (intertwines : ∀ x : I,
      inclusion (restrictAut I
        (inducedFiniteNormalizerAut tau P.1 label_fixed) stable x) =
          z * inclusion x * z⁻¹)
    (kappa : Irr k I)
    (gallagher : HasGallagherFactorisation B
      (rho.pullback inclusion).character kappa)
    (clifford : HasCliffordInduction I kappa P.2) :
    twist k (finiteNormalizer (H := H) (A := A) P.1) P.2
        (inducedFiniteNormalizerAut tau P.1 label_fixed) = P.2 := by
  exact EvenFieldLocalCharacterFormula.localCharacter_fixed I
    (inducedFiniteNormalizerAut tau P.1 label_fixed) stable B difference_mem
    (rho.pullback inclusion).character
    (ambientRestrictionCharacter_fixed tau P label_fixed I stable rho
      inclusion z intertwines)
    kappa gallagher P.2 clifford

/-- Combining the source-shaped character argument with separate fixation of
the algebraic-torus label fixes the dependent pair in the manuscript's right
action convention. -/
theorem rightTransportPair_eq_of_extension_gallagher_clifford
    (tau : MulAut H) (P : LocalPair k H A)
    (label_fixed : tau • P.1 = P.1)
    [CharZero k]
    [Fintype (finiteNormalizer (H := H) (A := A) P.1)]
    (I : Subgroup (finiteNormalizer (H := H) (A := A) P.1))
    (stable : ∀ x : finiteNormalizer (H := H) (A := A) P.1,
      x ∈ I ↔ inducedFiniteNormalizerAut tau P.1 label_fixed x ∈ I)
    (B : Subgroup I) [B.Normal]
    (difference_mem : ∀ x : I,
      x⁻¹ * restrictAut I
        (inducedFiniteNormalizerAut tau P.1 label_fixed) stable x ∈ B)
    (rho : Representation k K V)
    (inclusion : I →* K)
    (z : K)
    (intertwines : ∀ x : I,
      inclusion (restrictAut I
        (inducedFiniteNormalizerAut tau P.1 label_fixed) stable x) =
          z * inclusion x * z⁻¹)
    (kappa : Irr k I)
    (gallagher : HasGallagherFactorisation B
      (rho.pullback inclusion).character kappa)
    (clifford : HasCliffordInduction I kappa P.2) :
    rightTransportPair P tau = P := by
  apply rightTransportPair_eq_of_label_character_fixed tau P label_fixed
  exact pairCharacter_fixed_of_extension_gallagher_clifford tau P label_fixed
    I stable B difference_mem rho inclusion z
    intertwines kappa gallagher clifford

/-- The complete abstract local-pair endpoint: the exact extension,
Gallagher, Clifford, and induction formulas fix the pair under the inner
twist, and the inner twist then gives equality of the valid `H`-orbit classes
under the field automorphism. -/
theorem validConjugacyClass_fixed_of_extension_gallagher_clifford
    (fieldAut tau : MulAut H) (h : H)
    (htau : tau = MulAut.conj h * fieldAut)
    (P : LocalPair k H A)
    (label_fixed : tau • P.1 = P.1)
    [CharZero k]
    [Fintype (finiteNormalizer (H := H) (A := A) P.1)]
    (W : InnerStablePredicate k H A)
    (hP : W.predicate P)
    (I : Subgroup (finiteNormalizer (H := H) (A := A) P.1))
    (stable : ∀ x : finiteNormalizer (H := H) (A := A) P.1,
      x ∈ I ↔ inducedFiniteNormalizerAut tau P.1 label_fixed x ∈ I)
    (B : Subgroup I) [B.Normal]
    (difference_mem : ∀ x : I,
      x⁻¹ * restrictAut I
        (inducedFiniteNormalizerAut tau P.1 label_fixed) stable x ∈ B)
    (rho : Representation k K V)
    (inclusion : I →* K)
    (z : K)
    (intertwines : ∀ x : I,
      inclusion (restrictAut I
        (inducedFiniteNormalizerAut tau P.1 label_fixed) stable x) =
          z * inclusion x * z⁻¹)
    (kappa : Irr k I)
    (gallagher : HasGallagherFactorisation B
      (rho.pullback inclusion).character kappa)
    (clifford : HasCliffordInduction I kappa P.2) :
    ∃ hField : W.predicate (rightTransportPair P fieldAut),
      validConjugacyClass W ⟨rightTransportPair P fieldAut, hField⟩ =
        validConjugacyClass W ⟨P, hP⟩ := by
  apply validConjugacyClass_fixed_of_innerTwist_right W fieldAut tau h htau
    P hP
  exact rightTransportPair_eq_of_extension_gallagher_clifford tau P
    label_fixed I stable B difference_mem rho inclusion
    z intertwines kappa gallagher clifford

end ModularRep.PaperProofs.EvenFieldAlgebraicTorusPairCharacterBridge


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
