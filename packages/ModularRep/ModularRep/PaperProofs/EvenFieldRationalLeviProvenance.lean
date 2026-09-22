import ModularRep.PaperProofs.EvenFieldAlgebraicTorusLabelFixation
import ModularRep.PaperProofs.EvenFieldAlgebraicTorusPairInertiaBridge
import ModularRep.PaperProofs.EvenFieldFMZGenericPair

/-!
# Shared rational-Levi provenance in the even-field argument

The algebraic Levi used to fix the characteristic torus and the finite Levi
used for the selected FMZ character must come from the same rational-Levi
construction.  This module packages that group-level provenance and derives
the elementwise intertwining equation used to transport unipotent-character
fixation.  It contains no character, pair, or orbit fixedness assertion.

The embeddings are explicit because the algebraic ambient group, its finite
fixed-point group, and the standard finite Levi are different Lean types.
The two displayed provenance equations say exactly that the finite-Levi
equivalence is conjugation by the chosen Lang witness and that the two field
actions are restrictions of the corresponding algebraic automorphisms.
-/

namespace ModularRep.PaperProofs.EvenFieldRationalLeviProvenance

open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs.CharacterInductionEquivariance
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPair
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPairAssembly
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPairInertiaBridge
open ModularRep.PaperProofs.EvenFieldFMZGenericPair
open ModularRep.PaperProofs.EvenFieldLeviTorus

universe u

variable {k Gbar H A Block StandardLevi : Type u}
    [Field k] [CharZero k] [Group Gbar] [Group H]
    [MulAction (MulAut H) A] [Group StandardLevi]

/-- The group-level data identifying one rational Levi simultaneously in
the algebraic group, the standard finite model, and the literal FMZ finite
Levi inside `N_H(T)`. -/
structure Data (D : Definitions k H A Block) (P : LocalPair k H A)
    (sigmaBar : MulAut Gbar) (tauH : MulAut H) where
  g : Gbar
  L : Subgroup Gbar
  L_stable : L.map sigmaBar.toMonoidHom = L
  hEmbed : H →* Gbar
  hEmbed_injective : Function.Injective hEmbed
  standardEmbed : StandardLevi →* Gbar
  standardEmbed_injective : Function.Injective standardEmbed
  standardEmbed_range_le_L : standardEmbed.range ≤ L
  leviEquiv : StandardLevi ≃* D.levi P.1
  leviEquiv_is_conjugation : ∀ x : StandardLevi,
    hEmbed (((leviEquiv x : D.levi P.1) :
      finiteNormalizer (H := H) (A := A) P.1) : H) =
      g * standardEmbed x * g⁻¹
  sigmaLevi : MulAut StandardLevi
  sigmaLevi_is_restriction : ∀ x : StandardLevi,
    standardEmbed (sigmaLevi x) = sigmaBar (standardEmbed x)
  tauH_is_restriction : ∀ y : H,
    hEmbed (tauH y) = innerTwistedAut sigmaBar g (hEmbed y)

/-- The shared rational-Levi provenance derives the precise finite group
intertwining equation required by the character-transport lemma. -/
theorem Data.levi_intertwines
    {D : Definitions k H A Block} {P : LocalPair k H A}
    {sigmaBar : MulAut Gbar} {tauH : MulAut H}
    (R : Data (StandardLevi := StandardLevi) D P sigmaBar tauH)
    (label_fixed : tauH • P.1 = P.1)
    (difference :
      ∀ x : finiteNormalizer (H := H) (A := A) P.1,
        x⁻¹ * inducedFiniteNormalizerAut tauH P.1 label_fixed x ∈
          D.levi P.1)
    (x : StandardLevi) :
    R.leviEquiv (R.sigmaLevi x) =
      restrictAut (D.levi P.1)
        (inducedFiniteNormalizerAut tauH P.1 label_fixed)
        (subgroup_stable_of_difference (D.levi P.1)
          (inducedFiniteNormalizerAut tauH P.1 label_fixed) difference)
        (R.leviEquiv x) := by
  apply Subtype.ext
  apply Subtype.ext
  apply R.hEmbed_injective
  calc
    R.hEmbed (((R.leviEquiv (R.sigmaLevi x) : D.levi P.1) :
        finiteNormalizer (H := H) (A := A) P.1) : H) =
        R.g * R.standardEmbed (R.sigmaLevi x) * R.g⁻¹ :=
      R.leviEquiv_is_conjugation (R.sigmaLevi x)
    _ = R.g * sigmaBar (R.standardEmbed x) * R.g⁻¹ := by
      rw [R.sigmaLevi_is_restriction]
    _ = innerTwistedAut sigmaBar R.g
        (R.g * R.standardEmbed x * R.g⁻¹) := by
      rw [innerTwistedAut_conjugate]
    _ = innerTwistedAut sigmaBar R.g
        (R.hEmbed (((R.leviEquiv x : D.levi P.1) :
          finiteNormalizer (H := H) (A := A) P.1) : H)) := by
      rw [R.leviEquiv_is_conjugation]
    _ = R.hEmbed (tauH
        (((R.leviEquiv x : D.levi P.1) :
          finiteNormalizer (H := H) (A := A) P.1) : H)) := by
      rw [R.tauH_is_restriction]
    _ = R.hEmbed
        (((restrictAut (D.levi P.1)
          (inducedFiniteNormalizerAut tauH P.1 label_fixed)
          (subgroup_stable_of_difference (D.levi P.1)
            (inducedFiniteNormalizerAut tauH P.1 label_fixed) difference)
          (R.leviEquiv x) : D.levi P.1) :
            finiteNormalizer (H := H) (A := A) P.1) : H) := by
      congr 1

end ModularRep.PaperProofs.EvenFieldRationalLeviProvenance


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
