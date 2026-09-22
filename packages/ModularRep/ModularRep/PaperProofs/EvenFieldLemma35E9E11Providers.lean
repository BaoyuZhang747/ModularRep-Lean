import ModularRep.PaperProofs.EvenFieldLemma35Relative

/-!
# Exact E9--E11 providers for the relative form of Lemma 3.6

This module separates the three character-theoretic source inputs in the
even-field proof from the structural ambient-group calculation.

The coefficient field is `ℂ`.  This is the source-faithful choice for the
ordinary-character theorems of Späth, Clifford, and Gallagher.  Obtaining the
same providers over an arbitrary characteristic-zero field would require a
separate scalar-extension or descent argument.

`AmbientStabiliserGeometry` contains only group-theoretic data: the literal
inclusion of the character inertia group in an ambient character stabiliser,
an ambient element for each relevant automorphism, and the equality saying
that this element acts on the inertia group by conjugation.  The
`ConjugationWitness` used downstream is derived from these data.

In the manuscript instance the ambient group is intended to be

`((PGL_(2r+1))^F' ⋊ E((PGL_(2r+1))^F'))_(M, lambda)`.

The present algebraic-group interfaces do not yet construct that literal
simultaneous stabiliser.  Consequently the concrete identification of the
general ambient group below with this PGL stabiliser remains a source-side
structural task.  No field in this module states character fixation, pair
fixation, validity after transport, or equality of orbits.
-/

namespace ModularRep.PaperProofs.EvenFieldLemma35E9E11Providers

open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs.CharacterInductionEquivariance
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPair
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPairAssembly
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPairInertiaBridge
open ModularRep.PaperProofs.EvenFieldAmbientExtension
open ModularRep.PaperProofs.EvenFieldFMZGenericPair
open ModularRep.PaperProofs.EvenFieldGallagherFormula
open ModularRep.PaperProofs.EvenFieldLemma35Relative
open ModularRep.PaperProofs.EvenFieldLangInnerTwist
open ModularRep.PaperProofs.EvenFieldLocalCharacterFormula
open ModularRep.PaperProofs.EvenFieldSourceShaped
open ModularRep.PaperProofs.EvenFieldUnifiedRationalLevi

variable {N Khat Index : Type} [Group N] [Group Khat]

/-- Structural ambient-stabiliser data.

The map `inertiaInclusion` is intended to be the literal inclusion of
`N_H(M, lambda)` in the simultaneous ambient stabiliser of `(M, lambda)`.
The full normaliser `N_H(M)` need not be contained in that character
stabiliser.  The equality `conjugates_inertia` is a structural compatibility
of two concrete group actions, not a character-fixation input. -/
structure AmbientStabiliserGeometry
    (B : Subgroup N) [B.Normal] (lambda : Irr ℂ B)
    (alpha : Index → MulAut (characterInertia B lambda)) where
  inertiaInclusion : characterInertia B lambda →* Khat
  inertiaInclusion_injective : Function.Injective inertiaInclusion
  tauElement : Index → Khat
  conjugates_inertia : ∀ (i : Index) (x : characterInertia B lambda),
    inertiaInclusion (alpha i x) =
      tauElement i * inertiaInclusion x * (tauElement i)⁻¹

/-- E9 in its exact representation-level form.

The inclusion is not chosen by this provider.  It is the inertia inclusion
already fixed by `AmbientStabiliserGeometry`.  Thus the only mathematical
content here is a representation of the exact ambient group whose
restriction is the selected irreducible character `lambda`. -/
structure SpathE9Provider
    {B : Subgroup N} [B.Normal] {lambda : Irr ℂ B}
    {alpha : Index → MulAut (characterInertia B lambda)}
    (G : AmbientStabiliserGeometry (Khat := Khat) B lambda alpha) where
  dimension : ℕ
  rho : Representation ℂ Khat (Fin dimension → ℂ)
  baseRestriction_irreducible : Representation.IsIrreducible
    (rho.pullback
      (G.inertiaInclusion.comp (baseInInertia B lambda).subtype))
  baseRestriction_character :
    (rho.pullback
      (G.inertiaInclusion.comp (baseInInertia B lambda).subtype)).character =
      fun x : baseInInertia B lambda ↦
        lambda (baseInInertiaEquiv B lambda x)

/-- Convert the source-faithful E9 provider to the ambient-extension
interface used by the checked proof. -/
def SpathE9Provider.toData
    {B : Subgroup N} [B.Normal] {lambda : Irr ℂ B}
    {alpha : Index → MulAut (characterInertia B lambda)}
    {G : AmbientStabiliserGeometry (Khat := Khat) B lambda alpha}
    (S : SpathE9Provider (Khat := Khat) G) :
    EvenFieldAmbientExtension.Data B lambda Khat where
  dimension := S.dimension
  rho := S.rho
  inclusion := G.inertiaInclusion
  inclusion_injective := G.inertiaInclusion_injective
  baseRestriction_irreducible := S.baseRestriction_irreducible
  baseRestriction_character := S.baseRestriction_character

/-- Ambient conjugation on the character inertia group yields the exact
`ConjugationWitness` required by the checked proof.

In particular, no conjugation witness is stored in either E9 or E10--E11. -/
def AmbientStabiliserGeometry.conjugationWitness
    {B : Subgroup N} [B.Normal] {lambda : Irr ℂ B}
    {alpha : Index → MulAut (characterInertia B lambda)}
    (G : AmbientStabiliserGeometry (Khat := Khat) B lambda alpha)
    (S : SpathE9Provider (Khat := Khat) G) (i : Index) :
    EvenFieldAmbientExtension.ConjugationWitness S.toData
      (alpha i) where
  element := G.tauElement i
  intertwines := by
    intro x
    exact G.conjugates_inertia i x

/-- The smallest selected E10--E11 provider.

`clifford` is the exact induction formula supplied by Clifford
correspondence for the selected local character.  `gallagher` is the exact
multiplication-and-inflation formula after restricting the E9 extension to
the inertia group. -/
structure CliffordGallagherProvider
    {B : Subgroup N} [B.Normal] {lambda : Irr ℂ B}
    {alpha : Index → MulAut (characterInertia B lambda)}
    (G : AmbientStabiliserGeometry (Khat := Khat) B lambda alpha)
    (S : SpathE9Provider (Khat := Khat) G)
    [Fintype N] (eta : Irr ℂ N) where
  kappa : Irr ℂ (characterInertia B lambda)
  clifford : HasCliffordInduction
    (characterInertia B lambda) kappa eta
  gallagher : HasGallagherFactorisation
    (baseInInertia B lambda) S.toData.extensionIrr kappa

variable {Gbar A Block E Dual : Type}
    [Group Gbar] [Group E] [Group Dual]

variable (F : Gbar →* Gbar) (algebraicLift : E → MulAut Gbar)
  (commute : ∀ (sigma : E) (x : Gbar),
    F (algebraicLift sigma x) = algebraicLift sigma (F x))

abbrev H := frobeniusFixedSubgroup F

/-- A certificate packages one field-group element together with the two
equalities already derived before E9 is used.  It is only an index for the
structural ambient action; neither equality is supplied by the provider
structures in this module. -/
structure PairAutomorphismCertificate
    [MulAction (MulAut (H F)) A]
    {ell : ℕ} {InBlock : Irr ℂ (H F) → Prop}
    {Series : Irr ℂ (H F) → Dual → Prop}
    {D : Definitions ℂ (H F) A Block} {coherence : InnerCoherence D}
    {C : Block}
    {global : GlobalInputs F algebraicLift ell InBlock Series D C}
    {v : GenericPair D coherence C}
    (geometry : PairGeometrySource F algebraicLift commute global v) where
  sigma : E
  label_fixed :
    (geometry.rational.unified sigma).langData.tau • v.1.1 = v.1.1
  lambda_fixed :
    twist ℂ (D.levi v.1.1) geometry.generic.lambda
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
      geometry.generic.lambda

/-- The normaliser automorphism indexed by a field-automorphism certificate. -/
def certificateNormalizerAut
    [MulAction (MulAut (H F)) A]
    {ell : ℕ} {InBlock : Irr ℂ (H F) → Prop}
    {Series : Irr ℂ (H F) → Dual → Prop}
    {D : Definitions ℂ (H F) A Block} {coherence : InnerCoherence D}
    {C : Block}
    {global : GlobalInputs F algebraicLift ell InBlock Series D C}
    {v : GenericPair D coherence C}
    (geometry : PairGeometrySource F algebraicLift commute global v)
    (c : PairAutomorphismCertificate F algebraicLift commute geometry) :
    MulAut (finiteNormalizer (H := H F) (A := A) v.1.1) :=
  inducedFiniteNormalizerAut
    (geometry.rational.unified c.sigma).langData.tau v.1.1 c.label_fixed

/-- The automorphism of the character inertia group obtained from a
certificate.  Stability is derived from the relative-difference relation
and the supplied equality fixing `lambda`; it is not part of the ambient
geometry. -/
noncomputable def certificateInertiaAut
    [MulAction (MulAut (H F)) A]
    {ell : ℕ} {InBlock : Irr ℂ (H F) → Prop}
    {Series : Irr ℂ (H F) → Dual → Prop}
    {D : Definitions ℂ (H F) A Block} {coherence : InnerCoherence D}
    {C : Block}
    {global : GlobalInputs F algebraicLift ell InBlock Series D C}
    {v : GenericPair D coherence C}
    (geometry : PairGeometrySource F algebraicLift commute global v)
    [baseNormal : (D.levi v.1.1).Normal]
    (c : PairAutomorphismCertificate F algebraicLift commute geometry) :
    MulAut (characterInertia (D.levi v.1.1) geometry.generic.lambda) :=
  restrictAut
    (characterInertia (D.levi v.1.1) geometry.generic.lambda)
    (certificateNormalizerAut F algebraicLift commute geometry c)
    (characterInertia_stable_of_difference
      (D.levi v.1.1) geometry.generic.lambda
      (certificateNormalizerAut F algebraicLift commute geometry c)
      ((geometry.fmz c.sigma).relativeDifference_of_weylData
        geometry.WeylNormalizer geometry.WeylLevi
        (geometry.weyl c.sigma) c.label_fixed)
      c.lambda_fixed)

/-- Source-faithful E9--E11 data for one generic representative.

The abstract ambient carrier is retained only because the current project
does not yet contain the literal PGL semidirect product and simultaneous
stabiliser.  To receive concrete manuscript credit, `Khat` and
`ambientGeometry` must be instantiated by that exact group and its evident
character-inertia inclusion. -/
structure ExactPairCharacterSource
    [MulAction (MulAut (H F)) A]
    {ell : ℕ} {InBlock : Irr ℂ (H F) → Prop}
    {Series : Irr ℂ (H F) → Dual → Prop}
    {D : Definitions ℂ (H F) A Block} {coherence : InnerCoherence D}
    {C : Block}
    {global : GlobalInputs F algebraicLift ell InBlock Series D C}
    {v : GenericPair D coherence C}
    (geometry : PairGeometrySource F algebraicLift commute global v)
    [baseNormal : (D.levi v.1.1).Normal]
    [finiteNormalizerFintype : Fintype
      (finiteNormalizer (H := H F) (A := A) v.1.1)] where
  Khat : Type
  [khatGroup : Group Khat]
  ambientGeometry : AmbientStabiliserGeometry
    (Khat := Khat) (D.levi v.1.1) geometry.generic.lambda
    (certificateInertiaAut F algebraicLift commute geometry)
  e9 : SpathE9Provider (Khat := Khat) ambientGeometry
  e10e11 : CliffordGallagherProvider
    (Khat := Khat) ambientGeometry e9 v.1.2

attribute [instance] ExactPairCharacterSource.khatGroup

/-- The structural provider split reconstructs the older
`PairCharacterSource`.  Its conjugation callback is now a theorem obtained
from the structural ambient action on the character inertia group. -/
noncomputable def ExactPairCharacterSource.toPairCharacterSource
    [MulAction (MulAut (H F)) A]
    {ell : ℕ} {InBlock : Irr ℂ (H F) → Prop}
    {Series : Irr ℂ (H F) → Dual → Prop}
    {D : Definitions ℂ (H F) A Block} {coherence : InnerCoherence D}
    {C : Block}
    {global : GlobalInputs F algebraicLift ell InBlock Series D C}
    {v : GenericPair D coherence C}
    {geometry : PairGeometrySource F algebraicLift commute global v}
    [baseNormal : (D.levi v.1.1).Normal]
    [finiteNormalizerFintype : Fintype
      (finiteNormalizer (H := H F) (A := A) v.1.1)]
    (S : ExactPairCharacterSource F algebraicLift commute geometry) :
    PairCharacterSource F algebraicLift commute geometry where
  AmbientGroup := S.Khat
  ambientGroup := S.khatGroup
  ambient := S.e9.toData
  ambientConjugation := by
    intro sigma label_fixed lambda_fixed
    let c : PairAutomorphismCertificate F algebraicLift commute geometry :=
      ⟨sigma, label_fixed, lambda_fixed⟩
    exact S.ambientGeometry.conjugationWitness S.e9 c
  kappa := S.e10e11.kappa
  gallagher := S.e10e11.gallagher
  clifford := S.e10e11.clifford

/-- Install the E5-derived normality instance before asking for the exact
E9--E11 source package. -/
structure ExactCharacterSourceFor
    [MulAction (MulAut (H F)) A]
    {ell : ℕ} {InBlock : Irr ℂ (H F) → Prop}
    {Series : Irr ℂ (H F) → Dual → Prop}
    {D : Definitions ℂ (H F) A Block} {coherence : InnerCoherence D}
    {C : Block}
    {global : GlobalInputs F algebraicLift ell InBlock Series D C}
    {v : GenericPair D coherence C}
    (geometry : PairGeometrySource F algebraicLift commute global v) where
  [finiteNormalizerFintype : Fintype
    (finiteNormalizer (H := H F) (A := A) v.1.1)]
  data :
    letI : (D.levi v.1.1).Normal :=
      (geometry.fmz (1 : E)).fmzLevi_normal
    ExactPairCharacterSource F algebraicLift commute geometry

/-- Convert the source-faithful package to the wrapper consumed by
`lemma_3_5_relative`. -/
noncomputable def ExactCharacterSourceFor.toCharacterSourceFor
    [MulAction (MulAut (H F)) A]
    {ell : ℕ} {InBlock : Irr ℂ (H F) → Prop}
    {Series : Irr ℂ (H F) → Dual → Prop}
    {D : Definitions ℂ (H F) A Block} {coherence : InnerCoherence D}
    {C : Block}
    {global : GlobalInputs F algebraicLift ell InBlock Series D C}
    {v : GenericPair D coherence C}
    {geometry : PairGeometrySource F algebraicLift commute global v}
    (S : ExactCharacterSourceFor F algebraicLift commute geometry) :
    CharacterSourceFor F algebraicLift commute geometry where
  finiteNormalizerFintype := S.finiteNormalizerFintype
  data := by
    letI : Fintype
        (finiteNormalizer (H := H F) (A := A) v.1.1) :=
      S.finiteNormalizerFintype
    letI : (D.levi v.1.1).Normal :=
      (geometry.fmz (1 : E)).fmzLevi_normal
    exact S.data.toPairCharacterSource

/-- Complex-specialised relative form of Lemma 3.6 with the E9--E11 source
boundary exposed by `ExactCharacterSourceFor`.  The E1--E8 data remain the
explicit fields of `global` and `geometry`. -/
theorem lemma_3_5_relative_of_exact_providers
    [MulAction (MulAut (H F)) A]
    (ell : ℕ) (InBlock : Irr ℂ (H F) → Prop)
    (Series : Irr ℂ (H F) → Dual → Prop)
    (D : Definitions ℂ (H F) A Block) (coherence : InnerCoherence D)
    (C : Block)
    (global : GlobalInputs F algebraicLift ell InBlock Series D C)
    (geometry : ∀ v : GenericPair D coherence C,
      PairGeometrySource F algebraicLift commute global v)
    (characters : ∀ v : GenericPair D coherence C,
      ExactCharacterSourceFor F algebraicLift commute (geometry v)) :
    EvenFieldLemma35Conclusion.FixationConclusion
      ell InBlock Series D coherence C global.fieldAction := by
  apply lemma_3_5_relative F algebraicLift commute ell InBlock Series D
    coherence C global geometry
  intro v
  exact (characters v).toCharacterSourceFor

end ModularRep.PaperProofs.EvenFieldLemma35E9E11Providers


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
