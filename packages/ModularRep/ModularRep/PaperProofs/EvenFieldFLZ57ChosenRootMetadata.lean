import ModularRep.PaperProofs.EvenFieldFLZ57CentrelessGate
import ModularRep.PaperProofs.TypeCCoherentFiniteRootConvention

/-!
# The strong FLZ 5.7 output jointly chosen in one modular system

The family, its ambient root and its exact selected quotient reductions are
fixed before the source is invoked. Admissibility binds those existing roots
to ONE authenticated standard modular system. It does not change the family
or assert that unrelated fixed tables admit a common extension.

The metadata records only the roots of the SAME selected strong output:
quotient, own quotient, normalizer, ambient, local ambient, and both roots
at every actual intermediate subgroup. It contains no character equality,
extension, block induction, reverse fibre, normalization or covariance law.

The E2 interface is the existing FLZ Theorem 5.7 and fixed-semantics unpacking
carried out under the standard system explicitly fixed in FLZ Section 2.2,
p.5. Its domain keeps every old group, full-HG, hypothesis, cover and relation
index. The scalar/specified source interpretations remain E1. It is not a K
upgrade of an arbitrary old strong output or an assertion that every abstract
Convention is a standard modular-system realization.

Specified quotient dictionaries remain separate. Q=1 normalization and
cross-block construction are not source fields here. No complete target follows
from this file; the consumers only forget or retain the joint metadata.
-/

noncomputable section

namespace ModularRep.PaperProofs.EvenFieldFLZ57ChosenRootMetadata

open ModularRep CharacterWeight
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family
open EvenFieldFLZBAWGoodFamily EvenFieldFLZQuotientBlockFibre
open EvenFieldFLZ57CentrelessGate EvenFieldFLZFullHG
open EvenFieldAssumption53Actual EvenFieldConcreteTypeC
open TypeCCoherentFiniteRootConvention

universe u

section FamilyMetadata

variable {ell : ℕ} (family : Definition35Family.{u} ell)
variable (C : Convention ell family.k family.K)

/-- Exact E1 root dictionary on the PRE-EXISTING family and every selected
quotient table. No independently chosen own-normalizer packet is quantified.
Both equations bind actual root records, not just one character's values. -/
structure FamilyRootAdmissibility : Prop where
  ambient_eq : family.iota = C.rootAt family.H
  selected_eq : ∀ (block : family.Block)
      (w : Definition35Weight (family.problem block)),
    (family.localReduction block w).iota =
      C.rootAt (NormalizerQuotient (selectedRadical (family.problem block) w))

variable {family}

/-- Scalar metadata of ONE actual selected matched packet. The every-J
field retains the actual subgroup, base inclusion and dependent record. -/
structure MatchedRootMetadata {block : family.Block}
    {reference psi : Definition35Brauer (family.problem block)}
    {w : Definition35Weight (family.problem block)}
    (M : SpathMatchedBlockCondition (family.problem block) reference psi w) : Prop where
  quotient_eq : M.quotient.iota =
    C.rootAt (CentralCharacterQuotient (family.problem block) reference)
  weight_eq : M.weight.iota =
    C.rootAt (NormalizerQuotient (quotientRadical (family.problem block) reference w))
  normalizer_eq : M.localInflation.iota =
    C.rootAt (Subgroup.normalizer
      (quotientRadical (family.problem block) reference w :
        Set (CentralCharacterQuotient (family.problem block) reference)))
  ambient_eq : M.extensions.ambientRoot = C.rootAt M.ambient.A
  localAmbient_eq : M.extensions.localAmbientRoot =
    C.rootAt (AmbientLocalGroup (family.problem block) reference psi w
      M.quotient M.ambient)
  intermediate_eq : ∀ (J : Subgroup M.ambient.A) (hJ : M.ambient.base ≤ J),
    let I := M.intermediateBlocks.equalityAt J hJ
    I.globalRoot = C.rootAt ↥J ∧
      I.localRoot = C.rootAt (IntermediateLocalNormalizer (w := w) M.ambient J)

/-- Only the packets actually stored by W are bound to C. No replacement of
W, its omega, roots, extensions or intermediate choices is asserted. -/
structure RelativeRootMetadata {cover : EllPrimeCoverSource ell family.H}
    {block : family.Block}
    (W : RelativeBlockConditionWitness family cover block) : Prop where
  matched : ∀ psi : Definition35Brauer (family.problem block),
    MatchedRootMetadata C (W.matched psi)

namespace RelativeRootMetadata

variable {C} {cover : EllPrimeCoverSource ell family.H} {block : family.Block}
variable {W : RelativeBlockConditionWitness family cover block}

/-- All chosen quotient roots equal the SAME computed C root, so the old
fixed quotient-root interface is constructed without a further source. -/
def fixedQuotientRootSource (metadata : RelativeRootMetadata C W) :
    FixedQuotientRootSource W where
  matchedRoot_eq_reference psi :=
    (metadata.matched psi).quotient_eq.trans
      (metadata.matched W.reference).quotient_eq.symm

end RelativeRootMetadata
end FamilyMetadata

section StrongOutput

variable {ell r a : ℕ}
variable (scope : FLZFullHGUniverse 2 ell)
variable (coverage : FullHGDefinition35Coverage scope)
variable (model : CentrelessTypeCAmbientModel (r := r) (a := a) scope)
variable (frobenius : AmbientFrobeniusFieldMatch scope model)
variable (blockSource : FullHGBlockSource coverage)
variable (identification : CentrelessTypeCSourceIdentification scope coverage model frobenius)
variable (semantics : AmbientFLZBAWGoodSemantics scope coverage model frobenius
  blockSource identification)
variable (C : Convention ell (AmbientFamily scope coverage).k
  (AmbientFamily scope coverage).K)

/-- The scalar convention is recorded for every actual block certificate
and only its own selected matched packets, with the SAME standard semantics. -/
structure ChosenRootMetadata
    (output : FLZ57MatchedPairOutput scope coverage model frobenius blockSource
      identification semantics) : Prop where
  block : ∀ b : (AmbientFamily scope coverage).Block,
    RelativeRootMetadata C (output.certificate.blockCertificate b).relative

end StrongOutput

section JointPublishedChoice

variable {ell r a : ℕ} {CSp Fq : Type}
variable [Group CSp] [Finite CSp] [Field Fq] [Finite Fq] [CharP Fq 2]
variable (ha : 0 < a) [Finite (FiniteSymplecticFixed r a)]
variable [Finite (FieldGroup a)] [IsCyclic (FieldGroup a)]
variable (scope : FLZFullHGUniverse 2 ell)
variable (coverage : FullHGDefinition35Coverage scope)
variable (model : CentrelessTypeCAmbientModel (r := r) (a := a) scope)
variable (frobenius : AmbientFrobeniusFieldMatch scope model)
variable (conformal : ConformalStructuralSource r a ha CSp Fq)
variable (blockSource : FullHGBlockSource coverage)
variable (strictSource : FullHGStrictQuasiIsolationAdapter coverage)
variable (identification : CentrelessTypeCSourceIdentification scope coverage model frobenius)
variable (semantics : AmbientFLZBAWGoodSemantics scope coverage model frobenius
  blockSource identification)
variable (C : Convention ell (AmbientFamily scope coverage).k
  (AmbientFamily scope coverage).K)

/-- Exact FLZ 5.7 construction under its fixed standard modular system.
The E1 interpretation authenticates C, the coefficient realization and the
existing specified source data; the admissibility index binds the PRE-EXISTING
ambient and selected quotient tables. No instance for arbitrary records is
asserted. The sole E2 field keeps the old hypothesis and field-size exclusion,
and jointly chooses its old output plus scalar metadata, never a bare W input.

This is not an invocation of the old bare source followed by an upgrade.
Specified quotient operations, normalization and cross-block coherence are
separate from this interface. -/
structure JointFLZ57MatchedPairSource
    (admissible : FamilyRootAdmissibility (AmbientFamily scope coverage) C) : Prop where
  applyTheorem57AndUnpack :
    ∀ hypotheses : FLZ57ExplicitHypotheses ha scope coverage model frobenius
        conformal blockSource strictSource identification,
      (¬ ell ∣ frobenius.sourceFieldSize) →
      Nonempty {output : FLZ57MatchedPairOutput scope coverage model frobenius
          blockSource identification semantics //
        ChosenRootMetadata scope coverage model frobenius blockSource
          identification semantics C output}

namespace JointFLZ57MatchedPairSource

variable {admissible : FamilyRootAdmissibility (AmbientFamily scope coverage) C}
variable {ha scope coverage model frobenius conformal blockSource strictSource
  identification semantics C}
variable (source : JointFLZ57MatchedPairSource ha scope coverage model frobenius
  conformal blockSource strictSource identification semantics C admissible)

/-- Forget only the chosen metadata, obtaining the existing weaker source
on the SAME ambient family, cover, automorphism adapters and semantics. -/
def toBareSource :
    FLZ57MatchedPairSource ha scope coverage model frobenius conformal
      blockSource strictSource identification semantics where
  applyTheorem57AndUnpack hypotheses hnot := by
    obtain ⟨output⟩ := source.applyTheorem57AndUnpack hypotheses hnot
    exact ⟨output.1⟩

/-- Choose once from the joint existential; the nondivisibility premise is
the existing K consequence of the fixed field size and coefficient prime. -/
def choose (hypotheses : FLZ57ExplicitHypotheses ha scope coverage model frobenius
    conformal blockSource strictSource identification) :
    {output : FLZ57MatchedPairOutput scope coverage model frobenius blockSource
        identification semantics //
      ChosenRootMetadata scope coverage model frobenius blockSource
        identification semantics C output} :=
  Classical.choice (source.applyTheorem57AndUnpack hypotheses
    (coefficientPrime_not_dvd_sourceFieldSize scope coverage model frobenius))

/-- The existing BAW relation is retained at the SAME jointly chosen
certificate's omega. This is not a complete original-family conclusion. -/
def bawGoodFamily (hypotheses : FLZ57ExplicitHypotheses ha scope coverage model frobenius
    conformal blockSource strictSource identification) :
    AmbientFLZBAWGoodFamilyWitness scope coverage model frobenius blockSource
      identification semantics :=
  (source.choose hypotheses).1.toBAWGoodFamilyWitness

end JointFLZ57MatchedPairSource
end JointPublishedChoice

end ModularRep.PaperProofs.EvenFieldFLZ57ChosenRootMetadata


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
