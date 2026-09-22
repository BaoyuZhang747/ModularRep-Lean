import ModularRep.PaperProofs.EvenFieldFLZ57CentrelessGate

/-!
# Assumption 5.3 on the sole even-field full-HG family

The family-to-fixed-points group equivalence already determines both family
actions and the concrete root/character transport. This module constructs
the existing FamilyAssumption53Transport from that data and the standard
cyclic Brauer extension principle. No action-naturality, orbit, stabilizer,
extension, or Assumption 5.3 packet is an additional input.

The representative on each side is the original character. The family
extension uses its actual embedded field-inertia subgroup and the root
obtained from the SAME ambient iota by alongMulEquiv. The two Prop-valued
extension assertions are proved separately; no equality of arbitrarily
chosen extension representations is claimed.

This closes only the ambient Assumption 5.3 presentation join. The authentic
full-HG, high-rank own-pair/root/relation, and stronger final-target source
bindings remain separate from this construction.
-/

noncomputable section

namespace ModularRep.PaperProofs.EvenFieldFamilyAssumption53Actual

open Formalisation ModularRep
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.EvenFieldAssumption53Actual
open ModularRep.PaperProofs.EvenFieldConcreteTypeC
open ModularRep.PaperProofs.EvenFieldFLZ57CentrelessGate
open ModularRep.PaperProofs.EvenFieldFLZFullHG
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions

section CanonicalNaturality

variable {p : ℕ} {k K G H E : Type}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Finite G] [Group H] [Finite H] [Group E]

/-- The actual conjugated action is intertwined by the canonical IBr
equivalence, including the inverse/op convention. -/
theorem conjugatedAction_naturality
    (iota : PrimeRegularRootEmbedding p k K G) (e : G ≃* H)
    (rho : E →* MulAut H) (a : E) (psi : IBr iota) :
    IrreducibleBrauerCharacter.equivAlongMulEquiv iota e
        (inverseOpHom ((MulAut.congr e.symm).toMonoidHom.comp rho) a • psi) =
      inverseOpHom rho a •
        IrreducibleBrauerCharacter.equivAlongMulEquiv iota e psi := by
  apply Subtype.ext
  apply PrimeRegularClassFunction.ext
  intro x
  change psi.1 (PrimeRegularElement.map
      (MulAut.congr e.symm (rho a⁻¹)).toMonoidHom
      (PrimeRegularElement.map e.symm.toMonoidHom x)) =
    psi.1 (PrimeRegularElement.map e.symm.toMonoidHom
      (PrimeRegularElement.map (rho a⁻¹).toMonoidHom x))
  congr 1
  apply Subtype.ext
  change e.symm (rho a⁻¹ (e (e.symm x.1))) = e.symm (rho a⁻¹ x.1)
  rw [e.apply_symm_apply]

end CanonicalNaturality

section Family

variable {ell r a : ℕ} {C Fq : Type}
variable [Group C] [Finite C] [Field Fq] [Finite Fq] [CharP Fq 2]
variable (ha : 0 < a) [Finite (FiniteSymplecticFixed r a)]
variable [Finite (FieldGroup a)] [IsCyclic (FieldGroup a)]
variable (scope : FLZFullHGUniverse 2 ell)
variable (coverage : FullHGDefinition35Coverage scope)
variable (model : CentrelessTypeCAmbientModel (r := r) (a := a) scope)
variable (conformal : ConformalStructuralSource r a ha C Fq)

/-- Naturality uses the sole family-to-concrete group equivalence. -/
theorem regularAction_naturality (c : C)
    (psi : IBr (AmbientFamily scope coverage).iota) :
    familyIBrEquiv scope coverage model
        (inverseOpHom (familyConformalAction scope coverage model conformal) c • psi) =
      inverseOpHom (transportedConformalAction r a conformal.multiplier
        conformal.kernelEquiv) c • familyIBrEquiv scope coverage model psi :=
  conjugatedAction_naturality (AmbientFamily scope coverage).iota
    (familyToConcrete scope coverage model)
    (transportedConformalAction r a conformal.multiplier conformal.kernelEquiv) c psi

/-- Field naturality has the same canonical inverse/op action. -/
theorem fieldAction_naturality (sigma : FieldGroup a)
    (psi : IBr (AmbientFamily scope coverage).iota) :
    familyIBrEquiv scope coverage model
        (inverseOpHom (familyFieldAction scope coverage model ha) sigma • psi) =
      inverseOpHom (fieldAction r a ha) sigma •
        familyIBrEquiv scope coverage model psi :=
  conjugatedAction_naturality (AmbientFamily scope coverage).iota
    (familyToConcrete scope coverage model) (fieldAction r a ha) sigma psi

/-- Innerness of conformal conjugation fixes every family Brauer character
through that SAME actual equivalence. -/
theorem family_conformal_fixation :
    letI : MulAction C (IBr (AmbientFamily scope coverage).iota) :=
      rightAutomorphismAction (familyConformalAction scope coverage model conformal)
    ∀ (c : C) (psi : IBr (AmbientFamily scope coverage).iota), c • psi = psi := by
  intro c psi
  change inverseOpHom (familyConformalAction scope coverage model conformal) c • psi = psi
  apply (familyIBrEquiv scope coverage model).injective
  rw [regularAction_naturality ha scope coverage model conformal]
  exact conformal_fixation_actual r a ha
    ((AmbientFamily scope coverage).iota.alongMulEquiv
      (familyToConcrete scope coverage model)) conformal c
    (familyIBrEquiv scope coverage model psi)

/-- The actual family actions are compatible because the conformal action
fixes all of IBr; no compatibility field is assumed. -/
theorem family_compatible :
    FamilyAssumption53ActionCompatibility scope coverage model ha conformal := by
  dsimp only [FamilyAssumption53ActionCompatibility]
  letI : MulAction C (IBr (AmbientFamily scope coverage).iota) :=
    rightAutomorphismAction (familyConformalAction scope coverage model conformal)
  letI : MulAction (FieldGroup a) (IBr (AmbientFamily scope coverage).iota) :=
    rightAutomorphismAction (familyFieldAction scope coverage model ha)
  intro sigma c psi
  rw [family_conformal_fixation ha scope coverage model conformal c psi,
    family_conformal_fixation ha scope coverage model conformal]

/-- The actual regular orbit on the family is a singleton. -/
theorem family_regularOrbit_iff
    (psi representative : IBr (AmbientFamily scope coverage).iota) :
    FamilyAssumption53InRegularOrbit scope coverage model conformal
      psi representative ↔ representative = psi := by
  dsimp only [FamilyAssumption53InRegularOrbit]
  letI : MulAction C (IBr (AmbientFamily scope coverage).iota) :=
    rightAutomorphismAction (familyConformalAction scope coverage model conformal)
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨c, rfl⟩
    exact family_conformal_fixation ha scope coverage model conformal c psi
  · intro h
    subst representative
    exact ⟨1, one_smul C psi⟩

/-- The full family stabilizer has the required actual semidirect product
factorization for every character. -/
theorem family_stabilizerFactorization
    (psi : IBr (AmbientFamily scope coverage).iota) :
    FamilyAssumption53StabilizerFactorization scope coverage model ha conformal
      (family_compatible ha scope coverage model conformal) psi := by
  dsimp only [FamilyAssumption53StabilizerFactorization]
  letI : MulAction C (IBr (AmbientFamily scope coverage).iota) :=
    rightAutomorphismAction (familyConformalAction scope coverage model conformal)
  letI : MulAction (FieldGroup a) (IBr (AmbientFamily scope coverage).iota) :=
    rightAutomorphismAction (familyFieldAction scope coverage model ha)
  exact mem_semidirect_stabilizer_iff_exists_right_factorization
    conformal.conformalFieldAction (family_compatible ha scope coverage model conformal)
    (family_conformal_fixation ha scope coverage model conformal) psi

/-- The family field-inertia extension is constructed on its exact embedded
base with the ambient root transported along the canonical base equivalence.
The only theorem input is the independently quantified cyclic principle. -/
theorem family_fieldExtension
    (principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0}
      ell (AmbientFamily scope coverage).k)
    (psi : IBr (AmbientFamily scope coverage).iota) :
    FamilyAssumption53FieldExtension scope coverage model ha psi := by
  dsimp only [FamilyAssumption53FieldExtension]
  let field := familyFieldAction scope coverage model ha
  letI : MulAction (AmbientFamily scope coverage).H
      (IBr (AmbientFamily scope coverage).iota) :=
    rightAutomorphismAction
      (MulAut.conj : (AmbientFamily scope coverage).H →*
        MulAut (AmbientFamily scope coverage).H)
  letI : MulAction (FieldGroup a) (IBr (AmbientFamily scope coverage).iota) :=
    rightAutomorphismAction field
  let compatible := rightAutomorphismSemidirectCompatible
    (X := IBr (AmbientFamily scope coverage).iota) field
  letI : MulAction ((AmbientFamily scope coverage).H ⋊[field] FieldGroup a)
      (IBr (AmbientFamily scope coverage).iota) :=
    semidirectMulAction field compatible
  have innerFixed : ∀ h : (AmbientFamily scope coverage).H,
      (SemidirectProduct.inl h :
        (AmbientFamily scope coverage).H ⋊[field] FieldGroup a) • psi = psi := by
    intro h
    rw [semidirect_inl_smul]
    exact inner_fixes_ibr (AmbientFamily scope coverage).iota h psi
  let eH := canonicalHToEmbeddedEquiv psi innerFixed
  let embeddedRoot := (AmbientFamily scope coverage).iota.alongMulEquiv eH
  have pullbackIrreducible : IsIrreducibleBrauerCharacter embeddedRoot
      (pullbackPrimeRegularAlongEquiv eH psi.1) :=
    IrreducibleBrauerCharacter.pullback_isIrreducibleBrauerCharacter
      (AmbientFamily scope coverage).iota eH psi
  apply global_extension_actual (AmbientFamily scope coverage).iota field
    principle psi embeddedRoot pullbackIrreducible
  intro d x
  exact canonicalEmbedded_conjugationSquare field psi innerFixed d x

/-- Construct the existing family/concrete audit packet. Its two extension
clauses are Prop-valued existence assertions, both proved on their own exact
embedded base and canonical root; unrelated extensions are not identified. -/
def familyAssumption53Transport
    (principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0}
      ell (AmbientFamily scope coverage).k) :
    FamilyAssumption53Transport ha scope coverage model conformal where
  regularAction_naturality := regularAction_naturality ha scope coverage model conformal
  fieldAction_naturality := fieldAction_naturality ha scope coverage model
  compatible := family_compatible ha scope coverage model conformal
  family := {
    representative := fun psi => {
      representative := psi
      inRegularOrbit := (family_regularOrbit_iff ha scope coverage model conformal psi psi).mpr rfl
      stabilizerFactorization := family_stabilizerFactorization ha scope coverage model conformal psi
      fieldExtension := family_fieldExtension ha scope coverage model principle psi } }
  concrete := flzAssumption53_of_actual ha
    ((AmbientFamily scope coverage).iota.alongMulEquiv
      (familyToConcrete scope coverage model)) conformal principle
  representative_naturality := fun _ => rfl
  orbit_transport := by
    intro psi representative
    rw [family_regularOrbit_iff ha scope coverage model conformal]
    dsimp only [Assumption53InRegularOrbit]
    rw [conformal_orbit_eq_singleton_actual r a ha
      ((AmbientFamily scope coverage).iota.alongMulEquiv
        (familyToConcrete scope coverage model)) conformal]
    rw [Set.mem_singleton_iff]
    exact (familyIBrEquiv scope coverage model).injective.eq_iff.symm
  stabilizer_transport := fun psi =>
    ⟨fun _ => conformal_stabilizer_factorization_actual r a ha
        ((AmbientFamily scope coverage).iota.alongMulEquiv
          (familyToConcrete scope coverage model)) conformal
        (familyIBrEquiv scope coverage model psi),
      fun _ => family_stabilizerFactorization ha scope coverage model conformal psi⟩
  extension_transport := fun psi =>
    ⟨fun _ => field_stabilizer_extension_actual r a ha
        ((AmbientFamily scope coverage).iota.alongMulEquiv
          (familyToConcrete scope coverage model)) principle
        (familyIBrEquiv scope coverage model psi),
      fun _ => family_fieldExtension ha scope coverage model principle psi⟩

end Family

end ModularRep.PaperProofs.EvenFieldFamilyAssumption53Actual


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
