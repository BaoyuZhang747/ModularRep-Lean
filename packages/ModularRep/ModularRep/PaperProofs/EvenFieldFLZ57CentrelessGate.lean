import ModularRep.PaperProofs.EvenFieldUniversalCentralCoverSource
import ModularRep.PaperProofs.EvenFieldFLZBAWMatchedPairCertificate
import ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
import ModularRep.PaperProofs.EvenFieldFLZFullHG
import ModularRep.IrreducibleBrauerCharacterEquiv
import ModularRep.StrictQuasiIsolation

/-!
# Fixed centreless gate for Feng--Li--Zhang, Theorem 5.7

This module fixes the source boundary for the application of Feng--Li--Zhang,
Theorem 5.7, in the centreless even defining characteristic type-C case of
manuscript Proposition 3.9.  It does not prove that theorem.

There is exactly one ambient finite presentation:
`coverage.presentation scope.ambientPair`.  It is identified with the
concrete fixed-point symplectic group through the literal fixed points of the
ambient Steinberg map.  A separate source adapter identifies that map with
`F_2^a`, and hence its field size with `2^a`.

The first arm of Hypothesis 5.5 is family-native.  Its regular-overgroup and
field actions, orbits, stabiliser factorisation, and representation-level
extension are stated on the sole ambient family.  Explicit naturality fields
identify them with the already constructed concrete Assumption 5.3 package.

For the second arm, `scope.semantics`, `coverage`, and `blockSource` remain
the explicit E1/U or E2/U interpretations of the five conditions defining
`H_G`, its finite presentations, and the Definition 3.5 data.  No second
pseudo-source class is introduced.  The strict quasi-isolation audit is the
displayed semisimple-label/centraliser/Levi formula for every pair in
`FullHG scope` and every block of its presented family.  It is not a bare
selectable predicate and cannot omit a represented pair or block.

The ambient identification records the centreless type-C specialisation data
used to apply Theorem 5.7.  Centrelessness and simplicity realise simplicity
of the central quotient, and the full self-universal-cover condition is the
specialised universal-cover hypothesis.  Noncommutativity is contextual
evidence that the target lies in the nonabelian BAW-good domain; it is not an
additional theorem conclusion.  From these fields the kernel constructs the
canonical identity universal `ell'`-cover.  No cover is supplied by the
caller.  The subsidiary pairs in `FullHG scope` carry only the cover-free
Definition 3.5 data required by Hypothesis 5.5(b).

The E2 operation `FLZ57MatchedPairSource.applyTheorem57AndUnpack` returns the
fixed-semantics matched-pair output on that canonical cover.  Its concrete
certificate fixes the cover, automorphism adapters, and bijection.  The final
relation assertion remains a load-bearing U/E2 input: because the family
semantics is opaque, the kernel cannot verify that a caller has not chosen a
proposition equivalent to the desired conclusion.  The separate module
`EvenFieldFLZ57BAWGoodPassage` represents the cited one-way passage from the
published BAW condition to Definition 3.5.
-/

noncomputable section

open scoped Pointwise

namespace ModularRep.PaperProofs.EvenFieldFLZ57CentrelessGate

open Formalisation
open ModularRep
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.ManuscriptVerification.StrictQuasiIsolation
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.EvenFieldAssumption53Actual
open ModularRep.PaperProofs.EvenFieldConcreteTypeC
open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.EvenFieldFLZBAWMatchedPairCertificate
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
open ModularRep.PaperProofs.EvenFieldFLZFullHG
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions

universe u

/-! ## The sole ambient family and its literal Frobenius model -/

/-- The sole ambient presentation used by the gate. -/
abbrev AmbientPresentation {ell : ℕ}
    (scope : FLZFullHGUniverse 2 ell)
    (coverage : FullHGDefinition35Coverage scope) :=
  coverage.presentation scope.ambientPair

/-- The sole ambient family, obtained from the canonical ambient member. -/
abbrev AmbientFamily {ell : ℕ}
    (scope : FLZFullHGUniverse 2 ell)
    (coverage : FullHGDefinition35Coverage scope) :=
  (AmbientPresentation scope coverage).family

/-- Exact type-C identification of the fixed points of the canonical ambient
algebraic pair.  This is E1/U source data, not a second finite presentation. -/
structure CentrelessTypeCAmbientModel {ell r a : ℕ}
    (scope : FLZFullHGUniverse 2 ell) where
  fixedPointModel : scope.ambient.algebraicPair.FixedPointGroup ≃*
    FiniteSymplecticFixed r a

/-- The presented group transported through its literal fixed-point
equivalence to the concrete symplectic fixed-point group. -/
def familyToConcrete {ell r a : ℕ}
    (scope : FLZFullHGUniverse 2 ell)
    (coverage : FullHGDefinition35Coverage scope)
    (model : CentrelessTypeCAmbientModel (r := r) (a := a) scope) :
    (AmbientFamily scope coverage).H ≃* FiniteSymplecticFixed r a :=
  (AmbientPresentation scope coverage).fixedPointEquiv.trans
    model.fixedPointModel

/-- Canonical equivalence on irreducible Brauer characters induced by the
sole family-to-concrete group equivalence. -/
def familyIBrEquiv {ell r a : ℕ}
    [Finite (FiniteSymplecticFixed r a)]
    (scope : FLZFullHGUniverse 2 ell)
    (coverage : FullHGDefinition35Coverage scope)
    (model : CentrelessTypeCAmbientModel (r := r) (a := a) scope) :=
  IrreducibleBrauerCharacter.equivAlongMulEquiv
    (AmbientFamily scope coverage).iota
    (familyToConcrete scope coverage model)

/-- E1/U identification of the literal ambient Steinberg endomorphism with
the standard `a`th Frobenius iterate.  The formula is indexed by the actual
ambient algebraic pair, and `fixedPointModel_apply` ties the induced
fixed-point equivalence to the sole finite presentation. -/
structure AmbientFrobeniusFieldMatch {ell r a : ℕ}
    (scope : FLZFullHGUniverse 2 ell)
    (model : CentrelessTypeCAmbientModel (r := r) (a := a) scope) where
  algebraicGroupModel : scope.ambient.algebraicPair.AlgebraicGroup ≃*
    AmbientSymplectic r
  steinberg_apply : ∀ x : scope.ambient.algebraicPair.AlgebraicGroup,
    algebraicGroupModel (scope.ambient.algebraicPair.steinberg x) =
      definingFrobenius r a (algebraicGroupModel x)
  fixedPointModel_apply :
    ∀ x : scope.ambient.algebraicPair.FixedPointGroup,
      ((model.fixedPointModel x : FiniteSymplecticFixed r a) :
          AmbientSymplectic r) = algebraicGroupModel x.1

/-- The field size associated with the literal Frobenius match.  It is fixed,
not selected by the source adapter. -/
def AmbientFrobeniusFieldMatch.sourceFieldSize
    {ell r a : ℕ} {scope : FLZFullHGUniverse 2 ell}
    {model : CentrelessTypeCAmbientModel (r := r) (a := a) scope}
    (_ : AmbientFrobeniusFieldMatch scope model) : ℕ :=
  2 ^ a

@[simp]
theorem AmbientFrobeniusFieldMatch.sourceFieldSize_eq_two_pow
    {ell r a : ℕ} {scope : FLZFullHGUniverse 2 ell}
    {model : CentrelessTypeCAmbientModel (r := r) (a := a) scope}
    (frobenius : AmbientFrobeniusFieldMatch scope model) :
    frobenius.sourceFieldSize = 2 ^ a :=
  rfl

/-! ## Family-native Assumption 5.3 -/

/-- The conformal action transported back from the concrete fixed-point
group to the sole ambient family. -/
def familyConformalAction
    {ell r a : ℕ} {C Fq : Type}
    [Group C] [Finite C] [Field Fq] [Finite Fq] [CharP Fq 2]
    (scope : FLZFullHGUniverse 2 ell)
    (coverage : FullHGDefinition35Coverage scope)
    (model : CentrelessTypeCAmbientModel (r := r) (a := a) scope)
    {ha : 0 < a} (conformal : ConformalStructuralSource r a ha C Fq) :
    C →* MulAut (AmbientFamily scope coverage).H :=
  (MulAut.congr (familyToConcrete scope coverage model).symm).toMonoidHom.comp
    (transportedConformalAction r a conformal.multiplier
      conformal.kernelEquiv)

/-- The canonical field action transported back to the sole ambient family. -/
def familyFieldAction
    {ell r a : ℕ}
    (scope : FLZFullHGUniverse 2 ell)
    (coverage : FullHGDefinition35Coverage scope)
    (model : CentrelessTypeCAmbientModel (r := r) (a := a) scope)
    (ha : 0 < a) :
    FieldGroup a →* MulAut (AmbientFamily scope coverage).H :=
  (MulAut.congr (familyToConcrete scope coverage model).symm).toMonoidHom.comp
    (fieldAction r a ha)

/-- Regular-overgroup orbit membership stated on the ambient family. -/
def FamilyAssumption53InRegularOrbit
    {ell r a : ℕ} {C Fq : Type}
    [Group C] [Finite C] [Field Fq] [Finite Fq] [CharP Fq 2]
    (scope : FLZFullHGUniverse 2 ell)
    (coverage : FullHGDefinition35Coverage scope)
    (model : CentrelessTypeCAmbientModel (r := r) (a := a) scope)
    {ha : 0 < a} (conformal : ConformalStructuralSource r a ha C Fq)
    (psi representative : IBr (AmbientFamily scope coverage).iota) : Prop :=
  let _ : MulAction C (IBr (AmbientFamily scope coverage).iota) :=
    rightAutomorphismAction
      (familyConformalAction scope coverage model conformal)
  representative ∈ MulAction.orbit C psi

/-- Compatibility of the transported regular-overgroup and field actions. -/
def FamilyAssumption53ActionCompatibility
    {ell r a : ℕ} {C Fq : Type}
    [Group C] [Finite C] [Field Fq] [Finite Fq] [CharP Fq 2]
    (scope : FLZFullHGUniverse 2 ell)
    (coverage : FullHGDefinition35Coverage scope)
    (model : CentrelessTypeCAmbientModel (r := r) (a := a) scope)
    (ha : 0 < a) (conformal : ConformalStructuralSource r a ha C Fq) : Prop :=
  let _ : MulAction C (IBr (AmbientFamily scope coverage).iota) :=
    rightAutomorphismAction
      (familyConformalAction scope coverage model conformal)
  let _ : MulAction (FieldGroup a)
      (IBr (AmbientFamily scope coverage).iota) :=
    rightAutomorphismAction (familyFieldAction scope coverage model ha)
  SemidirectActionCompatible
    (X := IBr (AmbientFamily scope coverage).iota)
    conformal.conformalFieldAction

/-- The stabiliser factorisation of Assumption 5.3 on the ambient family. -/
def FamilyAssumption53StabilizerFactorization
    {ell r a : ℕ} {C Fq : Type}
    [Group C] [Finite C] [Field Fq] [Finite Fq] [CharP Fq 2]
    (scope : FLZFullHGUniverse 2 ell)
    (coverage : FullHGDefinition35Coverage scope)
    (model : CentrelessTypeCAmbientModel (r := r) (a := a) scope)
    (ha : 0 < a) (conformal : ConformalStructuralSource r a ha C Fq)
    (compatible : FamilyAssumption53ActionCompatibility scope coverage model
      ha conformal)
    (psi : IBr (AmbientFamily scope coverage).iota) : Prop :=
  let _ : MulAction C (IBr (AmbientFamily scope coverage).iota) :=
    rightAutomorphismAction
      (familyConformalAction scope coverage model conformal)
  let _ : MulAction (FieldGroup a)
      (IBr (AmbientFamily scope coverage).iota) :=
    rightAutomorphismAction (familyFieldAction scope coverage model ha)
  let _ : MulAction (C ⋊[conformal.conformalFieldAction] FieldGroup a)
      (IBr (AmbientFamily scope coverage).iota) :=
    semidirectMulAction conformal.conformalFieldAction compatible
  ∀ g : C ⋊[conformal.conformalFieldAction] FieldGroup a,
    g ∈ MulAction.stabilizer
        (C ⋊[conformal.conformalFieldAction] FieldGroup a) psi ↔
      ∃ c : C, ∃ sigma : FieldGroup a,
        sigma ∈ MulAction.stabilizer (FieldGroup a) psi ∧
          g = SemidirectProduct.inl c * SemidirectProduct.inr sigma

/-- The representation-level field-stabiliser extension on the ambient
family. -/
def FamilyAssumption53FieldExtension
    {ell r a : ℕ}
    [Finite (FieldGroup a)]
    (scope : FLZFullHGUniverse 2 ell)
    (coverage : FullHGDefinition35Coverage scope)
    (model : CentrelessTypeCAmbientModel (r := r) (a := a) scope)
    (ha : 0 < a)
    (psi : IBr (AmbientFamily scope coverage).iota) : Prop :=
  let field := familyFieldAction scope coverage model ha
  let _ : MulAction (AmbientFamily scope coverage).H
      (IBr (AmbientFamily scope coverage).iota) :=
    rightAutomorphismAction
      (MulAut.conj : (AmbientFamily scope coverage).H →*
        MulAut (AmbientFamily scope coverage).H)
  let _ : MulAction (FieldGroup a)
      (IBr (AmbientFamily scope coverage).iota) :=
    rightAutomorphismAction field
  let compatible := rightAutomorphismSemidirectCompatible
    (X := IBr (AmbientFamily scope coverage).iota) field
  let _ : MulAction
      ((AmbientFamily scope coverage).H ⋊[field] FieldGroup a)
      (IBr (AmbientFamily scope coverage).iota) :=
    semidirectMulAction field compatible
  let innerFixed : ∀ h : (AmbientFamily scope coverage).H,
      (SemidirectProduct.inl h :
        (AmbientFamily scope coverage).H ⋊[field] FieldGroup a) • psi = psi :=
    fun h ↦ by
      rw [semidirect_inl_smul]
      exact inner_fixes_ibr (AmbientFamily scope coverage).iota h psi
  let groupEquiv := canonicalHToEmbeddedEquiv psi innerFixed
  let embeddedRoot :=
    (AmbientFamily scope coverage).iota.alongMulEquiv groupEquiv
  ∃ W : FDRep (AmbientFamily scope coverage).k
      (embeddedHStabilizer (phi := field) psi),
    Representation.IsIrreducible W.ρ ∧
    pullbackPrimeRegularAlongEquiv groupEquiv psi.1 =
      Representation.brauerCharacterOfRootEmbedding W.ρ embeddedRoot ∧
    Nonempty (Representation.Extension
      (embeddedHStabilizer (phi := field) psi) W.ρ)

/-- One family-native representative satisfying all three clauses. -/
structure FamilyAssumption53Representative
    {ell r a : ℕ} {C Fq : Type}
    [Group C] [Finite C] [Field Fq] [Finite Fq] [CharP Fq 2]
    [Finite (FieldGroup a)]
    (scope : FLZFullHGUniverse 2 ell)
    (coverage : FullHGDefinition35Coverage scope)
    (model : CentrelessTypeCAmbientModel (r := r) (a := a) scope)
    (ha : 0 < a) (conformal : ConformalStructuralSource r a ha C Fq)
    (compatible : FamilyAssumption53ActionCompatibility scope coverage model
      ha conformal)
    (psi : IBr (AmbientFamily scope coverage).iota) where
  representative : IBr (AmbientFamily scope coverage).iota
  inRegularOrbit : FamilyAssumption53InRegularOrbit scope coverage model
    conformal psi representative
  stabilizerFactorization : FamilyAssumption53StabilizerFactorization
    scope coverage model ha conformal compatible representative
  fieldExtension : FamilyAssumption53FieldExtension scope coverage model ha
    representative

/-- Literal Assumption 5.3 data on the ambient family. -/
structure FamilyFLZAssumption53
    {ell r a : ℕ} {C Fq : Type}
    [Group C] [Finite C] [Field Fq] [Finite Fq] [CharP Fq 2]
    [Finite (FieldGroup a)]
    (scope : FLZFullHGUniverse 2 ell)
    (coverage : FullHGDefinition35Coverage scope)
    (model : CentrelessTypeCAmbientModel (r := r) (a := a) scope)
    (ha : 0 < a) (conformal : ConformalStructuralSource r a ha C Fq)
    (compatible : FamilyAssumption53ActionCompatibility scope coverage model
      ha conformal) where
  representative : ∀ psi : IBr (AmbientFamily scope coverage).iota,
    FamilyAssumption53Representative scope coverage model ha conformal
      compatible psi

/-- E1/U transport audit from the already constructed concrete Assumption
5.3 package to the literal family-native actions, orbits, stabilisers, and
extensions above. -/
structure FamilyAssumption53Transport
    {ell r a : ℕ} {C Fq : Type}
    [Group C] [Finite C]
    [Field Fq] [Finite Fq] [CharP Fq 2]
    (ha : 0 < a) [Finite (FiniteSymplecticFixed r a)]
    [Finite (FieldGroup a)] [IsCyclic (FieldGroup a)]
    (scope : FLZFullHGUniverse 2 ell)
    (coverage : FullHGDefinition35Coverage scope)
    (model : CentrelessTypeCAmbientModel (r := r) (a := a) scope)
    (conformal : ConformalStructuralSource r a ha C Fq) where
  regularAction_naturality : ∀ (c : C)
      (psi : IBr (AmbientFamily scope coverage).iota),
    familyIBrEquiv scope coverage model (inverseOpHom
        (familyConformalAction scope coverage model conformal) c • psi) =
      inverseOpHom
        (transportedConformalAction r a conformal.multiplier
          conformal.kernelEquiv) c • familyIBrEquiv scope coverage model psi
  fieldAction_naturality : ∀ (sigma : FieldGroup a)
      (psi : IBr (AmbientFamily scope coverage).iota),
    familyIBrEquiv scope coverage model
        (inverseOpHom (familyFieldAction scope coverage model ha) sigma •
          psi) =
      inverseOpHom (fieldAction r a ha) sigma •
        familyIBrEquiv scope coverage model psi
  compatible : FamilyAssumption53ActionCompatibility scope coverage model
    ha conformal
  family : FamilyFLZAssumption53 scope coverage model ha conformal compatible
  concrete : FLZAssumption53 ha
    ((AmbientFamily scope coverage).iota.alongMulEquiv
      (familyToConcrete scope coverage model)) conformal
  representative_naturality :
    ∀ psi : IBr (AmbientFamily scope coverage).iota,
      familyIBrEquiv scope coverage model
          (family.representative psi).representative =
        (concrete.representative
          (familyIBrEquiv scope coverage model psi)).representative
  orbit_transport : ∀ psi representative,
    FamilyAssumption53InRegularOrbit scope coverage model conformal
        psi representative ↔
      Assumption53InRegularOrbit ha
        ((AmbientFamily scope coverage).iota.alongMulEquiv
          (familyToConcrete scope coverage model)) conformal
        (familyIBrEquiv scope coverage model psi)
        (familyIBrEquiv scope coverage model representative)
  stabilizer_transport : ∀ representative,
    FamilyAssumption53StabilizerFactorization scope coverage model ha
        conformal compatible representative ↔
      Assumption53StabilizerFactorization ha
        ((AmbientFamily scope coverage).iota.alongMulEquiv
          (familyToConcrete scope coverage model)) conformal
        (familyIBrEquiv scope coverage model representative)
  extension_transport : ∀ representative,
    FamilyAssumption53FieldExtension scope coverage model ha representative ↔
      Assumption53FieldExtension ha
        ((AmbientFamily scope coverage).iota.alongMulEquiv
          (familyToConcrete scope coverage model))
        (familyIBrEquiv scope coverage model representative)

/-! ## Strict-block audit on every member of the relative `H_G` carrier -/

/-- Literal dual-centraliser data in the source definition of strict
quasi-isolation.  Exact identification of these objects with the dual
algebraic group and its two centralisers remains E1/U. -/
structure SourceStrictBlockModel (Block : Type u) where
  Dual : Type u
  [groupDual : Group Dual]
  label : Block → Dual
  finiteCentralizer : Dual → Subgroup Dual
  connectedCentralizer : Dual → Subgroup Dual
  IsProperLevi : Set Dual → Prop

attribute [instance] SourceStrictBlockModel.groupDual

/-- The source-shaped strict quasi-isolation formula. -/
def SourceStrictBlockModel.IsStrict {Block : Type u}
    (model : SourceStrictBlockModel Block) (block : Block) : Prop :=
  NotContainedInProperLevi
    (((model.finiteCentralizer (model.label block) : Set model.Dual) *
      (model.connectedCentralizer (model.label block) : Set model.Dual)))
    model.IsProperLevi

/-! `scope.semantics`, `coverage`, and `blockSource` are themselves the fixed
E1/U presentations of the five `H_G` predicates, every fixed-point group and
set of blocks, and the Definition 3.5 stabiliser and modular-triple relation.
No second pseudo-source class or duplicate relation is introduced here. -/

/-- Source-shaped strictness data for every represented pair and every block.

The carrier quantifies directly over all `pair : FullHG scope` and the actual
block type of `coverage.presentation pair`.  Consequently neither a selected
pair family nor a block equivalence can omit an obligation.  The iff prevents
`strictSource.predicate` from being set to false unless the literal
centraliser/Levi formula is also false for that block. -/
structure FullHGStrictSourceAudit {ell : ℕ}
    (scope : FLZFullHGUniverse 2 ell)
    (coverage : FullHGDefinition35Coverage scope)
    (strictSource : FullHGStrictQuasiIsolationAdapter coverage) where
  strictModel : ∀ pair : FullHG scope,
    SourceStrictBlockModel (coverage.presentation pair).family.Block
  strict_iff : ∀ (pair : FullHG scope)
      (block : (coverage.presentation pair).family.Block),
    (strictModel pair).IsStrict block ↔
      strictSource.predicate pair block

/-! ## Ambient source identification and canonical cover -/

/-- Centreless type-C specialisation data for the Theorem 5.7 application.

The source requires simplicity of the fixed-point central quotient and that
the fixed-point group be its universal cover.  Here `centerless` together
with `simple` realises the former condition, while `ownUniversalCover`
realises the latter.  `nonabelian` records the contextual BAW-good domain,
not an additional published Theorem 5.7 premise.  The separate universal
  `ell'`-cover used by the BAW-good carrier is derived below rather than
  accepted as an input. -/
structure CentrelessTypeCSourceIdentification
    {ell r a : ℕ}
    (scope : FLZFullHGUniverse 2 ell)
    (coverage : FullHGDefinition35Coverage scope)
    (model : CentrelessTypeCAmbientModel (r := r) (a := a) scope)
    (frobenius : AmbientFrobeniusFieldMatch scope model) where
  centerless : Subgroup.center (AmbientFamily scope coverage).H = ⊥
  simple : IsSimpleGroup (AmbientFamily scope coverage).H
  nonabelian : ¬ IsMulCommutative (AmbientFamily scope coverage).H
  ownUniversalCover : IsOwnUniversalCover (AmbientFamily scope coverage).H

/-- A nonabelian simple ambient group is perfect. -/
theorem CentrelessTypeCSourceIdentification.perfect
    {ell r a : ℕ}
    {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    {model : CentrelessTypeCAmbientModel (r := r) (a := a) scope}
    {frobenius : AmbientFrobeniusFieldMatch scope model}
    (identification : CentrelessTypeCSourceIdentification scope coverage model
      frobenius) :
    commutator (AmbientFamily scope coverage).H = ⊤ := by
  letI : IsSimpleGroup (AmbientFamily scope coverage).H :=
    identification.simple
  have hnormal :
      (commutator (AmbientFamily scope coverage).H).Normal := inferInstance
  rcases hnormal.eq_bot_or_eq_top with h | h
  · exact (identification.nonabelian
      ((commutator_eq_bot_iff _).mp h)).elim
  · exact h

/-- The canonical universal prime-to-`ell` cover in the centreless case is the
identity map of the ambient group.  In particular, the Theorem 5.7 source does
not receive a caller-selected cover. -/
def CentrelessTypeCSourceIdentification.identityEllPrimeCover
    {ell r a : ℕ}
    {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    {model : CentrelessTypeCAmbientModel (r := r) (a := a) scope}
    {frobenius : AmbientFrobeniusFieldMatch scope model}
    (identification : CentrelessTypeCSourceIdentification scope coverage model
      frobenius) :
    EllPrimeCoverSource ell (AmbientFamily scope coverage).H where
  S := (AmbientFamily scope coverage).H
  groupS := inferInstance
  fintypeS := inferInstance
  quotient := MonoidHom.id _
  quotient_surjective := Function.surjective_id
  quotient_kernel := by
    simpa [identification.centerless]
  perfect := identification.perfect
  simple := identification.simple
  nonabelian := identification.nonabelian
  centerPrimeTo := by
    simpa [identification.centerless] using
      (AmbientFamily scope coverage).ellPrime.not_dvd_one
  maximal := by
    intro D _ _ f hsurjective hcentral hperfect _
    rcases identification.ownUniversalCover.2 D f
        ⟨hsurjective, hcentral⟩ with ⟨lift, hlift, _⟩
    exact ⟨lift,
      centralExtension_section_surjective f hcentral lift hlift hperfect,
      hlift⟩

/-- Kernel proof that the coefficient prime does not divide the source field
size `2^a`. -/
theorem coefficientPrime_not_dvd_two_pow
    {ell : ℕ} (scope : FLZFullHGUniverse 2 ell)
    (coverage : FullHGDefinition35Coverage scope) (a : ℕ) :
    ¬ ell ∣ 2 ^ a := by
  intro hdiv
  have hdivTwo : ell ∣ 2 :=
    (AmbientFamily scope coverage).ellPrime.dvd_of_dvd_pow hdiv
  have hellTwo : ell = 2 :=
    (Nat.prime_dvd_prime_iff_eq
      (AmbientFamily scope coverage).ellPrime Nat.prime_two).mp hdivTwo
  exact scope.distinctPrimes hellTwo

/-- The same prime exclusion written for the field-size object in the
literal Frobenius match. -/
theorem coefficientPrime_not_dvd_sourceFieldSize
    {ell r a : ℕ} (scope : FLZFullHGUniverse 2 ell)
    (coverage : FullHGDefinition35Coverage scope)
    (model : CentrelessTypeCAmbientModel (r := r) (a := a) scope)
    (frobenius : AmbientFrobeniusFieldMatch scope model) :
    ¬ ell ∣ frobenius.sourceFieldSize := by
  rw [frobenius.sourceFieldSize_eq_two_pow]
  exact coefficientPrime_not_dvd_two_pow scope coverage a

/-- Both arms of Hypothesis 5.5 and every source-identification input needed
by the fixed centreless type-C invocation. -/
structure FLZ57ExplicitHypotheses
    {ell r a : ℕ} {C Fq : Type}
    [Group C] [Finite C]
    [Field Fq] [Finite Fq] [CharP Fq 2]
    (ha : 0 < a) [Finite (FiniteSymplecticFixed r a)]
    [Finite (FieldGroup a)] [IsCyclic (FieldGroup a)]
    (scope : FLZFullHGUniverse 2 ell)
    (coverage : FullHGDefinition35Coverage scope)
    (model : CentrelessTypeCAmbientModel (r := r) (a := a) scope)
    (frobenius : AmbientFrobeniusFieldMatch scope model)
    (conformal : ConformalStructuralSource r a ha C Fq)
    (blockSource : FullHGBlockSource coverage)
    (strictSource : FullHGStrictQuasiIsolationAdapter coverage)
    (identification : CentrelessTypeCSourceIdentification scope coverage model
      frobenius) where
  rankAtLeastFour : 4 ≤ r
  assumption53 : FamilyAssumption53Transport ha scope coverage model conformal
  strictnessAudit : FullHGStrictSourceAudit scope coverage strictSource
  strictBlocks :
    FullHGRelativeHypothesis55StrictBlocks blockSource strictSource

/-- The fixed source interpretation of BAW-goodness for the sole ambient block
family.  Its exact cover and automorphism adapters are fixed by its type. -/
abbrev AmbientFLZBAWGoodSemantics {ell r a : ℕ}
    (scope : FLZFullHGUniverse 2 ell)
    (coverage : FullHGDefinition35Coverage scope)
    (model : CentrelessTypeCAmbientModel (r := r) (a := a) scope)
    (frobenius : AmbientFrobeniusFieldMatch scope model)
    (blockSource : FullHGBlockSource coverage)
    (identification : CentrelessTypeCSourceIdentification scope coverage model
      frobenius) :=
  FLZBAWGoodFamilySemantics (AmbientFamily scope coverage)
    identification.identityEllPrimeCover
    (fun block ↦ blockSource.automorphisms scope.ambientPair block)

/-- BAW-good witnesses for every block of the sole ambient presentation, all
indexed by the canonical identity cover and one fixed source semantics. -/
abbrev AmbientFLZBAWGoodFamilyWitness {ell r a : ℕ}
    (scope : FLZFullHGUniverse 2 ell)
    (coverage : FullHGDefinition35Coverage scope)
    (model : CentrelessTypeCAmbientModel (r := r) (a := a) scope)
    (frobenius : AmbientFrobeniusFieldMatch scope model)
    (blockSource : FullHGBlockSource coverage)
    (identification : CentrelessTypeCSourceIdentification scope coverage model
      frobenius)
    (semantics : AmbientFLZBAWGoodSemantics scope coverage model frobenius
      blockSource identification) :=
  FLZBAWGoodFamilyWitness (AmbientFamily scope coverage)
    identification.identityEllPrimeCover
    (fun block ↦ blockSource.automorphisms scope.ambientPair block) semantics

/-- Matched-pair certificates for all blocks of the sole ambient family.  The
cover and every automorphism adapter are fixed by the ambient identification
and block source. -/
abbrev AmbientBroughSpathMatchedPairFamilyCertificate {ell r a : ℕ}
    (scope : FLZFullHGUniverse 2 ell)
    (coverage : FullHGDefinition35Coverage scope)
    (model : CentrelessTypeCAmbientModel (r := r) (a := a) scope)
    (frobenius : AmbientFrobeniusFieldMatch scope model)
    (blockSource : FullHGBlockSource coverage)
    (identification : CentrelessTypeCSourceIdentification scope coverage model
      frobenius) :=
  BroughSpathMatchedPairFamilyCertificate (AmbientFamily scope coverage)
    identification.identityEllPrimeCover
    (fun block ↦ blockSource.automorphisms scope.ambientPair block)

/-- The fixed-semantics output attributed to Theorem 5.7 after unpacking its
BAW-good conclusion.  The concrete matched-pair certificate fixes the cover,
automorphism adapters, and bijection, while the relation source fixes the
published BAW-good relation at that bijection.  Lean checks and reuses these
indices.  Their mathematical matched-pair content belongs to the E2/U
theorem-and-unpacking boundary. -/
structure FLZ57MatchedPairOutput {ell r a : ℕ}
    (scope : FLZFullHGUniverse 2 ell)
    (coverage : FullHGDefinition35Coverage scope)
    (model : CentrelessTypeCAmbientModel (r := r) (a := a) scope)
    (frobenius : AmbientFrobeniusFieldMatch scope model)
    (blockSource : FullHGBlockSource coverage)
    (identification : CentrelessTypeCSourceIdentification scope coverage model
      frobenius)
    (semantics : AmbientFLZBAWGoodSemantics scope coverage model frobenius
      blockSource identification) : Type 1 where
  certificate :
    AmbientBroughSpathMatchedPairFamilyCertificate scope coverage model
      frobenius blockSource identification
  relationSource : BroughSpathToBAWGoodRelationFamilySource
    certificate semantics

/-- Kernel construction of the BAW-good family witness from the explicit
matched-pair output. -/
def FLZ57MatchedPairOutput.toBAWGoodFamilyWitness
    {ell r a : ℕ}
    {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    {model : CentrelessTypeCAmbientModel (r := r) (a := a) scope}
    {frobenius : AmbientFrobeniusFieldMatch scope model}
    {blockSource : FullHGBlockSource coverage}
    {identification : CentrelessTypeCSourceIdentification scope coverage model
      frobenius}
    {semantics : AmbientFLZBAWGoodSemantics scope coverage model frobenius
      blockSource identification}
    (output : FLZ57MatchedPairOutput scope coverage model frobenius blockSource
      identification semantics) :
    AmbientFLZBAWGoodFamilyWitness scope coverage model frobenius blockSource
      identification semantics :=
  output.certificate.toBAWGoodFamilyWitness output.relationSource

/-- The public E2 interface for Feng--Li--Zhang, Theorem 5.7, together with
the fixed-semantics unpacking of its BAW-good conclusion into matched-pair data.
The fixed quotient-fibre completion is not part of this interface. -/
structure FLZ57MatchedPairSource
    {ell r a : ℕ} {C Fq : Type}
    [Group C] [Finite C]
    [Field Fq] [Finite Fq] [CharP Fq 2]
    (ha : 0 < a) [Finite (FiniteSymplecticFixed r a)]
    [Finite (FieldGroup a)] [IsCyclic (FieldGroup a)]
    (scope : FLZFullHGUniverse 2 ell)
    (coverage : FullHGDefinition35Coverage scope)
    (model : CentrelessTypeCAmbientModel (r := r) (a := a) scope)
    (frobenius : AmbientFrobeniusFieldMatch scope model)
    (conformal : ConformalStructuralSource r a ha C Fq)
    (blockSource : FullHGBlockSource coverage)
    (strictSource : FullHGStrictQuasiIsolationAdapter coverage)
    (identification : CentrelessTypeCSourceIdentification scope coverage model
      frobenius)
    (semantics : AmbientFLZBAWGoodSemantics scope coverage model frobenius
      blockSource identification) : Prop where
  applyTheorem57AndUnpack :
    ∀ hypotheses : FLZ57ExplicitHypotheses ha scope coverage model frobenius
        conformal blockSource strictSource identification,
      (¬ ell ∣ frobenius.sourceFieldSize) →
      Nonempty (FLZ57MatchedPairOutput scope coverage model frobenius
        blockSource identification semantics)

/-- Apply the fixed Theorem 5.7 and unpacking interface using the kernel proof
that `ell` does not divide the field size fixed by `frobenius`. -/
theorem matchedPairOutput_consequence_of_theorem57
    {ell r a : ℕ} {C Fq : Type}
    [Group C] [Finite C]
    [Field Fq] [Finite Fq] [CharP Fq 2]
    (ha : 0 < a) [Finite (FiniteSymplecticFixed r a)]
    [Finite (FieldGroup a)] [IsCyclic (FieldGroup a)]
    (scope : FLZFullHGUniverse 2 ell)
    (coverage : FullHGDefinition35Coverage scope)
    (model : CentrelessTypeCAmbientModel (r := r) (a := a) scope)
    (frobenius : AmbientFrobeniusFieldMatch scope model)
    (conformal : ConformalStructuralSource r a ha C Fq)
    (blockSource : FullHGBlockSource coverage)
    (strictSource : FullHGStrictQuasiIsolationAdapter coverage)
    (identification : CentrelessTypeCSourceIdentification scope coverage model
      frobenius)
    {semantics : AmbientFLZBAWGoodSemantics scope coverage model frobenius
      blockSource identification}
    (cited : FLZ57MatchedPairSource ha scope coverage model frobenius conformal
      blockSource strictSource identification semantics)
    (hypotheses : FLZ57ExplicitHypotheses ha scope coverage model frobenius
      conformal blockSource strictSource identification) :
    Nonempty (FLZ57MatchedPairOutput scope coverage model frobenius blockSource
      identification semantics) :=
  cited.applyTheorem57AndUnpack hypotheses
    (coefficientPrime_not_dvd_sourceFieldSize scope coverage model frobenius)

end ModularRep.PaperProofs.EvenFieldFLZ57CentrelessGate


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
