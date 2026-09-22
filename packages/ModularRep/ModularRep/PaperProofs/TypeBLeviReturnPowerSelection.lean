import ModularRep.PaperProofs.TypeBLeviRepresentativeSelection

/-!
# Fixed-base selection from the same actual return and standard power

The return homomorphism is the original local action conjugated through the
finite-model identification. Its factorization through the specified standard
field/graph subgroup follows from cyclic generation and a group-point square.
The original return subgroup and its kernel are retained.

The standard selector is used only at the canonical image of the actual local
base. In particular, a principal-supported field-fixation theorem does not
become a selector for every Brauer character. The actual finite-model and
common-adjoint identifications, and authentication of the full standard
field/graph subgroup and power, remain explicit E1/E2/U obligations.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBLeviReturnPowerSelection

open Formalisation
open TypeBRegularLeviRationalCarriers TypeBComponentCycleNormalization
open TypeBRegularLeviCharacterActionAdapter TypeBComponentReturnOriginalCarriers
open EvenFieldAssumption53Relative TypeBLemma47LeviApplication
open TypeBLeviRepresentativeCarriers TypeBLeviRepresentativeSelection
open TypeBLeviRepresentativeFactorSelector TypeBComponentReturnCarrierTransport
open ModularRep.ManuscriptVerification.StabilizerFactorizationTransport

section ReturnHom

variable {H S R : Type} [Group H] [Group S] [Group R]

/-- The return is computed from the same group identification and actual action. -/
abbrev canonicalReturn (e : H ≃* S) (rho : R →* MulAut H) : R →* MulAut S :=
  transportedAut e rho

/-- The supplied value square identifies the positive actual generator. -/
theorem canonicalReturn_generator (e : H ≃* S) (rho : R →* MulAut H)
    (P : Subgroup (MulAut S)) (generator : R) (standardGenerator : P)
    (value : ∀ x, e (rho generator x) = (standardGenerator : MulAut S) (e x)) :
    canonicalReturn e rho generator = (standardGenerator : MulAut S) := by
  ext s
  change e (rho generator (e.symm s)) = (standardGenerator : MulAut S) s
  simpa only [e.apply_symm_apply] using value (e.symm s)

/-- A square on a generator puts every original return element in the same
standard subgroup. No injectivity of this action is needed. -/
theorem canonicalReturn_mem (e : H ≃* S) (rho : R →* MulAut H)
    (P : Subgroup (MulAut S)) (generator : R)
    (generator_top : Subgroup.zpowers generator = ⊤) (standardGenerator : P)
    (value : ∀ x, e (rho generator x) = (standardGenerator : MulAut S) (e x))
    (r : R) : canonicalReturn e rho r ∈ P := by
  have hr : r ∈ Subgroup.zpowers generator := by
    rw [generator_top]
    exact Subgroup.mem_top r
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hr
  rw [map_zpow, canonicalReturn_generator e rho P generator standardGenerator value]
  exact P.zpow_mem standardGenerator.property n

/-- Restrict the computed return homomorphism to the full standard actor. -/
def returnToStandard (e : H ≃* S) (rho : R →* MulAut H)
    (P : Subgroup (MulAut S)) (generator : R)
    (generator_top : Subgroup.zpowers generator = ⊤) (standardGenerator : P)
    (value : ∀ x, e (rho generator x) = (standardGenerator : MulAut S) (e x)) :
    R →* P where
  toFun r := ⟨canonicalReturn e rho r,
    canonicalReturn_mem e rho P generator generator_top standardGenerator value r⟩
  map_one' := Subtype.ext (map_one (canonicalReturn e rho))
  map_mul' r s := Subtype.ext (map_mul (canonicalReturn e rho) r s)

@[simp] theorem returnToStandard_value (e : H ≃* S) (rho : R →* MulAut H)
    (P : Subgroup (MulAut S)) (generator : R)
    (generator_top : Subgroup.zpowers generator = ⊤) (standardGenerator : P)
    (value : ∀ x, e (rho generator x) = (standardGenerator : MulAut S) (e x))
    (r : R) :
    (returnToStandard e rho P generator generator_top standardGenerator value r : MulAut S) =
      canonicalReturn e rho r := rfl

/-- Exact conjugacy supplies the inner-comparison witness 1 internally. -/
theorem canonicalReturn_inner_comparison (e : H ≃* S) (rho : R →* MulAut H)
    (generator : R) :
    ∃ s : S, MulAut.congr e (rho generator) =
      MulAut.conj s * canonicalReturn e rho generator := by
  refine ⟨1, ?_⟩
  rw [map_one, one_mul]
  rfl

end ReturnHom

section StandardBase

variable {H S M Q J R k K : Type}
variable [Group H] [Finite H] [Group S] [Finite S]
variable [Group M] [Group Q] [Group J] [Group R]
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]

/-- The standard-factor statement at one specified character only. The
standard actor is a subgroup of the actual automorphism group of S. -/
def StandardSelectorAt (iotaS : PrimeRegularRootEmbedding 2 k K S)
    (diagonal : Q →* MulAut S) (P : Subgroup (MulAut S)) (base : IBr iotaS) : Prop :=
  letI := rightAutomorphismAction iotaS diagonal
  letI := rightAutomorphismAction iotaS P.subtype
  ∃ psi : IBr iotaS, psi ∈ MulAction.orbit Q base ∧
    ProductStabilizerFactorization (D := Q) (E := P) psi

/-- The published all-character type-A/B2 selector can be applied at this base. -/
theorem standardSelectorAt_of_all (iotaS : PrimeRegularRootEmbedding 2 k K S)
    (diagonal : Q →* MulAut S) (P : Subgroup (MulAut S))
    (source : StandardFactorSelector iotaS diagonal P.subtype) (base : IBr iotaS) :
    StandardSelectorAt iotaS diagonal P base := source base

/-- A field-fixed base selects itself. This adapter does not discard a
principal-support guard required to obtain the fixation premise. -/
theorem standardSelectorAt_of_fixed (iotaS : PrimeRegularRootEmbedding 2 k K S)
    (diagonal : Q →* MulAut S) (P : Subgroup (MulAut S)) (base : IBr iotaS)
    (fixed : ∀ p : P,
      IrreducibleBrauerCharacter.twist iotaS base (p : MulAut S) = base) :
    StandardSelectorAt iotaS diagonal P base := by
  letI := rightAutomorphismAction iotaS diagonal
  letI := rightAutomorphismAction iotaS P.subtype
  refine ⟨base, ⟨1, one_smul Q base⟩, ?_⟩
  intro d p
  have hp : p • base = base := by
    change IrreducibleBrauerCharacter.twist iotaS base (P.subtype p⁻¹) = base
    exact fixed p⁻¹
  constructor
  · intro h
    exact ⟨by simpa only [hp] using h, hp⟩
  · rintro ⟨hd, _⟩
    rw [hp, hd]

/-- Pull the standard factor statement back to the SAME original return group. -/
theorem standardSelectorAt_pullback (iotaS : PrimeRegularRootEmbedding 2 k K S)
    (diagonal : Q →* MulAut S) (e : H ≃* S) (rho : R →* MulAut H)
    (P : Subgroup (MulAut S)) (generator : R)
    (generator_top : Subgroup.zpowers generator = ⊤) (standardGenerator : P)
    (value : ∀ x, e (rho generator x) = (standardGenerator : MulAut S) (e x))
    (base : IBr iotaS) (source : StandardSelectorAt iotaS diagonal P base) :
    letI := rightAutomorphismAction iotaS diagonal
    letI := rightAutomorphismAction iotaS (canonicalReturn e rho)
    ∃ psi : IBr iotaS, psi ∈ MulAction.orbit Q base ∧
      ProductStabilizerFactorization (D := Q) (E := R) psi := by
  letI := rightAutomorphismAction iotaS diagonal
  letI := rightAutomorphismAction iotaS P.subtype
  letI := rightAutomorphismAction iotaS (canonicalReturn e rho)
  let f := returnToStandard e rho P generator generator_top standardGenerator value
  have action (r : R) (psi : IBr iotaS) : r • psi = f r • psi := by
    change IrreducibleBrauerCharacter.twist iotaS psi (canonicalReturn e rho r⁻¹) =
      IrreducibleBrauerCharacter.twist iotaS psi (canonicalReturn e rho r)⁻¹
    rw [map_inv]
  obtain ⟨psi, horbit, hfactor⟩ := source
  refine ⟨psi, horbit, ?_⟩
  intro d r
  simpa only [← action r psi] using hfactor d (f r)

/-- Transfer a standard selector at the canonical image of the actual base.
The return homomorphism and its inner-comparison proof are constructed here. -/
theorem actual_factor_selector_at
    (iota : PrimeRegularRootEmbedding 2 k K H) (e : H ≃* S)
    (actualDiagonal : M →* MulAut H) (standardDiagonal : Q →* MulAut S)
    (adjoint : CommonAdjointData (J := J) e actualDiagonal standardDiagonal)
    (rho : R →* MulAut H) (generator : R)
    (generator_top : Subgroup.zpowers generator = ⊤)
    (P : Subgroup (MulAut S)) (standardGenerator : P)
    (value : ∀ x, e (rho generator x) = (standardGenerator : MulAut S) (e x))
    (base : IBr iota)
    (source : StandardSelectorAt (iota.alongMulEquiv e) standardDiagonal P
      (IrreducibleBrauerCharacter.equivAlongMulEquiv iota e base)) :
    letI := rightAutomorphismAction iota actualDiagonal.range.subtype
    letI := rightAutomorphismAction iota rho
    ∃ psi : IBr iota, psi ∈ MulAction.orbit actualDiagonal.range base ∧
      ProductStabilizerFactorization (D := actualDiagonal.range) (E := R) psi := by
  letI := rightAutomorphismAction iota actualDiagonal.range.subtype
  letI := rightAutomorphismAction iota rho
  letI := rightAutomorphismAction (iota.alongMulEquiv e) standardDiagonal
  letI := rightAutomorphismAction (iota.alongMulEquiv e) (canonicalReturn e rho)
  let beta := IrreducibleBrauerCharacter.equivAlongMulEquiv iota e
  obtain ⟨chi, hchi, hfactor⟩ := standardSelectorAt_pullback
    (iota.alongMulEquiv e) standardDiagonal e rho P generator generator_top
    standardGenerator value (beta base) source
  refine ⟨beta.symm chi, ?_, ?_⟩
  · apply (character_orbit_iff iota adjoint base (beta.symm chi)).mp
    simpa only [beta, Equiv.apply_symm_apply] using hchi
  · apply product_factorization_transport iota adjoint rho (canonicalReturn e rho)
      generator generator_top (canonicalReturn_inner_comparison e rho generator) (beta.symm chi)
    simpa only [beta, Equiv.apply_symm_apply] using hfactor

end StandardBase

section ActualSelection

variable {A : Type} [Group A] {Frob : MulAut A} {Lbar : Subgroup A}
variable [Finite (fixedPoints Frob.toMonoidHom)]
variable {E : Type} [Group E] [Finite E] [IsCyclic E]
variable {C : Type} [Fintype C] {m : C → ℕ}
variable {leviStable : Lbar.map Frob.toMonoidHom = Lbar}
variable {k K : Type} [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]

/-- Lower model data only. The full standard field/graph subgroup and its
specified power require specified authentication; no character is selected. -/
structure ModelData {geometry : PrimalData Frob Lbar leviStable m}
    {field : FieldData Frob Lbar E}
    {root : PrimeRegularRootEmbedding 2 k K (L0 Frob.toMonoidHom Lbar)}
    {theta0 : IBr (rootN Frob Lbar root)}
    (presentation : Presentation geometry field root theta0)
    (S Q J : C → Type) [∀ c, Group (S c)] [∀ c, Finite (S c)]
    [∀ c, Group (Q c)] [∀ c, Group (J c)] where
  identification : ∀ c, Base m geometry.factor c ≃* S c
  standardDiagonal : ∀ c, Q c →* MulAut (S c)
  adjoint : ∀ c, CommonAdjointData (J := J c) (identification c)
    (geometry.actualDiagonal (first m c)) (standardDiagonal c)
  fieldGraph : ∀ c, Subgroup (MulAut (S c))
  standardGenerator : ∀ c, fieldGraph c
  generator_value : ∀ c (x : Base m geometry.factor c),
    identification c (presentation.localH c (presentation.localGenerator c) x) =
      (standardGenerator c : MulAut (S c)) (identification c x)

namespace ModelData

variable {geometry : PrimalData Frob Lbar leviStable m}
variable {field : FieldData Frob Lbar E}
variable {root : PrimeRegularRootEmbedding 2 k K (L0 Frob.toMonoidHom Lbar)}
variable {theta0 : IBr (rootN Frob Lbar root)}
variable {presentation : Presentation geometry field root theta0}
variable {S Q J : C → Type} [∀ c, Group (S c)] [∀ c, Finite (S c)]
variable [∀ c, Group (Q c)] [∀ c, Group (J c)]
variable (model : ModelData presentation S Q J)

abbrev standardRoot (c : C) :=
  (presentation.factorRoot c).alongMulEquiv (model.identification c)

abbrev standardBase (c : C) : IBr (model.standardRoot c) :=
  IrreducibleBrauerCharacter.equivAlongMulEquiv (presentation.factorRoot c)
    (model.identification c) (presentation.localBase c)

abbrev standardReturn (c : C) : presentation.ReturnGroup c →* MulAut (S c) :=
  canonicalReturn (model.identification c) (presentation.localH c)

def standardActorHom (c : C) : presentation.ReturnGroup c →* model.fieldGraph c :=
  returnToStandard (model.identification c) (presentation.localH c)
    (model.fieldGraph c) (presentation.localGenerator c)
    (presentation.localGenerator_generates c) (model.standardGenerator c)
    (model.generator_value c)

@[simp] theorem standardActorHom_value (c : C) (r : presentation.ReturnGroup c) :
    (model.standardActorHom c r : MulAut (S c)) = model.standardReturn c r := rfl

/-- The positive return in this presentation is the inverse of its raw wrap:
the presentation's monomial action is that of tau inverse. -/
theorem positiveGenerator_eq_inverse_fullReturn (c : C) :
    presentation.localH c (presentation.localGenerator c) =
      (fullReturn m geometry.factor presentation.SH c)⁻¹ :=
  TypeBComponentReturnRestriction.returnAction_generator m geometry.factor presentation.SH
    ((geometry.productField field).comp
      (geometry.orbitStabilizer root field theta0).subtype)
    presentation.tau presentation.hH c

end ModelData

/-- Combine the same literal N representative from standard selectors at
exactly the prescribed local bases, retaining the original return groups. -/
theorem selected_constituent
    (geometry : PrimalData Frob Lbar leviStable m)
    (field : FieldData Frob Lbar E)
    (root : PrimeRegularRootEmbedding 2 k K (L0 Frob.toMonoidHom Lbar))
    (theta0 : IBr (rootN Frob Lbar root))
    (presentation : Presentation geometry field root theta0)
    (S Q J : C → Type) [∀ c, Group (S c)] [∀ c, Finite (S c)]
    [∀ c, Group (Q c)] [∀ c, Group (J c)]
    (model : ModelData presentation S Q J)
    (selectors : ∀ c, StandardSelectorAt (model.standardRoot c)
      (model.standardDiagonal c) (model.fieldGraph c) (model.standardBase c)) :
    let _ := ambientBrauerAction (N Frob Lbar) (rootN Frob Lbar root)
    let EO := TypeBLeviRepresentativeComponents.actualOrbitStabilizer (N Frob Lbar)
      (rootN Frob Lbar root) field.fieldOnGamma field.N_stable theta0
    let fieldO := field.fieldOnGamma.comp EO.subtype
    let stableO := fun a : EO ↦ field.N_stable a.1
    let _ := fieldBrauerAction (N Frob Lbar) (rootN Frob Lbar root) fieldO stableO
    ∃ theta : IBr (rootN Frob Lbar root),
      theta ∈ MulAction.orbit (Gamma Frob Lbar) theta0 ∧
      (∀ a : EO, a • theta = theta) ∧
      SemidirectStabilizerFactors fieldO
        (field_ambient_semidirect_compatible (N Frob Lbar) (rootN Frob Lbar root)
          fieldO stableO) theta := by
  classical
  have selected : ∀ c,
      let _ := rightAutomorphismAction (presentation.factorRoot c)
        (geometry.diagonalAction (first m c))
      let _ := rightAutomorphismAction (presentation.factorRoot c) (presentation.localH c)
      ∃ psi : IBr (presentation.factorRoot c),
        psi ∈ MulAction.orbit (geometry.diagonalGroup (first m c)) (presentation.localBase c) ∧
        ProductStabilizerFactorization (D := geometry.diagonalGroup (first m c))
          (E := presentation.ReturnGroup c) psi := by
    intro c
    exact actual_factor_selector_at (presentation.factorRoot c) (model.identification c)
      (geometry.actualDiagonal (first m c)) (model.standardDiagonal c) (model.adjoint c)
      (presentation.localH c) (presentation.localGenerator c)
      (presentation.localGenerator_generates c) (model.fieldGraph c)
      (model.standardGenerator c) (model.generator_value c) (presentation.localBase c)
      (selectors c)
  choose representative representative_orbit representative_factorization using selected
  have local_factorisation : ∀ c,
      let _ := rightAutomorphismAction (presentation.factorRoot c)
        (geometry.diagonalAction (first m c))
      let _ := rightAutomorphismAction (presentation.factorRoot c) (presentation.localH c)
      SemidirectStabilizerFactors (presentation.localD c) (presentation.localCompatible c)
        (representative c) := by
    intro c
    letI := rightAutomorphismAction (presentation.factorRoot c)
      (geometry.diagonalAction (first m c))
    letI := rightAutomorphismAction (presentation.factorRoot c) (presentation.localH c)
    exact (semidirectStabilizerFactors_iff_productStabilizerFactorization
      (presentation.localD c) (presentation.localCompatible c) (representative c)).mpr
      (representative_factorization c)
  exact TypeBLeviRepresentativeComponents.exists_actual_fixed_constituent
    (N Frob Lbar) (rootN Frob Lbar root) field.fieldOnGamma field.N_stable
    m geometry.factor geometry.diagonalGroup geometry.componentProduct geometry.diagonalAction
    geometry.imageProduct geometry.imageProduct_surjective geometry.groupSquare
    presentation.SH presentation.SD presentation.pairs presentation.factorRoot presentation.productSource
    presentation.phi presentation.normalises theta0 presentation.tau presentation.hH presentation.hD
    presentation.tau_generates representative representative_orbit local_factorisation

end ActualSelection

end ModularRep.PaperProofs.TypeBLeviReturnPowerSelection


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
