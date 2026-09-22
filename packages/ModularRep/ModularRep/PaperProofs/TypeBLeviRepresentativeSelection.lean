import ModularRep.PaperProofs.TypeBLeviRepresentativeGeometry
import ModularRep.PaperProofs.TypeBLeviRepresentativeComponents
import ModularRep.PaperProofs.TypeBLeviRepresentativeFactorSelector

/-!
# Selection from the primal Levi geometry and standard factor sources

The regular-Levi product map, its surjectivity and its conjugation square
are computed from the same primal component data and central Lang source.
The finite field actor is the restriction constructed by Carriers from the
specified point endomorphism. The only selector source is on each standard
S/Q factor with its original return group. Common adjoint point projections
and a generator inner-difference equation transfer it to the actual factor.
The resulting local representatives are then combined by TypeBLeviRepresentativeComponents.

The geometric Frobenius cycle lengths are independent of the field-return
cycle lengths m. No arbitrary-index conversion or actual-factor selector is
assumed. Algebraic component/field data remain E1/U; central Lang is E2/U;
the standard type-A/B2 selector retains its exact E2/U scope.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBLeviRepresentativeSelection

open Formalisation
open TypeBRegularLeviRationalCarriers TypeBRegularLeviComponentPointSource
open TypeBComponentCycleNormalization TypeBRegularLeviCharacterActionAdapter
open TypeBComponentReturnOriginalCarriers EvenFieldAssumption53Relative
open TypeBLemma47LeviApplication TypeBLeviRepresentativeCarriers
open TypeBLeviRepresentativeFactorSelector
open ModularRep.ManuscriptVerification.StabilizerFactorizationTransport

variable {A : Type} [Group A]

/-- Lower primal component and central data on the same actual Levi. -/
structure PrimalData (Frob : MulAut A) (Lbar : Subgroup A)
    (leviStable : Lbar.map Frob.toMonoidHom = Lbar)
    {C : Type} (m : C → ℕ) where
  geometricLength : Index m → ℕ
  components : ComponentPointData (TypeBLeviRepresentativeGeometry.pairedFrobenius Frob Lbar leviStable)
    (TypeBLeviRepresentativeGeometry.derivedInside Lbar) (TypeBLeviRepresentativeGeometry.derived_stable Frob Lbar leviStable) geometricLength
  central : ∀ b : pairedLevi Lbar,
    ∃ h : TypeBLeviRepresentativeGeometry.derivedInside Lbar, ∃ z : Subgroup.center (pairedLevi Lbar),
      b = (h : pairedLevi Lbar) * z
  lang : TypeBRegularLeviSupportedLift.CentralLangSource
    (TypeBLeviRepresentativeGeometry.pairedFrobenius Frob Lbar leviStable)

/-- The finite actor and its actual point-endomorphism interpretation. No
action on algebraic points or completed chain conclusion is a field. -/
structure FieldData (Frob : MulAut A) (Lbar : Subgroup A)
    [Finite (fixedPoints Frob.toMonoidHom)] (E : Type) [Group E] where
  sigma : A →* A
  injective : Function.Injective sigma
  commutes : ∀ x, Frob (sigma x) = sigma (Frob x)
  sigma_levi : ∀ x ∈ Lbar, sigma x ∈ Lbar
  sigma_centre : ∀ z ∈ Subgroup.center A, sigma z ∈ Subgroup.center A
  fieldPoints : E →* MulAut (fixedPoints Frob.toMonoidHom)
  generator : E
  generates : Subgroup.zpowers generator = ⊤
  generatorValue : ∀ x : fixedPoints Frob.toMonoidHom,
    fieldPoints generator x = TypeBRegularLeviCurrentQuotient.fixedPointAutomorphism
      Frob.toMonoidHom sigma commutes injective x

variable {Frob : MulAut A} {Lbar : Subgroup A}
variable [Finite (fixedPoints Frob.toMonoidHom)]
variable {E : Type} [Group E]

namespace FieldData

variable (field : FieldData Frob Lbar E)

abbrev fieldOnGamma : E →* MulAut (Gamma Frob Lbar) :=
  TypeBLeviRepresentativeCarriers.fieldOnGamma Frob Lbar field.sigma field.injective
    field.commutes field.sigma_levi field.sigma_centre field.fieldPoints
    field.generator field.generates field.generatorValue

theorem H_stable (a : E) (x : Gamma Frob Lbar) :
    x ∈ TypeBLeviRepresentativeCarriers.H Frob Lbar ↔
      field.fieldOnGamma a x ∈ TypeBLeviRepresentativeCarriers.H Frob Lbar :=
  fieldOnGamma_H_stable Frob Lbar field.sigma field.injective field.commutes
    field.sigma_levi field.sigma_centre field.fieldPoints field.generator
    field.generates field.generatorValue a x

theorem N_stable (a : E) (x : Gamma Frob Lbar) :
    x ∈ N Frob Lbar ↔ field.fieldOnGamma a x ∈ N Frob Lbar :=
  fieldOnGamma_N_stable Frob Lbar field.sigma field.injective field.commutes
    field.sigma_levi field.sigma_centre field.fieldPoints field.generator
    field.generates field.generatorValue a x

end FieldData

variable {C : Type} [Fintype C] {m : C → ℕ}
variable {leviStable : Lbar.map Frob.toMonoidHom = Lbar}

namespace PrimalData

variable (geometry : PrimalData Frob Lbar leviStable m)

abbrev factor (i : Index m) :=
  TypeBLeviRepresentativeGeometry.factor Frob Lbar leviStable geometry.geometricLength geometry.components i

abbrev actualDiagonal (i : Index m) :=
  TypeBRegularLeviOrbitAssembly.factorAction
    (TypeBLeviRepresentativeGeometry.pairedFrobenius Frob Lbar leviStable) (TypeBLeviRepresentativeGeometry.derivedInside Lbar)
    (TypeBLeviRepresentativeGeometry.derived_stable Frob Lbar leviStable) geometry.geometricLength
    geometry.components geometry.central i

abbrev diagonalGroup (i : Index m) : Type :=
  TypeBLeviRepresentativeGeometry.factorImage Frob Lbar leviStable geometry.geometricLength
    geometry.components geometry.central i

abbrev diagonalAction :=
  TypeBLeviRepresentativeGeometry.factorImageAction Frob Lbar leviStable geometry.geometricLength
    geometry.components geometry.central

abbrev componentProduct :=
  TypeBLeviRepresentativeGeometry.componentProduct Frob Lbar leviStable geometry.geometricLength geometry.components

abbrev imageProduct :=
  TypeBLeviRepresentativeGeometry.imageProduct Frob Lbar leviStable geometry.geometricLength
    geometry.components geometry.central

theorem imageProduct_surjective : Function.Surjective geometry.imageProduct :=
  TypeBLeviRepresentativeGeometry.imageProduct_surjective Frob Lbar leviStable geometry.geometricLength
    geometry.components geometry.central geometry.lang

theorem groupSquare (g : Gamma Frob Lbar) :
    MulAut.congr geometry.componentProduct (MulAut.conjNormal g) =
      coordinateMulAut geometry.factor geometry.diagonalGroup geometry.diagonalAction
        (geometry.imageProduct g) :=
  TypeBLeviRepresentativeGeometry.groupSquare Frob Lbar leviStable geometry.geometricLength
    geometry.components geometry.central g

variable {k K : Type} [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable (root : PrimeRegularRootEmbedding 2 k K (L0 Frob.toMonoidHom Lbar))

abbrev productRoot := TypeBLeviRepresentativeComponents.productRoot (rootN Frob Lbar root) geometry.componentProduct

abbrev productCharacter :=
  TypeBLeviRepresentativeComponents.toProductCharacter (rootN Frob Lbar root) geometry.componentProduct

abbrev productField (field : FieldData Frob Lbar E) :=
  TypeBLeviRepresentativeComponents.productField (N Frob Lbar) field.fieldOnGamma field.N_stable geometry.componentProduct

abbrev orbitStabilizer (field : FieldData Frob Lbar E)
    (theta0 : IBr (rootN Frob Lbar root)) :=
  originalStabilizer m geometry.factor geometry.diagonalGroup geometry.diagonalAction
    (geometry.productRoot root) (geometry.productField field) (geometry.productCharacter root theta0)

end PrimalData

variable [Finite E] [IsCyclic E]
variable {k K : Type} [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]

/-- Lower field-cycle presentation and the literal external-product source.
There are no selected actual characters or factorization fields. -/
structure Presentation (geometry : PrimalData Frob Lbar leviStable m)
    (field : FieldData Frob Lbar E)
    (root : PrimeRegularRootEmbedding 2 k K (L0 Frob.toMonoidHom Lbar))
    (theta0 : IBr (rootN Frob Lbar root)) where
  SH : CycleCoordinates m geometry.factor
  SD : CycleCoordinates m geometry.diagonalGroup
  pairs : PairEdges m geometry.factor geometry.diagonalGroup SH SD geometry.diagonalAction
  factorRoot : ∀ c, PrimeRegularRootEmbedding 2 k K (Base m geometry.factor c)
  productSource : TypeBFiniteProductNaturality.ExternalProductData
    (fun i : Index m ↦ Base m geometry.factor i.1)
    (normalizedRoot m geometry.factor SH (geometry.productRoot root))
    (fun i ↦ factorRoot i.1)
  phi : E →* MulAut (Original m geometry.diagonalGroup)
  normalises : AutomorphismSemidirectCompatible
    (coordinateMulAut geometry.factor geometry.diagonalGroup geometry.diagonalAction)
    (geometry.productField field) phi
  tau : geometry.orbitStabilizer root field theta0
  tau_generates : Subgroup.zpowers tau = ⊤
  hH : MonomialAction m geometry.factor SH
    (((geometry.productField field).comp
      (geometry.orbitStabilizer root field theta0).subtype) tau⁻¹)
  hD : MonomialAction m geometry.diagonalGroup SD
    ((phi.comp (geometry.orbitStabilizer root field theta0).subtype) tau⁻¹)

namespace Presentation

variable {geometry : PrimalData Frob Lbar leviStable m}
variable {field : FieldData Frob Lbar E}
variable {root : PrimeRegularRootEmbedding 2 k K (L0 Frob.toMonoidHom Lbar)}
variable {theta0 : IBr (rootN Frob Lbar root)}
variable (presentation : Presentation geometry field root theta0)

abbrev ReturnGroup (c : C) := TypeBComponentReturnRestriction.ReturnGroup m presentation.tau c

abbrev localGenerator (c : C) := TypeBComponentReturnRestriction.returnElement m presentation.tau c

theorem localGenerator_generates (c : C) :
    Subgroup.zpowers (presentation.localGenerator c) = ⊤ := by
  apply top_unique
  intro r _
  obtain ⟨n, hn⟩ := r.property
  refine ⟨n, Subtype.ext ?_⟩
  change (presentation.tau ^ (m c + 1)) ^ n = r.val
  exact hn

abbrev localH (c : C) :=
  TypeBComponentReturnRestriction.returnAction m geometry.factor presentation.SH
    ((geometry.productField field).comp (geometry.orbitStabilizer root field theta0).subtype)
    presentation.tau presentation.hH c

abbrev localD (c : C) :=
  TypeBComponentReturnRestriction.returnAction m geometry.diagonalGroup presentation.SD
    (presentation.phi.comp (geometry.orbitStabilizer root field theta0).subtype)
    presentation.tau presentation.hD c

abbrev localBase (c : C) :=
  presentation.productSource.characters
    (characterEquiv m geometry.factor presentation.SH (geometry.productRoot root)
      (geometry.productCharacter root theta0)) (first m c)

theorem localCompatible (c : C) :
    let _ := rightAutomorphismAction (presentation.factorRoot c) (geometry.diagonalAction (first m c))
    let _ := rightAutomorphismAction (presentation.factorRoot c) (presentation.localH c)
    SemidirectActionCompatible (X := IBr (presentation.factorRoot c)) (presentation.localD c) :=
  brauerRightActions_semidirectCompatible (presentation.factorRoot c)
    (geometry.diagonalAction (first m c)) (presentation.localH c) (presentation.localD c)
    (TypeBComponentReturnRestriction.return_actions_compatible m geometry.factor geometry.diagonalGroup
      presentation.SH presentation.SD geometry.diagonalAction
      ((geometry.productField field).comp (geometry.orbitStabilizer root field theta0).subtype)
      (presentation.phi.comp (geometry.orbitStabilizer root field theta0).subtype)
      presentation.tau presentation.hH presentation.hD (fun a d ↦ presentation.normalises a.1 d) c)

end Presentation

/-- The published selector is only on S/Q and the original return group.
Actual image/orbit equality and actual selector factorization are derived. -/
structure StandardData {geometry : PrimalData Frob Lbar leviStable m}
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
  standardReturn : ∀ c, presentation.ReturnGroup c →* MulAut (S c)
  generator_difference : ∀ c, ∃ s : S c,
    MulAut.congr (identification c) (presentation.localH c (presentation.localGenerator c)) =
      MulAut.conj s * standardReturn c (presentation.localGenerator c)
  selector : ∀ c, StandardFactorSelector
    ((presentation.factorRoot c).alongMulEquiv (identification c))
    (standardDiagonal c) (standardReturn c)

/-- Construct the actual N representative from specified primal geometry
and the standard factor selectors, deriving all internal q/action inputs. -/
theorem selected_constituent
    (geometry : PrimalData Frob Lbar leviStable m)
    (field : FieldData Frob Lbar E)
    (root : PrimeRegularRootEmbedding 2 k K (L0 Frob.toMonoidHom Lbar))
    (theta0 : IBr (rootN Frob Lbar root))
    (presentation : Presentation geometry field root theta0)
    (S Q J : C → Type) [∀ c, Group (S c)] [∀ c, Finite (S c)]
    [∀ c, Group (Q c)] [∀ c, Group (J c)]
    (standard : StandardData presentation S Q J) :
    let _ := ambientBrauerAction (N Frob Lbar) (rootN Frob Lbar root)
    let EO := TypeBLeviRepresentativeComponents.actualOrbitStabilizer (N Frob Lbar) (rootN Frob Lbar root)
      field.fieldOnGamma field.N_stable theta0
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
      let _ := rightAutomorphismAction (presentation.factorRoot c) (geometry.diagonalAction (first m c))
      let _ := rightAutomorphismAction (presentation.factorRoot c) (presentation.localH c)
      ∃ psi : IBr (presentation.factorRoot c),
        psi ∈ MulAction.orbit (geometry.diagonalGroup (first m c)) (presentation.localBase c) ∧
        ProductStabilizerFactorization (D := geometry.diagonalGroup (first m c))
          (E := presentation.ReturnGroup c) psi := by
    intro c
    exact actual_factor_selector (presentation.factorRoot c) (standard.adjoint c)
      (presentation.localH c) (standard.standardReturn c) (presentation.localGenerator c)
      (presentation.localGenerator_generates c) (standard.generator_difference c)
      (standard.selector c) (presentation.localBase c)
  choose representative representative_orbit representative_factorization using selected
  have local_factorisation : ∀ c,
      let _ := rightAutomorphismAction (presentation.factorRoot c) (geometry.diagonalAction (first m c))
      let _ := rightAutomorphismAction (presentation.factorRoot c) (presentation.localH c)
      SemidirectStabilizerFactors (presentation.localD c) (presentation.localCompatible c)
        (representative c) := by
    intro c
    letI := rightAutomorphismAction (presentation.factorRoot c) (geometry.diagonalAction (first m c))
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

end ModularRep.PaperProofs.TypeBLeviRepresentativeSelection


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
