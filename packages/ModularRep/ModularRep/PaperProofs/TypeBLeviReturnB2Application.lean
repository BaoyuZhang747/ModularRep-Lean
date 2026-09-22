import ModularRep.PaperProofs.TypeBLeviReturnB2Coefficient
import ModularRep.PaperProofs.TypeBLeviReturnB2Diagonal
import ModularRep.PaperProofs.TypeBLeviReturnSpinPrincipalSelection

/-!
# The prescribed B2 constituent on the original return carrier

The coefficient model, common Frobenius, original component and one Lang
solution determine the finite identification.  The actual diagonal source is
only a projection to the literal projective conformal group with its point
conjugation square.  No lift to the conformal group, projection surjectivity,
character selector or original stabilizer conclusion is an input.

The sole character source is the fixed standard Sp4 instance of FM2022,
Corollary 4.6.  The same original localBase is the identity orbit representative.
The component/root/field and regular-adjoint interpretation remains the
explicit E1/E2/U boundary of the B2 source interface.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBLeviReturnB2Application

open Formalisation
open TypeBRegularLeviRationalCarriers TypeBRegularLeviComponentPointSource
open TypeBComponentCycleNormalization TypeBRegularLeviComponentFixedPoints
open TypeBRegularLeviProductProjection TypeBRegularLeviSupportedLift
open TypeBRegularLeviCharacterActionAdapter TypeBComponentReturnCarrierTransport
open TypeBLeviRepresentativeCarriers TypeBLeviRepresentativeSelection
open TypeBLeviReturnSpinOriginalCarrier TypeBLeviReturnSpinOriginalReturn
open TypeBLeviReturnSpinPrincipalSelection TypeBLeviReturnPowerSelection
open TypeBLeviReturnPowerModel TypeBLeviReturnPowerAutomorphism
open TypeBRankThreeFactorsRationalForms TypeBLeviReturnB2Coefficient
open EvenFieldAssumption53Relative
open ModularRep.ManuscriptVerification.StabilizerFactorizationTransport

private theorem component_conjugation {B I : Type} [Group B]
    (H : Subgroup B) (V : I → Subgroup H) [DecidableEq I]
    (coordinates : H ≃* (∀ i, V i))
    (inclusion : ∀ i (x : V i), coordinates.symm (Function.update 1 i x) = (x : H))
    (h : H) (i : I) (x : V i) :
    (h : B) * ((x : H) : B) * (h : B)⁻¹ =
      (((coordinates h i * x * (coordinates h i)⁻¹ : V i) : H) : B) := by
  have coordinate (j : I) (y : V j) :
      coordinates (y : H) = Function.update (1 : ∀ i, V i) j y := by
    exact (congrArg coordinates (inclusion j y)).symm.trans
      (coordinates.apply_symm_apply _)
  have equality : h * (x : H) * h⁻¹ =
      (coordinates h i * x * (coordinates h i)⁻¹ : V i) := by
    apply coordinates.injective
    rw [map_mul, map_mul, map_inv, coordinate i x,
      coordinate i (coordinates h i * x * (coordinates h i)⁻¹)]
    funext j
    by_cases hji : j = i
    · subst j
      simp only [Pi.mul_apply, Pi.inv_apply, Function.update_self]
    · simp only [Pi.mul_apply, Pi.inv_apply, Function.update_of_ne hji,
        Pi.one_apply, mul_one, mul_inv_cancel]
  exact congrArg H.subtype equality

/-- The first geometric component has the same ambient conjugation value.
The full rational-cycle embedding is not substituted for this component. -/
private theorem factorAction_component_value {B I : Type} [Group B]
    (F : B →* B) (H : Subgroup B) (hH : ∀ h ∈ H, F h ∈ H)
    (lengths : I → ℕ) (data : ComponentPointData F H hH lengths)
    (central : ∀ b : B, ∃ h : H, ∃ z : Subgroup.center B, b = (h : B) * z)
    (i : I) (b : fixedPoints F) (x : rationalFactor F H hH lengths data i) :
    (((TypeBRegularLeviOrbitAssembly.factorAction F H hH lengths data central i b x).val
      : H) : B) = (b : B) * ((x.val : H) : B) * (b : B)⁻¹ := by
  classical
  letI : DecidableEq (Index lengths) :=
    TypeBRegularLeviComponentPointSource.instDecidableEqIndex lengths
  obtain ⟨h, z, hb⟩ := central (b : B)
  let V := componentGroup F H hH lengths data
  have coordinate := TypeBRegularLeviRationalAction.productConjugation_coordinate
    F H hH lengths V data.cycles data.frobenius data.monomial
    data.coordinates data.frobenius_value central b h z hb
    (singleFactor lengths V data.cycles i x) i
  have single_self : singleFactor lengths V data.cycles i x i = x := by
    change Function.update (1 : ∀ d, Factor lengths V data.cycles d) i x i = x
    exact Function.update_self (β := fun d => ↥(Factor lengths V data.cycles d)) i x 1
  have value :
      (TypeBRegularLeviOrbitAssembly.factorAction F H hH lengths data central i b x).val =
        data.coordinates h (first lengths i) * x.val *
          (data.coordinates h (first lengths i))⁻¹ := by
    change (TypeBRegularLeviRationalAction.productConjugation F H hH lengths V
      data.cycles data.frobenius data.monomial data.coordinates data.frobenius_value
      central b (singleFactor lengths V data.cycles i x) i).val = _
    simpa only [single_self] using coordinate
  calc
    _ = (((data.coordinates h (first lengths i) * x.val *
        (data.coordinates h (first lengths i))⁻¹ : data.component (first lengths i))
        : H) : B) := congrArg (fun y : data.component (first lengths i) ↦ ((y : H) : B)) value
    _ = (h : B) * ((x.val : H) : B) * (h : B)⁻¹ :=
      (component_conjugation H data.component data.coordinates data.inclusion
        h (first lengths i) x.val).symm
    _ = (b : B) * ((x.val : H) : B) * (b : B)⁻¹ := by
      rw [hb, conjugation_mul_central]

variable {A : Type} [Group A] {Frob : MulAut A} {Lbar : Subgroup A}
variable [Finite (fixedPoints Frob.toMonoidHom)]
variable {E : Type} [Group E] [Finite E] [IsCyclic E]
variable {C : Type} [Fintype C] {m : C → ℕ}
variable {leviStable : Lbar.map Frob.toMonoidHom = Lbar}
variable {k K : Type} [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable {geometry : PrimalData Frob Lbar leviStable m}
variable {field : FieldData Frob Lbar E}
variable {root : PrimeRegularRootEmbedding 2 k K (L0 Frob.toMonoidHom Lbar)}
variable {theta0 : IBr (rootN Frob Lbar root)}

/-- Primitive point data for the specified B2 component.  The common matrix
Frobenius and the finite equivalence are computed, rather than source fields. -/
structure B2Realization (presentation : Presentation geometry field root theta0) (c : C)
    (p f : ℕ) (FQ Astd : Type) [Field FQ] [Finite FQ] [Field Astd]
    [Algebra FQ Astd] [Fact p.Prime] [CharP FQ p] [CharP Astd p] where
  cycle : OriginalCycleData presentation c
  primeStep : ℕ
  cardinality : Nat.card FQ = p ^ f
  finite_exponent : f = (primeStep * cycle.u) * cycle.s
  scalarDescent : ∀ x : Astd, x ^ (p ^ f) = x → ∃ y : FQ, algebraMap FQ Astd y = x
  embedding : Sp4 Astd →* pairedLevi Lbar
  injective : Function.Injective embedding
  range : embedding.range = originalComponent Frob Lbar leviStable m geometry c
  twist : Sp4 Astd
  generator_value : ∀ x, (cycle.points.F0 ^ cycle.u) (embedding x) =
    embedding (twist * commonFrobenius Astd p (primeStep * cycle.u) x * twist⁻¹)
  lang : ∃ a : Sp4 Astd,
    commonFrobenius Astd p (primeStep * cycle.u) a * a⁻¹ = twist⁻¹

namespace B2Realization

variable {presentation : Presentation geometry field root theta0} {c : C}
variable {p f : ℕ} {FQ Astd : Type} [Field FQ] [Finite FQ] [Field Astd]
variable [Algebra FQ Astd] [Fact p.Prime] [CharP FQ p] [CharP Astd p]
variable (real : B2Realization presentation c p f FQ Astd)

abbrev common := commonFrobenius Astd p (real.primeStep * real.cycle.u)

theorem definingPower_pos : 0 < real.cycle.s := by
  apply Nat.pos_of_ne_zero
  intro hs
  have exponent : f = 0 := by simpa only [hs, Nat.mul_zero] using real.finite_exponent
  have card : Nat.card FQ = 1 := by simpa only [exponent, pow_zero] using real.cardinality
  have nontrivial : 1 < Nat.card FQ := Finite.one_lt_card
  rw [card] at nontrivial
  exact (Nat.lt_irrefl 1) nontrivial

/-- Both fixed-point identifications use the same coefficient map and Lang point. -/
def standardToRational : Sp4 FQ ≃*
    rationalSubgroup
      (pairedFrobeniusEnd Frob Lbar leviStable ^
        (geometry.geometricLength (first m c) + 1))
      (originalComponent Frob Lbar leviStable m geometry c) :=
  (coefficientEquiv FQ Astd p (real.primeStep * real.cycle.u) f real.cycle.s
    real.cardinality real.finite_exponent real.scalarDescent).trans
  (normalizedFixedEquiv real.embedding
    (originalComponent Frob Lbar leviStable m geometry c) real.injective real.range
    real.cycle.points.F0 (pairedFrobeniusEnd Frob Lbar leviStable) real.common
    real.cycle.h real.cycle.u (geometry.geometricLength (first m c) + 1) real.cycle.s
    real.cycle.defining real.cycle.fixed_exponent real.twist real.generator_value
    real.lang.choose real.lang.choose_spec)

def identification : Base m geometry.factor c ≃* Sp4 FQ :=
  (originalBaseEquivRational Frob Lbar leviStable m geometry c).trans
    real.standardToRational.symm

theorem standardToRational_value (x : Sp4 FQ) :
    (real.standardToRational x).val.val =
      adjustedEmbedding real.embedding real.lang.choose (coefficientMap FQ Astd x) := by
  exact (normalizedFixedEquiv_value real.embedding
    (originalComponent Frob Lbar leviStable m geometry c) real.injective real.range
    real.cycle.points.F0 (pairedFrobeniusEnd Frob Lbar leviStable) real.common
    real.cycle.h real.cycle.u (geometry.geometricLength (first m c) + 1) real.cycle.s
    real.cycle.defining real.cycle.fixed_exponent real.twist real.generator_value
    real.lang.choose real.lang.choose_spec
    (coefficientEquiv FQ Astd p (real.primeStep * real.cycle.u) f real.cycle.s
      real.cardinality real.finite_exponent real.scalarDescent x)).trans
    (congrArg (adjustedEmbedding real.embedding real.lang.choose)
      (coefficientEquiv_value FQ Astd p (real.primeStep * real.cycle.u) f real.cycle.s
        real.cardinality real.finite_exponent real.scalarDescent x))

theorem identification_value (x : Base m geometry.factor c) :
    adjustedEmbedding real.embedding real.lang.choose
      (coefficientMap FQ Astd (real.identification x)) =
        (originalBaseEquivRational Frob Lbar leviStable m geometry c x).val.val := by
  rw [← real.standardToRational_value]
  change (real.standardToRational (real.standardToRational.symm
    (originalBaseEquivRational Frob Lbar leviStable m geometry c x))).val.val = _
  rw [real.standardToRational.apply_symm_apply]

/-- The positive original return is the computed standard field power. -/
theorem localGenerator_value (x : Base m geometry.factor c) :
    real.identification (presentation.localH c (presentation.localGenerator c) x) =
      (fieldGenerator FQ p ^ ((real.primeStep * real.cycle.u) * real.cycle.r))
        (real.identification x) := by
  let nu := originalBaseEquivRational Frob Lbar leviStable m geometry c
  let eS := real.standardToRational
  let ec := coefficientEquiv FQ Astd p (real.primeStep * real.cycle.u) f real.cycle.s
    real.cardinality real.finite_exponent real.scalarDescent
  let en := normalizedFixedEquiv real.embedding
    (originalComponent Frob Lbar leviStable m geometry c) real.injective real.range
    real.cycle.points.F0 (pairedFrobeniusEnd Frob Lbar leviStable) real.common
    real.cycle.h real.cycle.u (geometry.geometricLength (first m c) + 1) real.cycle.s
    real.cycle.defining real.cycle.fixed_exponent real.twist real.generator_value
    real.lang.choose real.lang.choose_spec
  let actual := MulAut.congr nu (presentation.localH c (presentation.localGenerator c))
  have value (z : rationalSubgroup
      (pairedFrobeniusEnd Frob Lbar leviStable ^
        (geometry.geometricLength (first m c) + 1))
      (originalComponent Frob Lbar leviStable m geometry c)) :
      (actual z).val.val =
        (pairedFrobeniusEnd Frob Lbar leviStable ^ real.cycle.q)
          ((real.cycle.points.F0 ^ (real.cycle.a * (m c + 1))) z.val.val) := by
    obtain ⟨y, rfl⟩ := nu.surjective z
    change (nu (presentation.localH c (presentation.localGenerator c)
      (nu.symm (nu y)))).val.val = _
    rw [nu.symm_apply_apply]
    exact original_positive_return_value geometry field real.cycle.points presentation c
      real.cycle.a real.cycle.h real.cycle.u real.cycle.q real.cycle.r
      real.cycle.tau_value real.cycle.defining real.cycle.return_exponent real.cycle.period y
  have square := normalizedFixedEquiv_return_square real.embedding
    (originalComponent Frob Lbar leviStable m geometry c) real.injective real.range
    real.cycle.points.F0 (pairedFrobeniusEnd Frob Lbar leviStable) real.common
    real.cycle.h real.cycle.u (geometry.geometricLength (first m c) + 1) real.cycle.s
    real.cycle.defining real.cycle.fixed_exponent real.twist real.generator_value
    real.lang.choose real.lang.choose_spec
    (real.cycle.a * (m c + 1)) real.cycle.q real.cycle.r real.cycle.return_exponent
    real.definingPower_pos actual value (ec (real.identification x))
  have coefficients := coefficientEquiv_field_power FQ Astd p
    (real.primeStep * real.cycle.u) f real.cycle.s real.cardinality
    real.finite_exponent real.scalarDescent real.cycle.r real.definingPower_pos
    (real.identification x)
  change ec ((fieldGenerator FQ p ^ ((real.primeStep * real.cycle.u) * real.cycle.r))
    (real.identification x)) = fixedPowerAut real.common real.cycle.r real.cycle.s
      real.definingPower_pos (ec (real.identification x)) at coefficients
  change actual (en (ec (real.identification x))) =
    en (fixedPowerAut real.common real.cycle.r real.cycle.s
      real.definingPower_pos (ec (real.identification x))) at square
  rw [← coefficients] at square
  change actual (eS (real.identification x)) =
    eS ((fieldGenerator FQ p ^ ((real.primeStep * real.cycle.u) * real.cycle.r))
      (real.identification x)) at square
  apply eS.injective
  change eS (eS.symm (nu (presentation.localH c (presentation.localGenerator c) x))) = _
  rw [eS.apply_symm_apply]
  change nu (presentation.localH c (presentation.localGenerator c)
    (nu.symm (eS (eS.symm (nu x))))) = _ at square
  rw [eS.apply_symm_apply, nu.symm_apply_apply] at square
  exact square

/-- Codomain restriction preserves the complete original cyclic return group. -/
def returnToField : presentation.ReturnGroup c →*
    Subgroup.zpowers (fieldGenerator FQ p) :=
  returnToStandard real.identification (presentation.localH c)
    (Subgroup.zpowers (fieldGenerator FQ p)) (presentation.localGenerator c)
    (presentation.localGenerator_generates c)
    ⟨fieldGenerator FQ p ^ ((real.primeStep * real.cycle.u) * real.cycle.r),
      Subgroup.npow_mem_zpowers _ _⟩ real.localGenerator_value

@[simp] theorem returnToField_value (r0 : presentation.ReturnGroup c) :
    (real.returnToField r0 : MulAut (Sp4 FQ)) =
      canonicalReturn real.identification (presentation.localH c) r0 := rfl

abbrev standardRoot := (presentation.factorRoot c).alongMulEquiv real.identification

abbrev standardBase : IBr real.standardRoot :=
  IrreducibleBrauerCharacter.equivAlongMulEquiv
    (presentation.factorRoot c) real.identification (presentation.localBase c)

/-- Only the regular-adjoint projection and its literal point square are
sourced.  The projection need not be surjective and has no conformal lift. -/
structure DiagonalSource
    (coordinates : TypeBLeviReturnB2MatrixAction.MatrixKernelSource FQ) where
  projection : fixedPoints (pairedFrobeniusEnd Frob Lbar leviStable) →*
    TypeBConformalDualCarriers.PCSp FQ 2
  ambient_value : ∀ (g : fixedPoints (pairedFrobeniusEnd Frob Lbar leviStable)) (x : Sp4 FQ),
    g.val * adjustedEmbedding real.embedding real.lang.choose (coefficientMap FQ Astd x) * g.val⁻¹ =
      adjustedEmbedding real.embedding real.lang.choose
        (coefficientMap FQ Astd
          (TypeBLeviReturnB2MatrixAction.pcspAction coordinates (projection g) x))

variable {coordinates : TypeBLeviReturnB2MatrixAction.MatrixKernelSource FQ}
variable (diagonal : real.DiagonalSource coordinates)

theorem original_diagonal_value
    (g : fixedPoints (pairedFrobeniusEnd Frob Lbar leviStable))
    (x : Base m geometry.factor c) :
    (originalBaseEquivRational Frob Lbar leviStable m geometry c
      (geometry.actualDiagonal (first m c) g x)).val.val =
    g.val * (originalBaseEquivRational Frob Lbar leviStable m geometry c x).val.val * g.val⁻¹ := by
  exact factorAction_component_value (pairedFrobeniusEnd Frob Lbar leviStable)
    (TypeBLeviRepresentativeGeometry.derivedInside Lbar)
    (TypeBLeviRepresentativeGeometry.derived_stable Frob Lbar leviStable)
    geometry.geometricLength geometry.components geometry.central (first m c) g x

/-- The original conjugation and standard projective conformal action match
through the internally constructed finite identification. -/
theorem diagonal_square
    (g : fixedPoints (pairedFrobeniusEnd Frob Lbar leviStable)) :
    MulAut.congr real.identification (geometry.actualDiagonal (first m c) g) =
      TypeBLeviReturnB2MatrixAction.pcspAction coordinates (diagonal.projection g) := by
  apply MulEquiv.ext
  intro s
  apply coefficientMap_injective FQ Astd
  apply adjustedEmbedding_injective real.embedding real.injective real.lang.choose
  change adjustedEmbedding real.embedding real.lang.choose
    (coefficientMap FQ Astd (real.identification
      (geometry.actualDiagonal (first m c) g (real.identification.symm s)))) = _
  rw [real.identification_value, original_diagonal_value]
  rw [← real.identification_value (real.identification.symm s),
    real.identification.apply_symm_apply]
  exact diagonal.ambient_value g s

include diagonal in
/-- Each actual image actor has a projective representative; no homomorphic
lift of that image to CSp is asserted or used. -/
theorem diagonal_image_lift (d : geometry.diagonalGroup (first m c)) :
    ∃ q : TypeBConformalDualCarriers.PCSp FQ 2,
      canonicalReturn real.identification (geometry.diagonalAction (first m c)) d =
        TypeBLeviReturnB2MatrixAction.pcspAction coordinates q := by
  obtain ⟨g, hg⟩ := d.property
  refine ⟨diagonal.projection g, ?_⟩
  change MulAut.congr real.identification (d : MulAut (Base m geometry.factor c)) = _
  rw [← hg]
  exact real.diagonal_square diagonal g

include diagonal in
/-- Internal transport of a proved standard factorization.  The public
endpoint obtains this premise from the literal FM source. -/
private theorem same_base_of_standard
    (standard :
      letI := rightAutomorphismAction real.standardRoot
        (TypeBLeviReturnB2MatrixAction.pcspAction coordinates)
      letI := rightAutomorphismAction real.standardRoot
        (Subgroup.zpowers (fieldGenerator FQ p)).subtype
      ProductStabilizerFactorization (D := TypeBConformalDualCarriers.PCSp FQ 2)
        (E := Subgroup.zpowers (fieldGenerator FQ p)) real.standardBase) :
    letI := rightAutomorphismAction (presentation.factorRoot c)
      (geometry.diagonalAction (first m c))
    letI := rightAutomorphismAction (presentation.factorRoot c) (presentation.localH c)
    ProductStabilizerFactorization (D := geometry.diagonalGroup (first m c))
      (E := presentation.ReturnGroup c) (presentation.localBase c) ∧
    SemidirectStabilizerFactors (presentation.localD c) (presentation.localCompatible c)
      (presentation.localBase c) := by
  letI := rightAutomorphismAction (presentation.factorRoot c)
    (geometry.diagonalAction (first m c))
  letI := rightAutomorphismAction (presentation.factorRoot c) (presentation.localH c)
  letI := rightAutomorphismAction real.standardRoot
    (TypeBLeviReturnB2MatrixAction.pcspAction coordinates)
  letI := rightAutomorphismAction real.standardRoot
    (Subgroup.zpowers (fieldGenerator FQ p)).subtype
  letI := rightAutomorphismAction real.standardRoot
    (canonicalReturn real.identification (geometry.diagonalAction (first m c)))
  letI := rightAutomorphismAction real.standardRoot
    (canonicalReturn real.identification (presentation.localH c))
  let beta := IrreducibleBrauerCharacter.equivAlongMulEquiv
    (presentation.factorRoot c) real.identification
  have return_transport (r0 : presentation.ReturnGroup c)
      (chi : IBr (presentation.factorRoot c)) :
      beta (r0 • chi) = real.returnToField r0 • beta chi := by
    rw [brauerAction_transport (presentation.factorRoot c) real.identification
      (presentation.localH c)]
    change IrreducibleBrauerCharacter.twist real.standardRoot (beta chi)
      (canonicalReturn real.identification (presentation.localH c) r0⁻¹) =
      IrreducibleBrauerCharacter.twist real.standardRoot (beta chi)
        (canonicalReturn real.identification (presentation.localH c) r0)⁻¹
    rw [map_inv]
  have factor : ProductStabilizerFactorization
      (D := geometry.diagonalGroup (first m c)) (E := presentation.ReturnGroup c)
      (presentation.localBase c) := by
    intro d r0
    obtain ⟨q, hq⟩ := real.diagonal_image_lift diagonal d
    have diagonal_transport (chi : IBr (presentation.factorRoot c)) :
        beta (d • chi) = q • beta chi := by
      rw [brauerAction_transport (presentation.factorRoot c) real.identification
        (geometry.diagonalAction (first m c))]
      change IrreducibleBrauerCharacter.twist real.standardRoot (beta chi)
        (canonicalReturn real.identification (geometry.diagonalAction (first m c)) d⁻¹) =
        IrreducibleBrauerCharacter.twist real.standardRoot (beta chi)
          (TypeBLeviReturnB2MatrixAction.pcspAction coordinates q⁻¹)
      rw [map_inv, hq, map_inv]
    constructor
    · intro equality
      have equalityS : q • (real.returnToField r0 • real.standardBase) = real.standardBase := by
        change q • (real.returnToField r0 • beta (presentation.localBase c)) =
          beta (presentation.localBase c)
        rw [← return_transport r0 (presentation.localBase c),
          ← diagonal_transport (r0 • presentation.localBase c)]
        exact congrArg beta equality
      obtain ⟨hd, hr⟩ := (standard q (real.returnToField r0)).mp equalityS
      exact ⟨beta.injective ((diagonal_transport (presentation.localBase c)).trans hd),
        beta.injective ((return_transport r0 (presentation.localBase c)).trans hr)⟩
    · rintro ⟨hd, hr⟩
      rw [hr, hd]
  exact ⟨factor,
    (semidirectStabilizerFactors_iff_productStabilizerFactorization
      (presentation.localD c) (presentation.localCompatible c)
      (presentation.localBase c)).mpr factor⟩

include diagonal in
/-- The prescribed original B2 character itself is a valid representative.
Both stabilizer factorizations are deduced from literal standard FM separation
through the same coefficient, component, return and adjoint-point squares. -/
theorem b2_localBase_factorization (hOdd : Odd (Nat.card FQ))
    (separation : TypeBLeviReturnB2Diagonal.FengMalleSeparation
      coordinates hOdd real.standardRoot p) :
    letI := rightAutomorphismAction (presentation.factorRoot c)
      (geometry.diagonalAction (first m c))
    letI := rightAutomorphismAction (presentation.factorRoot c) (presentation.localH c)
    ProductStabilizerFactorization (D := geometry.diagonalGroup (first m c))
      (E := presentation.ReturnGroup c) (presentation.localBase c) ∧
    SemidirectStabilizerFactors (presentation.localD c) (presentation.localCompatible c)
      (presentation.localBase c) ∧
    ∃ psi : IBr (presentation.factorRoot c),
      psi = presentation.localBase c ∧
      psi ∈ MulAction.orbit (geometry.diagonalGroup (first m c)) (presentation.localBase c) ∧
      ProductStabilizerFactorization (D := geometry.diagonalGroup (first m c))
        (E := presentation.ReturnGroup c) psi ∧
      SemidirectStabilizerFactors (presentation.localD c) (presentation.localCompatible c) psi := by
  letI := rightAutomorphismAction (presentation.factorRoot c)
    (geometry.diagonalAction (first m c))
  letI := rightAutomorphismAction (presentation.factorRoot c) (presentation.localH c)
  have standard := TypeBLeviReturnB2Diagonal.standard_product_factorization
    coordinates hOdd real.standardRoot p separation real.standardBase
  obtain ⟨factor, semidirect⟩ := real.same_base_of_standard diagonal standard
  exact ⟨factor, semidirect, presentation.localBase c, rfl,
    ⟨1, one_smul (geometry.diagonalGroup (first m c)) (presentation.localBase c)⟩,
    factor, semidirect⟩

end B2Realization

end ModularRep.PaperProofs.TypeBLeviReturnB2Application


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
