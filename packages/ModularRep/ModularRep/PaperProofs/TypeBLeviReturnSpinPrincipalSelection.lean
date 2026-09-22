import ModularRep.PaperProofs.TypeBLeviReturnSpinOriginalReturn
import ModularRep.PaperProofs.TypeBLeviReturnPowerArithmetic
import ModularRep.PaperProofs.TypeBLeviReturnSpinCoefficientBinding
import ModularRep.PaperProofs.TypeBLeviReturnPrincipalSelectorBinding
import ModularRep.PaperProofs.TypeBCentralKernelSpinFibreIdentification

/-!
# The same principal constituent on an original Spin-type factor

The original local return is computed from its one-step field/component
dictionary. The finite Spin identification uses the same coefficient map
and one Lang adjustment. The standard root, block and supported character
are transported from the prescribed original local base.

The two public selection theorems call the actual rank-three or
rank-at-least-four GGGR fixation provider with its full specified telescope.
No ModelData, common-adjoint comparison, completed standard fixation or
finished local-return square is an external source. The representative is
the original localBase itself. This is the Spin principal branch only.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBLeviReturnSpinPrincipalSelection

open Formalisation
open ModularRep TypeBCliffordCarriers TypeBRegularLeviRationalCarriers
open TypeBComponentCycleNormalization TypeBRegularLeviCharacterActionAdapter
open TypeBLeviRepresentativeCarriers TypeBLeviRepresentativeSelection
open TypeBLeviReturnSpinOriginalCarrier TypeBLeviReturnSpinOriginalReturn
open TypeBLeviReturnSpinCoefficientBinding TypeBLeviReturnPowerSelection
open TypeBComponentReturnCarrierTransport TypeBCentralKernelBlockSource
open TypeBCentralKernelSpinFibreIdentification
open EvenFieldAssumption53Relative
open ModularRep.ManuscriptVerification.StabilizerFactorizationTransport

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

/-- The original component-cycle dictionary, before choosing corrected powers.
The period identification and SameCycle statement refer only to the actual
component permutation and its original rational cycle. -/
structure OriginalCycleData
    (presentation : Presentation geometry field root theta0) (c : C) where
  points : OriginalFieldData geometry field
  h : ℕ
  a : ℕ
  defining : TypeBLeviRepresentativeGeometry.pairedFrobenius Frob Lbar leviStable =
    points.F0 ^ h
  tau_value : presentation.tau.1 = field.generator ^ a
  defining_period : TypeBLeviReturnPowerArithmetic.orbitLength (points.permutation ^ h)
    (first geometry.geometricLength (first m c)) =
      geometry.geometricLength (first m c) + 1
  return_cycle : (points.permutation ^ h).SameCycle
    (first geometry.geometricLength (first m c))
    ((points.permutation ^ (a * (m c + 1)))
      (first geometry.geometricLength (first m c)))

namespace OriginalCycleData

variable {presentation : Presentation geometry field root theta0} {c : C}
variable (cycle : OriginalCycleData presentation c)

abbrev u : ℕ := TypeBLeviReturnPowerArithmetic.orbitLength cycle.points.permutation
  (first geometry.geometricLength (first m c))

private theorem powers_exist :
    ∃ v : ℕ × ℕ × ℕ,
      cycle.a * (m c + 1) + cycle.h * v.1 = cycle.u * v.2.1 ∧
      cycle.h * (geometry.geometricLength (first m c) + 1) = cycle.u * v.2.2 := by
  obtain ⟨k0, _, _, r0, s0, hr, hs⟩ :=
    TypeBLeviReturnPowerArithmetic.exists_natural_return_powers
      cycle.points.permutation (first geometry.geometricLength (first m c))
      cycle.a (m c + 1) cycle.h cycle.return_cycle
  rw [cycle.defining_period] at hs
  exact ⟨⟨(-k0).toNat, r0, s0⟩, hr, hs⟩

/-- One simultaneous choice of the already proved natural multipliers. -/
def powers : {v : ℕ × ℕ × ℕ //
    cycle.a * (m c + 1) + cycle.h * v.1 = cycle.u * v.2.1 ∧
      cycle.h * (geometry.geometricLength (first m c) + 1) = cycle.u * v.2.2} :=
  ⟨cycle.powers_exist.choose, cycle.powers_exist.choose_spec⟩

abbrev q : ℕ := cycle.powers.1.1
abbrev r : ℕ := cycle.powers.1.2.1
abbrev s : ℕ := cycle.powers.1.2.2

theorem return_exponent :
    cycle.a * (m c + 1) + cycle.h * cycle.q = cycle.u * cycle.r :=
  cycle.powers.2.1

theorem fixed_exponent :
    cycle.h * (geometry.geometricLength (first m c) + 1) = cycle.u * cycle.s :=
  cycle.powers.2.2

theorem period : (cycle.points.permutation ^ cycle.u)
    (first geometry.geometricLength (first m c)) =
      first geometry.geometricLength (first m c) :=
  MulAction.pow_period_smul cycle.points.permutation
    (first geometry.geometricLength (first m c))

end OriginalCycleData

/-- Lower geometric and coefficient inputs for one specified Spin component.
Corrected exponents are computed from cycle data; no completed return map,
finite-model equivalence or selected character is a source field. -/
structure SpinRealization
    (presentation : Presentation geometry field root theta0) (c : C)
    (n p f : ℕ) (FQ Astd : Type)
    [Field FQ] [Finite FQ] [CharP FQ p] [Field Astd] [Algebra FQ Astd]
    (NQ : NormSource n FQ) (Nbar : NormSource n Astd) where
  cycle : OriginalCycleData presentation c
  primeStep : ℕ
  FrobStd : MulAut (SpecialClifford n Astd)
  coefficients : CliffordFixedPointSource n p f FQ Astd NQ Nbar FrobStd
  fieldAction : FieldActionSource n FQ p f coefficients.parameters NQ
  common : Monoid.End (Spin n Astd Nbar)
  commonData : CommonFrobeniusData (p := p) (b := primeStep * cycle.u) common
  finite_exponent : f = (primeStep * cycle.u) * cycle.s
  embedding : Spin n Astd Nbar →* pairedLevi Lbar
  injective : Function.Injective embedding
  range : embedding.range = originalComponent Frob Lbar leviStable m geometry c
  twist : Spin n Astd Nbar
  generator_value : ∀ x, (cycle.points.F0 ^ cycle.u) (embedding x) =
    embedding (twist * common x * twist⁻¹)
  lang : ∃ z : Spin n Astd Nbar, common z * z⁻¹ = twist⁻¹

namespace SpinRealization

variable {presentation : Presentation geometry field root theta0} {c : C}
variable {n p f : ℕ} {FQ Astd : Type}
variable [Field FQ] [Finite FQ] [CharP FQ p] [Field Astd] [Algebra FQ Astd]
variable {NQ : NormSource n FQ} {Nbar : NormSource n Astd}
variable (real : SpinRealization presentation c n p f FQ Astd NQ Nbar)

abbrev points := real.cycle.points
abbrev h := real.cycle.h
abbrev u := real.cycle.u
abbrev a := real.cycle.a
abbrev q := real.cycle.q
abbrev r := real.cycle.r
abbrev s := real.cycle.s
abbrev defining := real.cycle.defining
abbrev tau_value := real.cycle.tau_value
abbrev period := real.cycle.period
abbrev return_exponent := real.cycle.return_exponent
abbrev fixed_exponent := real.cycle.fixed_exponent

/-- The defining exponent is positive by the same finite-field parameters. -/
theorem definingPower_pos : 0 < real.s := by
  apply Nat.pos_of_ne_zero
  intro hs
  change real.cycle.s = 0 at hs
  have hf := real.coefficients.parameters.exponent_pos
  rw [real.finite_exponent, hs, Nat.mul_zero] at hf
  exact (Nat.lt_irrefl 0) hf

/-- The same coefficient map and single chosen Lang solution. -/
def standardToRational : Spin n FQ NQ ≃*
    rationalSubgroup
      (pairedFrobeniusEnd Frob Lbar leviStable ^
        (geometry.geometricLength (first m c) + 1))
      (originalComponent Frob Lbar leviStable m geometry c) :=
  normalizedSpinEquiv real.coefficients real.common real.commonData real.finite_exponent
    real.embedding (originalComponent Frob Lbar leviStable m geometry c)
    real.injective real.range real.points.F0
    (TypeBLeviRepresentativeGeometry.pairedFrobenius Frob Lbar leviStable)
    real.h real.u (geometry.geometricLength (first m c) + 1)
    real.defining real.fixed_exponent real.twist real.generator_value
    real.lang.choose real.lang.choose_spec

/-- Identification of the actual original factor, constructed internally. -/
def identification : Base m geometry.factor c ≃* Spin n FQ NQ :=
  (originalBaseEquivRational Frob Lbar leviStable m geometry c).trans
    real.standardToRational.symm

/-- The actual positive local generator has the computed full-field value. -/
theorem localGenerator_value (x : Base m geometry.factor c) :
    real.identification (presentation.localH c (presentation.localGenerator c) x) =
      spinFieldAction n FQ real.fieldAction
        (fieldGenerator f ^ ((real.primeStep * real.u) * real.r))
        (real.identification x) := by
  let nu := originalBaseEquivRational Frob Lbar leviStable m geometry c
  let eS := real.standardToRational
  let actual := MulAut.congr nu (presentation.localH c (presentation.localGenerator c))
  have value (z : rationalSubgroup
      (pairedFrobeniusEnd Frob Lbar leviStable ^
        (geometry.geometricLength (first m c) + 1))
      (originalComponent Frob Lbar leviStable m geometry c)) :
      (actual z).1.1 =
        (pairedFrobeniusEnd Frob Lbar leviStable ^ real.q)
          ((real.points.F0 ^ (real.a * (m c + 1))) z.1.1) := by
    obtain ⟨y, rfl⟩ := nu.surjective z
    change (nu (presentation.localH c (presentation.localGenerator c)
      (nu.symm (nu y)))).1.1 = _
    rw [nu.symm_apply_apply]
    exact original_positive_return_value geometry field real.points presentation c
      real.a real.h real.u real.q real.r real.tau_value real.defining
      real.return_exponent real.period y
  have square := normalizedSpinEquiv_return_square real.coefficients real.fieldAction
    real.common real.commonData real.finite_exponent
    real.embedding (originalComponent Frob Lbar leviStable m geometry c)
    real.injective real.range real.points.F0
    (TypeBLeviRepresentativeGeometry.pairedFrobenius Frob Lbar leviStable)
    real.h real.u (geometry.geometricLength (first m c) + 1)
    real.defining real.fixed_exponent real.twist real.generator_value
    real.lang.choose real.lang.choose_spec
    (real.a * (m c + 1)) real.q real.r real.return_exponent
    real.definingPower_pos actual value (real.identification x)
  change actual (eS (real.identification x)) =
    eS (spinFieldAction n FQ real.fieldAction
      (fieldGenerator f ^ ((real.primeStep * real.u) * real.r))
      (real.identification x)) at square
  apply eS.injective
  change eS (eS.symm (nu (presentation.localH c (presentation.localGenerator c) x))) = _
  rw [eS.apply_symm_apply]
  change nu (presentation.localH c (presentation.localGenerator c) x) = _
  change nu (presentation.localH c (presentation.localGenerator c)
    (nu.symm (eS (eS.symm (nu x))))) = _ at square
  rw [eS.apply_symm_apply, nu.symm_apply_apply] at square
  exact square

/-- Every element of the ORIGINAL return subgroup maps into the full field image. -/
theorem return_mem_fieldImage (r0 : presentation.ReturnGroup c) :
    canonicalReturn real.identification (presentation.localH c) r0 ∈
      (spinFieldAction n FQ real.fieldAction).range := by
  exact canonicalReturn_mem real.identification (presentation.localH c)
    (spinFieldAction n FQ real.fieldAction).range (presentation.localGenerator c)
    (presentation.localGenerator_generates c)
    ⟨spinFieldAction n FQ real.fieldAction
      (fieldGenerator f ^ ((real.primeStep * real.u) * real.r)),
      ⟨fieldGenerator f ^ ((real.primeStep * real.u) * real.r), rfl⟩⟩
    real.localGenerator_value r0

include real in
/-- Finiteness is inherited from the same original rational component. -/
theorem finiteSpin : Finite (Spin n FQ NQ) :=
  Finite.of_equiv (Base m geometry.factor c) real.identification.toEquiv

variable [Finite (Spin n FQ NQ)]

abbrev standardRoot :=
  (presentation.factorRoot c).alongMulEquiv real.identification

abbrev standardBase : IBr real.standardRoot :=
  IrreducibleBrauerCharacter.equivAlongMulEquiv (presentation.factorRoot c)
    real.identification (presentation.localBase c)

def standardBlock (bH : LiteralPrimitiveBlock k (Base m geometry.factor c)) :
    LiteralPrimitiveBlock k (Spin n FQ NQ) :=
  primitiveBlockEquiv real.identification bH

theorem standardBlock_principal (bH : LiteralPrimitiveBlock k (Base m geometry.factor c))
    (principal : IsPrincipal bH) : IsPrincipal (real.standardBlock bH) :=
  (primitiveBlockEquiv_principal_iff real.identification bH).mpr principal

/-- Support moves with the same affording representation, root and idempotent. -/
theorem standardBase_supported (bH : LiteralPrimitiveBlock k (Base m geometry.factor c))
    (support : Supported (presentation.factorRoot c) bH (presentation.localBase c)) :
    Supported real.standardRoot (real.standardBlock bH) real.standardBase := by
  exact TypeBCentralKernelButterflyCharacterIdentification.supported_along_of_lift_eq
    real.identification (presentation.factorRoot c) real.standardRoot bH
    (presentation.localBase c) real.standardBase
    (funext fun z ↦ (presentation.factorRoot c).alongMulEquiv_lift real.identification z)
    rfl support

/-- Internal implication used only after applying the specified GGGR provider. -/
private theorem same_base_of_field_fixation
    (fixed : ∀ a : FieldGroup f,
      IrreducibleBrauerCharacter.twist real.standardRoot real.standardBase
        (spinFieldAction n FQ real.fieldAction a) = real.standardBase) :
    letI := rightAutomorphismAction (presentation.factorRoot c)
      (geometry.diagonalAction (first m c))
    letI := rightAutomorphismAction (presentation.factorRoot c) (presentation.localH c)
    (∀ r0 : presentation.ReturnGroup c, r0 • presentation.localBase c = presentation.localBase c) ∧
      ProductStabilizerFactorization (D := geometry.diagonalGroup (first m c))
        (E := presentation.ReturnGroup c) (presentation.localBase c) ∧
      SemidirectStabilizerFactors (presentation.localD c) (presentation.localCompatible c)
        (presentation.localBase c) := by
  letI := rightAutomorphismAction (presentation.factorRoot c)
    (geometry.diagonalAction (first m c))
  letI := rightAutomorphismAction (presentation.factorRoot c) (presentation.localH c)
  letI := rightAutomorphismAction real.standardRoot
    (canonicalReturn real.identification (presentation.localH c))
  let beta := IrreducibleBrauerCharacter.equivAlongMulEquiv
    (presentation.factorRoot c) real.identification
  have actual_fixed (r0 : presentation.ReturnGroup c) :
      r0 • presentation.localBase c = presentation.localBase c := by
    apply beta.injective
    rw [brauerAction_transport (presentation.factorRoot c) real.identification
      (presentation.localH c)]
    change IrreducibleBrauerCharacter.twist real.standardRoot real.standardBase
      (canonicalReturn real.identification (presentation.localH c) r0⁻¹) =
        real.standardBase
    obtain ⟨a, ha⟩ := real.return_mem_fieldImage r0⁻¹
    rw [← ha]
    exact fixed a
  have factor : ProductStabilizerFactorization
      (D := geometry.diagonalGroup (first m c))
      (E := presentation.ReturnGroup c) (presentation.localBase c) := by
    intro d r0
    constructor
    · intro equality
      exact ⟨by simpa only [actual_fixed r0] using equality, actual_fixed r0⟩
    · rintro ⟨hd, _⟩
      rw [actual_fixed r0, hd]
  exact ⟨actual_fixed, factor,
    (semidirectStabilizerFactors_iff_productStabilizerFactorization
      (presentation.localD c) (presentation.localCompatible c)
      (presentation.localBase c)).mpr factor⟩

end SpinRealization



section RankThree

open OrdinaryIrreducibleCharacter TypeBCentralKernelBlockSource
open TypeBSpinRationalUnipotentClassBinding TypeBSpinGGGRPrincipalSeriesBinding
open TypeBSpinPrincipalGGGRBasisBinding TypeBSpinPrincipalDecompositionBinding
open TypeBSpinPrincipalProjectiveBinding TypeBSpinGGGRProjectivityBinding
open TypeBPrincipalSelectorCorollary413SourceInstantiation
open TypeBGGGRRankProposition412Corollary413Bridge TypeBIndexedRationalFieldHandoff
open scoped MonoidAlgebra

variable {presentation : Presentation geometry field root theta0} {c : C}
variable {p f : ℕ} {FQ Astd O : Type}
variable [Field FQ] [Finite FQ] [CharP FQ p] [Field Astd] [Algebra FQ Astd]
variable {NQ : NormSource 3 FQ} {Nbar : NormSource 3 Astd}
variable [HasEnoughRootsOfUnity K (Nat.card (Spin 3 FQ NQ))]
variable [CommRing O] [IsDomain O] [Algebra O K]
variable (real : SpinRealization presentation c 3 p f FQ Astd NQ Nbar)
variable (bH : LiteralPrimitiveBlock k (Base m geometry.factor c))
variable (principal : IsPrincipal bH)

local instance finiteTypeFintype (X : Type) [Finite X] : Fintype X :=
  Fintype.ofFinite X

/-- Rank three: the specified principal GGGR theorem fixes the SAME original
local base under the entire original return group. Finiteness of this actual
Spin carrier is derived from its constructed original-factor identification. -/
theorem spin_principal_localBase_rankThree :
    letI : Finite (Spin 3 FQ NQ) := real.finiteSpin
    ∀ (orthogonality : OrdinaryOrthogonalitySource (N := NQ) (K := K))
      {GeometricClass : Type}
      (geometricClass : UnipotentClass (r := p) (N := NQ) → GeometricClass)
      (geometricStable : GeometricFieldStable real.coefficients.parameters
        real.fieldAction geometricClass)
      (ComponentGroup : GeometricClass → Type) [∀ D, Group (ComponentGroup D)]
      (inner : ∀ D, ComponentGroup D)
      (gamma : UnipotentClass (r := p) (N := NQ) → Spin 3 FQ NQ → K)
      (rational : RationalGGGRSource (K := K) real.coefficients.parameters
        (show 3 ≤ 3 from le_rfl) real.fieldAction
        geometricClass geometricStable ComponentGroup inner)
      (gamma_eq : rational.gamma = gamma)
      (rationalSeries : TypeBConformalDualCarriers.PCSp FQ 3 →
        Irr K (Spin 3 FQ NQ) → Prop)
      (quasiIsolated : TypeBConformalDualCarriers.PCSp FQ 3 → Prop)
      (normalizedDual : Irr K (Spin 3 FQ NQ) → Irr K (Spin 3 FQ NQ))
      (unipotentSupport : Irr K (Spin 3 FQ NQ) → GeometricClass → Prop)
      (raw : RankThreeChanebSource real.coefficients.parameters geometricClass
        ComponentGroup gamma rationalSeries quasiIsolated normalizedDual unipotentSupport)
      (Msys : ModularSystem 2 K O k)
      (hcompat : StableReductionBrauerCharacterCompatibility Msys real.standardRoot)
      [Fintype (LiteralPrimitiveBlock k (Spin 3 FQ NQ))]
      (blocks : BlockIdempotentDecomposition
        (fun b : LiteralPrimitiveBlock k (Spin 3 FQ NQ) ↦ b.val))
      (ordinary : OrdinaryBlockSource Msys real.standardRoot blocks)
      (columns : DecompositionColumnIndependenceSource Msys real.standardRoot)
      (series : PrincipalSeriesCertificate real.coefficients.parameters
        (show 3 ≤ 3 from le_rfl) ordinary.ordinaryBlock
        (real.standardBlock bH) (real.standardBlock_principal bH principal)
        rationalSeries quasiIsolated normalizedDual)
      {classCount : ℕ}
      (classIndex : Fin classCount ≃ UnipotentClass (r := p) (N := NQ))
      (closure : GeometricClass → GeometricClass → Prop)
      (ordering : GeometricOrdering geometricClass classIndex closure)
      (waveFront : WaveFrontClosureCertificate real.coefficients.parameters
        geometricClass gamma normalizedDual unipotentSupport closure)
      (count : PrincipalRationalClassCount real.coefficients.parameters
        real.standardRoot (real.standardBlock bH) (real.standardBlock_principal bH principal))
      (induction : GGGRInductionSource real.coefficients.parameters
        (show 3 ≤ 3 from le_rfl) gamma)
      (expansion : letI : Finite (Irr K (Spin 3 FQ NQ)) := ordinary_finite orthogonality
        OddInductionExpansionCertificate Msys real.standardRoot hcompat),
    Supported (presentation.factorRoot c) bH (presentation.localBase c) →
    letI := rightAutomorphismAction (presentation.factorRoot c)
      (geometry.diagonalAction (first m c))
    letI := rightAutomorphismAction (presentation.factorRoot c) (presentation.localH c)
    (∀ r0 : presentation.ReturnGroup c, r0 • presentation.localBase c = presentation.localBase c) ∧
      ProductStabilizerFactorization (D := geometry.diagonalGroup (first m c))
        (E := presentation.ReturnGroup c) (presentation.localBase c) ∧
      SemidirectStabilizerFactors (presentation.localD c) (presentation.localCompatible c)
        (presentation.localBase c) := by
  letI : Finite (Spin 3 FQ NQ) := real.finiteSpin
  intro orthogonality GeometricClass geometricClass geometricStable
    ComponentGroup componentInstances inner gamma rational gamma_eq rationalSeries
    quasiIsolated normalizedDual unipotentSupport raw Msys hcompat blockInstances
    blocks ordinary columns series classCount classIndex closure ordering waveFront
    count induction expansion support
  apply SpinRealization.same_base_of_field_fixation real
  intro fieldElement
  exact TypeBSpinPrincipalGGGRFieldApplication.principalBrauer_fixed
    (N := NQ) (parameters := real.coefficients.parameters)
    (geometricClass := geometricClass) (ComponentGroup := ComponentGroup)
    (gamma := gamma) (rationalSeries := rationalSeries)
    (quasiIsolated := quasiIsolated) (normalizedDual := normalizedDual)
    (unipotentSupport := unipotentSupport) (raw := raw)
    (orthogonality := orthogonality) (Msys := Msys) (iota := real.standardRoot)
    (hcompat := hcompat) (b := real.standardBlock bH)
    (principal := real.standardBlock_principal bH principal)
    (blocks := blocks) (ordinary := ordinary) (columns := columns) (series := series)
    (classIndex := classIndex) (closure := closure) (ordering := ordering)
    (waveFront := waveFront) (count := count) (induction := induction) (expansion := expansion)
    (S := real.fieldAction) (geometricStable := geometricStable) (inner := inner)
    (rational := rational) (gamma_eq := gamma_eq)
    fieldElement real.standardBase (real.standardBase_supported bH support)

end RankThree

section RankAtLeastFour

open OrdinaryIrreducibleCharacter TypeBCentralKernelBlockSource
open TypeBSpinPrincipalDecompositionBinding TypeBSpinPrincipalProjectiveBinding
open TypeBSpinRationalUnipotentClassBinding TypeBSpinGGGRPrincipalSeriesBinding
open TypeBSpinGGGRProjectivityBinding TypeBSpinGGGRRationalSpanBinding
open TypeBAllRankGGGRFibres TypeBAllRankGGGREntries TypeBAllRankGGGR.BasisPhysical
open scoped MonoidAlgebra Pointwise

variable {presentation : Presentation geometry field root theta0} {c : C}
variable {n p f : ℕ} {FQ Astd O : Type}
variable [Field FQ] [Finite FQ] [CharP FQ p] [Field Astd] [Algebra FQ Astd]
variable [CommRing O] [IsDomain O] [Algebra O K]
variable {NQ : NormSource n FQ} {Nbar : NormSource n Astd}
variable (real : SpinRealization presentation c n p f FQ Astd NQ Nbar)
variable (finiteClifford : FiniteCliffordSource n FQ)
variable [HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n FQ))]
variable (bH : LiteralPrimitiveBlock k (Base m geometry.factor c))
variable (principal : IsPrincipal bH)

/-- Rank at least four: the same original principal constituent is fixed.
The upper Clifford root hypothesis and the original specified GGGR inputs are
retained; the finite Spin carrier and its ordinary roots are derived. -/
theorem spin_principal_localBase_rankAtLeastFour :
    letI : Finite (SpecialClifford n FQ) := specialClifford_finite n FQ finiteClifford
    letI : Finite (Spin n FQ NQ) :=
      TypeBAllRankGGGRCarriers.spin_finite NQ finiteClifford
    letI : HasEnoughRootsOfUnity K (Nat.card (Spin n FQ NQ)) :=
      TypeBAllRankGGGRCarriers.spin_roots_of_upper NQ
    ∀ (orthogonality : OrdinaryOrthogonalitySource (N := NQ) (K := K)),
    letI : Finite (Irr K (Spin n FQ NQ)) := ordinary_finite orthogonality
    ∀ {rank : 4 ≤ n}
      {GeometricClass : Type}
      {geometricClass : UnipotentClass (r := p) (N := NQ) → GeometricClass}
      {upperGeometricClass :
        UpperUnipotentClass (n := n) (F := FQ) (r := p) → GeometricClass}
      {geometric_square : ∀ z,
        upperGeometricClass (upperClassMap z) = geometricClass z}
      {ComponentGroup : GeometricClass → Type} [∀ D, Group (ComponentGroup D)]
      (geometricStable : GeometricFieldStable real.coefficients.parameters
        real.fieldAction geometricClass)
      (inner : ∀ D, ComponentGroup D)
      (rational : RationalGGGRSource (K := K) real.coefficients.parameters
        (Nat.le_trans (show 3 ≤ 4 by decide) rank) real.fieldAction
        geometricClass geometricStable ComponentGroup inner)
      {upperDual : Irr K (SpecialClifford n FQ) → Irr K (SpecialClifford n FQ)}
      {lowerDual : Irr K (Spin n FQ NQ) → Irr K (Spin n FQ NQ)}
      {rationalSeries : TypeBConformalDualCarriers.PCSp FQ n →
        Irr K (Spin n FQ NQ) → Prop}
      {quasiIsolated : TypeBConformalDualCarriers.PCSp FQ n → Prop}
      {unipotentSupport : Irr K (Spin n FQ NQ) → GeometricClass → Prop}
      {Msys : ModularSystem 2 K O k}
      {hcompat : StableReductionBrauerCharacterCompatibility Msys real.standardRoot}
      [Fintype (LiteralPrimitiveBlock k (Spin n FQ NQ))]
      {blocks : BlockIdempotentDecomposition
        (fun b : LiteralPrimitiveBlock k (Spin n FQ NQ) ↦ b.val)}
      {ordinary : OrdinaryBlockSource Msys real.standardRoot blocks}
      (columns : DecompositionColumnIndependenceSource Msys real.standardRoot)
      (series : PrincipalSeriesCertificate real.coefficients.parameters
        (Nat.le_trans (show 3 ≤ 4 by decide) rank)
        ordinary.ordinaryBlock (real.standardBlock bH)
        (real.standardBlock_principal bH principal)
        rationalSeries quasiIsolated lowerDual)
      {classCount : ℕ}
      (classIndex : Fin classCount ≃ UnipotentClass (r := p) (N := NQ))
      {closure : GeometricClass → GeometricClass → Prop}
      (ordering : GeometricOrdering geometricClass classIndex closure)
      (waveFront : WaveFrontClosureCertificate real.coefficients.parameters rank
        geometricClass rational.gamma lowerDual unipotentSupport closure)
      (count : PrincipalRationalClassCount real.coefficients.parameters rank
        real.standardRoot (real.standardBlock bH)
        (real.standardBlock_principal bH principal))
      (induction : GGGRInductionSource real.coefficients.parameters
        (Nat.le_trans (show 3 ≤ 4 by decide) rank) rational.gamma)
      (expansion : OddInductionExpansionCertificate Msys real.standardRoot hcompat)
      (reciprocity : FrobeniusReciprocitySource (N := NQ) (K := K))
      (sources : ∀ D, Nonempty (RationalFibre geometricClass D) →
        TypeBAllRankGGGRSelection.LocalSources (geometricClass := geometricClass)
          (upperGeometricClass := upperGeometricClass) (geometric_square := geometric_square)
          (ComponentGroup := ComponentGroup) (gamma := rational.gamma) (upperDual := upperDual)
          (lowerDual := lowerDual) (rationalSeries := rationalSeries)
          (quasiIsolated := quasiIsolated) (unipotentSupport := unipotentSupport)
          (parameters := real.coefficients.parameters) (rank := rank) D),
    Supported (presentation.factorRoot c) bH (presentation.localBase c) →
    letI := rightAutomorphismAction (presentation.factorRoot c)
      (geometry.diagonalAction (first m c))
    letI := rightAutomorphismAction (presentation.factorRoot c) (presentation.localH c)
    (∀ r0 : presentation.ReturnGroup c, r0 • presentation.localBase c = presentation.localBase c) ∧
      ProductStabilizerFactorization (D := geometry.diagonalGroup (first m c))
        (E := presentation.ReturnGroup c) (presentation.localBase c) ∧
      SemidirectStabilizerFactors (presentation.localD c) (presentation.localCompatible c)
        (presentation.localBase c) := by
  classical
  letI : Finite (SpecialClifford n FQ) := specialClifford_finite n FQ finiteClifford
  letI : Finite (Spin n FQ NQ) := TypeBAllRankGGGRCarriers.spin_finite NQ finiteClifford
  letI : HasEnoughRootsOfUnity K (Nat.card (Spin n FQ NQ)) :=
    TypeBAllRankGGGRCarriers.spin_roots_of_upper NQ
  intro orthogonality
  letI : Finite (Irr K (Spin n FQ NQ)) := ordinary_finite orthogonality
  intro rank GeometricClass geometricClass upperGeometricClass geometric_square
    ComponentGroup componentInstances geometricStable inner rational
    upperDual lowerDual rationalSeries quasiIsolated unipotentSupport
    Msys hcompat blockInstances blocks ordinary columns series
    classCount classIndex closure ordering waveFront count induction expansion reciprocity sources
    support
  apply SpinRealization.same_base_of_field_fixation real
  intro fieldElement
  exact TypeBAllRankPrincipalSelectorApplication.principalBrauer_fixed
    (N := NQ) finiteClifford orthogonality
    (parameters := real.coefficients.parameters) (rank := rank) real.fieldAction
    (geometricClass := geometricClass) (upperGeometricClass := upperGeometricClass)
    (geometric_square := geometric_square) (ComponentGroup := ComponentGroup)
    geometricStable inner rational
    (upperDual := upperDual) (lowerDual := lowerDual)
    (rationalSeries := rationalSeries) (quasiIsolated := quasiIsolated)
    (unipotentSupport := unipotentSupport)
    (Msys := Msys) (iota := real.standardRoot) (hcompat := hcompat)
    (b := real.standardBlock bH) (principal := real.standardBlock_principal bH principal)
    (blocks := blocks) (ordinary := ordinary)
    columns series classIndex ordering waveFront count induction expansion reciprocity sources
    fieldElement real.standardBase (real.standardBase_supported bH support)

end RankAtLeastFour

end ModularRep.PaperProofs.TypeBLeviReturnSpinPrincipalSelection


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
