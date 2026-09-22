import ManuscriptIBAW.TypeB.Levi
import ManuscriptIBAW.TypeB.PrincipalApplication
import ManuscriptIBAW.TypeB.LeviRankTwo
import ModularRep.PaperProofs.TypeBCurrentBrauerHypothesis

/-!
# Principal assumptions on every Levi factor

The Levi arguments use the GGGR context and the published principal results
on the Spin factors of higher rank. The required principal series assertion
is proved from the underlying context data before it is used in these
arguments. Type A uses its separately stated published result. Rank two
uses the principal block assertion, with a direct proof for trivial field action.
Factor representatives and the final Brauer hypothesis follow from these
assumptions.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option genInjectivity false
set_option genSizeOfSpec false
open scoped MonoidAlgebra

namespace ManuscriptIBAW.TypeB.LeviSources

open Formalisation ModularRep ModularRep.PaperProofs
open TypeBCliffordCarriers TypeBRegularLeviRationalCarriers
open TypeBLeviRepresentativeCarriers TypeBLeviRepresentativeSelection
open TypeBLemma47LeviApplication
open TypeBCurrentLeviAssembly TypeBCurrentLeviFactorSelection
open TypeBLeviRepresentativeAssembly TypeBLeviRepresentativeClifford TypeBLeviRepresentativeField
open TypeBCharacteristicTwoCorrespondenceSource TypeBCharacteristicTwoExtensionCarriers
open TypeBCharacteristicTwoCliffordKernel TypeBCharacteristicTwoCliffordApplication
open TypeBCharacteristicTwoGallagherSource TypeBCharacteristicTwoGallagherProduct
open TypeBLeviRepresentativeFactorSelector TypeBComponentReturnCarrierTransport
open TypeBRegularLeviCharacterActionAdapter EvenFieldAssumption53Relative
open TypeBCurrentBrauerTransport TypeBCurrentBrauerHypothesis
open FDRepSimpleClassKZero CyclicOuterLemma37LiteralLocalExtension
open TypeBComponentCycleNormalization TypeBComponentReturnOriginalCarriers
open TypeBLeviReturnPowerSelection TypeBLeviReturnSpinPrincipalSelection TypeBCentralKernelBlockSource
open TypeBCentralKernelCarriers TypeBCharacteristicTwoConstituentSource
open TypeBRankThreeJordanPacketCarriers TypeBCurrentJordanCliffordCarriers
open ModularRep.ManuscriptVerification.StabilizerFactorizationTransport

section Factors

variable {A : Type} [Group A] {Frob : MulAut A} {Lbar : Subgroup A}
  [Finite (fixedPoints Frob.toMonoidHom)]
  {E : Type} [Group E] [Finite E] [IsCyclic E]
  {C : Type} [Fintype C] {m : C → ℕ}
  {leviStable : Lbar.map Frob.toMonoidHom = Lbar}
  {k K : Type} [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
  {geometry : PrimalData Frob Lbar leviStable m}
  {field : FieldData Frob Lbar E}
  {root : PrimeRegularRootEmbedding 2 k K (L0 Frob.toMonoidHom Lbar)}
  {theta0 : IBr (rootN Frob Lbar root)}
  {presentation : Presentation geometry field root theta0} {c : C}

structure SpinFactorSources (presentation : Presentation geometry field root theta0) (c : C) where
  n : ℕ
  p : ℕ
  f : ℕ
  FQ : Type
  Astd : Type
  O : Type
  [fieldFQ : Field FQ]
  [finiteFQ : Finite FQ]
  [charFQ : CharP FQ p]
  [fieldAstd : Field Astd]
  [algebraAstd : Algebra FQ Astd]
  [ringO : CommRing O]
  [domainO : IsDomain O]
  [algebraO : Algebra O K]
  NQ : NormSource n FQ
  Nbar : NormSource n Astd
  [finiteUpper : Finite (SpecialClifford n FQ)]
  [finiteLower : Finite (Spin n FQ NQ)]
  [rootsUpper : HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n FQ))]
  [rootsLower : HasEnoughRootsOfUnity K (Nat.card (Spin n FQ NQ))]
  [finiteIrr : Finite (OrdinaryIrreducibleCharacter.Irr K (Spin n FQ NQ))]
  [finiteBlocks : Fintype (LiteralPrimitiveBlock k (Spin n FQ NQ))]
  real : SpinRealization presentation c n p f FQ Astd NQ Nbar
  rank : 3 ≤ n
  block : LiteralPrimitiveBlock k (Base m geometry.factor c)
  principal : IsPrincipal block
  supported : Supported (presentation.factorRoot c) block (presentation.localBase c)
  Msys : ModularSystem 2 K O k
  data : PrincipalSeries.ContextData real.coefficients.parameters rank Msys
    real.standardRoot (real.standardBlock block)
  current : PrincipalApplication.Inputs data real.fieldAction

attribute [instance] SpinFactorSources.fieldFQ SpinFactorSources.finiteFQ
  SpinFactorSources.charFQ SpinFactorSources.fieldAstd SpinFactorSources.algebraAstd
  SpinFactorSources.ringO SpinFactorSources.domainO SpinFactorSources.algebraO
  SpinFactorSources.finiteUpper SpinFactorSources.finiteLower SpinFactorSources.rootsUpper
  SpinFactorSources.rootsLower SpinFactorSources.finiteIrr SpinFactorSources.finiteBlocks


/-- Apply current GGGR fixedness to the same transported character. -/
theorem SpinFactorSources.representative (sources : SpinFactorSources presentation c) :
    FactorRepresentative presentation c := by
  let := rightAutomorphismAction (presentation.factorRoot c)
    (geometry.diagonalAction (first m c))
  let := rightAutomorphismAction (presentation.factorRoot c) (presentation.localH c)
  let := rightAutomorphismAction sources.real.standardRoot
    (canonicalReturn sources.real.identification (presentation.localH c))
  let beta := IrreducibleBrauerCharacter.equivAlongMulEquiv
    (presentation.factorRoot c) sources.real.identification
  have fixed (r : presentation.ReturnGroup c) :
      r • presentation.localBase c = presentation.localBase c := by
    apply beta.injective
    rw [brauerAction_transport (presentation.factorRoot c) sources.real.identification
      (presentation.localH c)]
    change IrreducibleBrauerCharacter.twist sources.real.standardRoot sources.real.standardBase
      (canonicalReturn sources.real.identification (presentation.localH c) r⁻¹) =
        sources.real.standardBase
    obtain ⟨a, ha⟩ := sources.real.return_mem_fieldImage r⁻¹
    rw [← ha]
    exact PrincipalApplication.principalBrauer_fixed sources.current a sources.real.standardBase
      (sources.real.standardBase_supported sources.block sources.supported)
  have factor : ProductStabilizerFactorization (D := geometry.diagonalGroup (first m c))
      (E := presentation.ReturnGroup c) (presentation.localBase c) := by
    intro d r
    rw [fixed r]
    simp only [and_true]
  exact ⟨presentation.localBase c,
    ⟨1, one_smul (geometry.diagonalGroup (first m c)) (presentation.localBase c)⟩,
    factor, (semidirectStabilizerFactors_iff_productStabilizerFactorization
      (presentation.localD c) (presentation.localCompatible c)
      (presentation.localBase c)).mpr factor⟩


/-- All original types of factors, before representatives are chosen. -/
inductive FactorSource (presentation : Presentation geometry field root theta0) (c : C) : Type 1 where
  | typeA (source : TypeAFactorSources presentation c)
  | b2 (source : LeviRankTwo.Sources presentation c)
  | spin (source : SpinFactorSources presentation c)

structure RawFactorSources (presentation : Presentation geometry field root theta0) where
  factor : ∀ c, FactorSource presentation c

/-- Every original localBase orbit has a representative with both stabilizer
factorizations. Case coverage and all selector applications are internal. -/
theorem factor_representatives (presentation : Presentation geometry field root theta0)
    (sources : RawFactorSources presentation) (c : C) :
    FactorRepresentative presentation c := by
  cases sources.factor c with
  | typeA source => exact source.representative
  | b2 source => exact source.representative
  | spin source => exact source.representative

/-- Combine the same original N constituent, fixed by the entire stabilizer
of its original diagonal orbit, from the proved factor representatives. -/
theorem selected_constituent
    (geometry : PrimalData Frob Lbar leviStable m)
    (field : FieldData Frob Lbar E)
    (root : PrimeRegularRootEmbedding 2 k K (L0 Frob.toMonoidHom Lbar))
    (theta0 : IBr (rootN Frob Lbar root))
    (presentation : Presentation geometry field root theta0)
    (sources : RawFactorSources presentation) :
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
  have selected := factor_representatives presentation sources
  choose representative orbit productFactor semidirectFactor using selected
  exact TypeBLeviRepresentativeComponents.exists_actual_fixed_constituent
    (N Frob Lbar) (rootN Frob Lbar root) field.fieldOnGamma field.N_stable
    m geometry.factor geometry.diagonalGroup geometry.componentProduct geometry.diagonalAction
    geometry.imageProduct geometry.imageProduct_surjective geometry.groupSquare
    presentation.SH presentation.SD presentation.pairs presentation.factorRoot presentation.productSource
    presentation.phi presentation.normalises theta0 presentation.tau presentation.hH presentation.hD
    presentation.tau_generates representative orbit semidirectFactor

end Factors

section Components

variable {A : Type} [Group A] (Frob : MulAut A) (Lbar : Subgroup A)
  [Finite (fixedPoints Frob.toMonoidHom)]
  (leviStable : Lbar.map Frob.toMonoidHom = Lbar)
  {E : Type} [Group E] [Finite E] [IsCyclic E]
  (field : FieldData Frob Lbar E)
  {k K : Type} [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
  (iotaL : PrimeRegularRootEmbedding 2 k K (L Frob.toMonoidHom Lbar))
  (iotaN : PrimeRegularRootEmbedding 2 k K (L0 Frob.toMonoidHom Lbar))

/-- The geometric components and original constituent, with Spin sources
expressed by the underlying context data and published assumptions. -/
structure ComponentInput (theta0 : IBr (rootN Frob Lbar iotaN)) where
  C : Type
  [finiteC : Fintype C]
  m : C → ℕ
  geometry : PrimalData Frob Lbar leviStable m
  presentation : Presentation geometry field iotaN theta0
  factors : RawFactorSources presentation

attribute [instance] ComponentInput.finiteC

variable (iotaGamma : PrimeRegularRootEmbedding 2 k K (Gamma Frob Lbar))

local instance quotientCommutative : IsMulCommutative (Gamma Frob Lbar ⧸ N Frob Lbar) :=
  quotientN_abelian Frob Lbar

/-- Both characters are transported by the same original paired-Levi element.
Component return and Clifford transfer construct the full chosen-field
factorization. It is not a field of either source record. -/
theorem same_y_representative
    (raw : CliffordInput Frob Lbar iotaL iotaN iotaGamma)
    (psi0 : IBr (rootH Frob Lbar iotaL))
    (theta0 : IBr (rootN Frob Lbar iotaN))
    (occurs0 : Occurs (H Frob Lbar) (N Frob Lbar) (N_le_H Frob Lbar)
      (rootH Frob Lbar iotaL) (rootN Frob Lbar iotaN) psi0 theta0)
    (components : ComponentInput Frob Lbar leviStable field iotaN theta0) :
    letI := ambientBrauerAction (H Frob Lbar) (rootH Frob Lbar iotaL)
    letI := ambientBrauerAction (N Frob Lbar) (rootN Frob Lbar iotaN)
    letI := fieldBrauerAction (H Frob Lbar) (rootH Frob Lbar iotaL)
      field.fieldOnGamma field.H_stable
    ∃ (theta : IBr (rootN Frob Lbar iotaN)) (y : Gamma Frob Lbar)
        (psi : IBr (rootH Frob Lbar iotaL)),
      psi = y • psi0 ∧ theta = y • theta0 ∧
      Occurs (H Frob Lbar) (N Frob Lbar) (N_le_H Frob Lbar)
        (rootH Frob Lbar iotaL) (rootN Frob Lbar iotaN) psi theta ∧
      Formalisation.SemidirectStabilizerFactors field.fieldOnGamma
        (field_ambient_semidirect_compatible (H Frob Lbar) (rootH Frob Lbar iotaL)
          field.fieldOnGamma field.H_stable) psi := by
  let := ambientBrauerAction (H Frob Lbar) (rootH Frob Lbar iotaL)
  let := ambientBrauerAction (N Frob Lbar) (rootN Frob Lbar iotaN)
  let := fieldBrauerAction (H Frob Lbar) (rootH Frob Lbar iotaL)
    field.fieldOnGamma field.H_stable
  let := fieldBrauerAction (N Frob Lbar) (rootN Frob Lbar iotaN)
    field.fieldOnGamma field.N_stable
  obtain ⟨theta, selectedInOrbit, selectedFixed, _⟩ :=
    ManuscriptIBAW.TypeB.LeviSources.selected_constituent components.geometry field iotaN
      theta0 components.presentation components.factors
  obtain ⟨y, hy⟩ := MulAction.mem_orbit_iff.mp selectedInOrbit
  let psi : IBr (rootH Frob Lbar iotaL) := y • psi0
  have occurs : Occurs (H Frob Lbar) (N Frob Lbar) (N_le_H Frob Lbar)
      (rootH Frob Lbar iotaL) (rootN Frob Lbar iotaN) psi theta := by
    rw [← hy]
    exact occurs_ambient (H Frob Lbar) (N Frob Lbar) (N_le_H Frob Lbar)
      (rootH Frob Lbar iotaL) (rootN Frob Lbar iotaN) y psi0 theta0 occurs0
  have orbitEq := orbit_field_stabilizer_eq (N Frob Lbar) (rootN Frob Lbar iotaN)
    field.fieldOnGamma field.N_stable theta0 theta selectedInOrbit
  let EO := orbitFieldStabilizer (N Frob Lbar) (rootN Frob Lbar iotaN)
    field.fieldOnGamma field.N_stable theta
  let fieldO := field.fieldOnGamma.comp EO.subtype
  have hHO := fun e : EO => field.H_stable e.val
  have hNO := fun e : EO => field.N_stable e.val
  have thetaFixed : ∀ e : EO, (e : E) • theta = theta := by
    intro e
    have he : e.val ∈ orbitFieldStabilizer (N Frob Lbar) (rootN Frob Lbar iotaN)
        field.fieldOnGamma field.N_stable theta0 := by
      rw [← orbitEq]
      exact e.property
    exact selectedFixed ⟨e.val, he⟩
  have thetaFactorization :
      letI := fieldBrauerAction (N Frob Lbar) (rootN Frob Lbar iotaN) fieldO hNO
      Formalisation.SemidirectStabilizerFactors fieldO
        (field_ambient_semidirect_compatible (N Frob Lbar) (rootN Frob Lbar iotaN)
          fieldO hNO) theta := by
    intro x
    change x.left • ((x.right : E) • theta) = theta ↔
      x.left • theta = theta ∧ (x.right : E) • theta = theta
    rw [thetaFixed x.right]
    simp only [and_true]
  have localFactorization := representative_characteristic_two_clifford (E := EO)
    (H Frob Lbar) (N Frob Lbar) (N_le_H Frob Lbar) iotaGamma
    (rootH Frob Lbar iotaL) (rootN Frob Lbar iotaN) psi theta occurs
    (raw.iotaI theta) (raw.iotaA theta) raw.roots_N_G (raw.roots_A_G theta)
    raw.multiplicityFree raw.above raw.homogeneous raw.navarro87 (raw.navarro89 theta)
    raw.navarro820 (raw.roots_N_A theta) (raw.roots_I_A theta)
    fieldO hHO hNO thetaFactorization
  refine ⟨theta, y, psi, rfl, hy.symm, occurs, ?_⟩
  apply full_field_factorization (H Frob Lbar) (N Frob Lbar) (N_le_H Frob Lbar)
    (rootH Frob Lbar iotaL) (rootN Frob Lbar iotaN)
    field.fieldOnGamma field.H_stable field.N_stable raw.roots raw.navarro87 psi theta occurs
  intro g e
  exact localFactorization ⟨g, e⟩

end Components

variable {n p f : ℕ} {F A k K : Type}
  [Field F] [Finite F] [CharP F p] [Field A] [Algebra F A]
  [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
  {normF : NormSource n F} {normA : NormSource n A}
  {parameters : OddFieldParameters F p f}
  [Finite (SpecialClifford n F)] [NeZero f]
  (fs : FieldActionSource n F p f parameters normF)
  (iotaG : PrimeRegularRootEmbedding 2 k K (Spin n F normF))
  {BG : Type} [Fintype BG] {bG : BG → k[Spin n F normF]}
  (blocksG : BlockIdempotentDecomposition bG)
  (parametersG : ParameterSource fs (k := k))
  (Frob : MulAut (SpecialClifford n A))
  [Finite (fixedPoints Frob.toMonoidHom)]
  (points : CliffordFixedPointSource n p f F A normF normA Frob)

/-- The same Levi geometry and complete Jordan data, with Spin sources
constructed from their underlying contexts and the stated published results. -/
structure Source (s : SemisimpleIndex (n := n) (p := p) (F := F))
    extends LeviGeometry fs parametersG Frob points s where
  iotaL : PrimeRegularRootEmbedding 2 k K (L Frob.toMonoidHom Lbar)
  iotaN : PrimeRegularRootEmbedding 2 k K (L0 Frob.toMonoidHom Lbar)
  iotaGamma : PrimeRegularRootEmbedding 2 k K (Gamma Frob Lbar)
  BL : Type
  [finiteBL : Fintype BL]
  bL : BL → k[H Frob Lbar]
  blocksL : BlockIdempotentDecomposition bL
  eL : k[H Frob Lbar]
  centralL : IsMulCentral eL
  idempotentL : IsIdempotentElem eL
  gammaInvariant : ∀ g : Gamma Frob Lbar,
    MonoidAlgebra.mapDomainRingEquiv k (MulAut.conjNormal (H := H Frob Lbar) g) eL = eL
  fieldInvariant : ∀ e : parametersG.stabilizer s,
    MonoidAlgebra.mapDomainRingEquiv k
      (restrictAutomorphismHom (H Frob Lbar) field.fieldOnGamma field.H_stable e) eL = eL
  clifford : CliffordInput Frob Lbar iotaL iotaN iotaGamma
  constituent : ∀ psi : Packet (rootH Frob Lbar iotaL) blocksL eL,
    ∃ theta : IBr (rootN Frob Lbar iotaN),
      Occurs (H Frob Lbar) (N Frob Lbar) (N_le_H Frob Lbar)
        (rootH Frob Lbar iotaL) (rootN Frob Lbar iotaN) psi.val theta
  components : ∀ (psi : Packet (rootH Frob Lbar iotaL) blocksL eL)
      (theta : IBr (rootN Frob Lbar iotaN)),
    Occurs (H Frob Lbar) (N Frob Lbar) (N_le_H Frob Lbar)
      (rootH Frob Lbar iotaL) (rootN Frob Lbar iotaN) psi.val theta →
    ComponentInput Frob Lbar leviStable field iotaN theta
  jordan : Packet (rootH Frob Lbar iotaL) blocksL eL ≃
    Packet iotaG blocksG (parametersG.idempotent s)
  gamma_equivariant :
    let := packetMulAction (rootH Frob Lbar iotaL) blocksL eL
      (MulAut.conjNormal (H := H Frob Lbar)) gammaInvariant
    let := diagonalAction iotaG
    ∀ (g : Gamma Frob Lbar) (psi : Packet (rootH Frob Lbar iotaL) blocksL eL),
      (jordan (g • psi)).val = gammaEmbedding points Lbar g • (jordan psi).val
  field_equivariant :
    let := packetMulAction (rootH Frob Lbar iotaL) blocksL eL
      (restrictAutomorphismHom (H Frob Lbar) field.fieldOnGamma field.H_stable) fieldInvariant
    let := fieldAction fs iotaG
    ∀ (e : parametersG.stabilizer s) (psi : Packet (rootH Frob Lbar iotaL) blocksL eL),
      (jordan (e • psi)).val = (e : FieldGroup f) • (jordan psi).val
  blockCorrespondence : LiteralSupport eL ≃ LiteralSupport (parametersG.idempotent s)
  block_equation : ∀ psi : Packet (rootH Frob Lbar iotaL) blocksL eL,
    supportingBlock iotaG blocksG (jordan psi).val =
      (blockCorrespondence ⟨supportingBlock (rootH Frob Lbar iotaL) blocksL psi.val,
        psi.property⟩).val


end ManuscriptIBAW.TypeB.LeviSources

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
