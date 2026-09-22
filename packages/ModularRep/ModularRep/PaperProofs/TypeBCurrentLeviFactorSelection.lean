import ModularRep.PaperProofs.TypeBCurrentTypeASelection
import ModularRep.PaperProofs.TypeBLeviReturnB2Application
import ModularRep.PaperProofs.TypeBCurrentPrincipalResults

/-!
# Original Levi factor selection for the current Type B argument

The cases below retain the original factor, its prescribed local base, its
diagonal image and its entire cyclic return group. Type A uses the literal
FLZ/Clifford deduction; B2 uses the existing Feng--Malle separation theorem;
principal Spin factors use the established specified GGGR sources.

All matrix, common-adjoint and original-return identifications remain exact
E1/U inputs. Raw sources contain neither a selected representative nor a
standard selector. The final component deduction constructs a representative
fixed by the entire stabilizer of the original constituent orbit.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBCurrentLeviFactorSelection

open Formalisation ModularRep
open TypeBRegularLeviRationalCarriers TypeBComponentCycleNormalization
open TypeBRegularLeviCharacterActionAdapter TypeBComponentReturnOriginalCarriers
open EvenFieldAssumption53Relative TypeBLemma47LeviApplication
open TypeBLeviRepresentativeCarriers TypeBLeviRepresentativeSelection
open TypeBLeviRepresentativeFactorSelector TypeBComponentReturnCarrierTransport
open TypeBLeviReturnPowerSelection TypeBLeviReturnB2Application
open TypeBLeviReturnSpinPrincipalSelection TypeBCliffordCarriers
open TypeBCentralKernelBlockSource TypeBCentralKernelCarriers
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

/-- The desired local result, retaining the same original base and actors. -/
def FactorRepresentative (presentation : Presentation geometry field root theta0) (c : C) : Prop :=
  letI := rightAutomorphismAction (presentation.factorRoot c)
    (geometry.diagonalAction (first m c))
  letI := rightAutomorphismAction (presentation.factorRoot c) (presentation.localH c)
  ∃ psi : IBr (presentation.factorRoot c),
    psi ∈ MulAction.orbit (geometry.diagonalGroup (first m c)) (presentation.localBase c) ∧
    ProductStabilizerFactorization (D := geometry.diagonalGroup (first m c))
      (E := presentation.ReturnGroup c) psi ∧
    SemidirectStabilizerFactors (presentation.localD c) (presentation.localCompatible c) psi

/-- Literal type A pair and common-adjoint/return squares. Both adjoint image
directions are retained so the selected GL/GU translate returns to the
prescribed original orbit. -/
structure TypeAFactorSources (presentation : Presentation geometry field root theta0) (c : C) where
  Q : Type
  [groupQ : Group Q]
  [finiteQ : Finite Q]
  N : Subgroup Q
  [normalN : N.Normal]
  J : Type
  [groupJ : Group J]
  matrix : TypeBCurrentTypeASelection.MatrixModel N
  actors : TypeBCurrentTypeASelection.FieldGraphData N matrix
  identification : Base m geometry.factor c ≃* N
  adjoint : CommonAdjointData (J := J) identification
    (geometry.actualDiagonal (first m c)) (originalAction N)
  upperRoot : PrimeRegularRootEmbedding 2 k K Q
  source : TypeBCurrentTypeASelection.Sources N upperRoot
    ((presentation.factorRoot c).alongMulEquiv identification) matrix actors
  standardGenerator : actors.full
  generator_value : ∀ x : Base m geometry.factor c,
    identification (presentation.localH c (presentation.localGenerator c) x) =
      (standardGenerator : MulAut N) (identification x)

attribute [instance] TypeAFactorSources.groupQ TypeAFactorSources.finiteQ
  TypeAFactorSources.normalN TypeAFactorSources.groupJ

namespace TypeAFactorSources

variable {presentation : Presentation geometry field root theta0} {c : C}

/-- The standard selector is constructed here from FLZ and Clifford theory,
then transported by the accepted same-carrier theorem. -/
theorem representative (sources : TypeAFactorSources presentation c) :
    FactorRepresentative presentation c := by
  letI := rightAutomorphismAction (presentation.factorRoot c)
    (geometry.diagonalAction (first m c))
  letI := rightAutomorphismAction (presentation.factorRoot c) (presentation.localH c)
  have standard := TypeBCurrentTypeASelection.standard_selector_at sources.N
    sources.upperRoot ((presentation.factorRoot c).alongMulEquiv sources.identification)
    sources.matrix sources.actors sources.source
    (IrreducibleBrauerCharacter.equivAlongMulEquiv (presentation.factorRoot c)
      sources.identification (presentation.localBase c))
  obtain ⟨psi, orbit, factor⟩ := actual_factor_selector_at (presentation.factorRoot c)
    sources.identification (geometry.actualDiagonal (first m c))
    (originalAction sources.N) sources.adjoint (presentation.localH c)
    (presentation.localGenerator c) (presentation.localGenerator_generates c)
    sources.actors.full sources.standardGenerator sources.generator_value
    (presentation.localBase c) standard
  exact ⟨psi, orbit, factor,
    (semidirectStabilizerFactors_iff_productStabilizerFactorization
      (presentation.localD c) (presentation.localCompatible c) psi).mpr factor⟩

end TypeAFactorSources

/-- The already compiled B2 constructor's original component, coefficient,
Lang and adjoint sources, followed by the literal FM separation input. -/
structure B2FactorSources (presentation : Presentation geometry field root theta0) (c : C) where
  p : ℕ
  f : ℕ
  FQ : Type
  Astd : Type
  [fieldFQ : Field FQ]
  [finiteFQ : Finite FQ]
  [fieldAstd : Field Astd]
  [algebra : Algebra FQ Astd]
  [prime : Fact p.Prime]
  [charFQ : CharP FQ p]
  [charAstd : CharP Astd p]
  real : B2Realization presentation c p f FQ Astd
  coordinates : TypeBLeviReturnB2MatrixAction.MatrixKernelSource FQ
  diagonal : real.DiagonalSource coordinates
  odd : Odd (Nat.card FQ)
  separation : TypeBLeviReturnB2Diagonal.FengMalleSeparation
    coordinates odd real.standardRoot p

attribute [instance] B2FactorSources.fieldFQ B2FactorSources.finiteFQ
  B2FactorSources.fieldAstd B2FactorSources.algebra B2FactorSources.prime
  B2FactorSources.charFQ B2FactorSources.charAstd

namespace B2FactorSources

variable {presentation : Presentation geometry field root theta0} {c : C}

/-- Reuse the reviewed original B2 theorem and its identity representative. -/
theorem representative (sources : B2FactorSources presentation c) :
    FactorRepresentative presentation c := by
  obtain ⟨_, _, psi, _, orbit, factor, semidirect⟩ :=
    sources.real.b2_localBase_factorization sources.diagonal sources.odd sources.separation
  exact ⟨psi, orbit, factor, semidirect⟩

end B2FactorSources

/-- Specified principal Spin source data in every allowed rank. The block and
support refer to the original localBase; the standard block/root are computed
by the existing Spin realization. No character fixation is a field. -/
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
  context : TypeBCurrentPrincipalResults.GGGRContext real.coefficients.parameters rank Msys
    real.standardRoot (real.standardBlock block)
  raw : TypeBCurrentPrincipalResults.RankSources context
  fieldSources : TypeBCurrentPrincipalResults.FieldSources context real.fieldAction

attribute [instance] SpinFactorSources.fieldFQ SpinFactorSources.finiteFQ
  SpinFactorSources.charFQ SpinFactorSources.fieldAstd SpinFactorSources.algebraAstd
  SpinFactorSources.ringO SpinFactorSources.domainO SpinFactorSources.algebraO
  SpinFactorSources.finiteUpper SpinFactorSources.finiteLower SpinFactorSources.rootsUpper
  SpinFactorSources.rootsLower SpinFactorSources.finiteIrr SpinFactorSources.finiteBlocks

namespace SpinFactorSources

variable {presentation : Presentation geometry field root theta0} {c : C}

/-- Reuse principal GGGR fixation on the same transported supported character,
then pull it back through the established original Spin return square. -/
theorem representative (sources : SpinFactorSources presentation c) :
    FactorRepresentative presentation c := by
  letI := rightAutomorphismAction (presentation.factorRoot c)
    (geometry.diagonalAction (first m c))
  letI := rightAutomorphismAction (presentation.factorRoot c) (presentation.localH c)
  letI := rightAutomorphismAction sources.real.standardRoot
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
    exact TypeBCurrentPrincipalResults.principalBrauer_fixed sources.context sources.raw
      sources.real.fieldAction sources.fieldSources a sources.real.standardBase
      (sources.real.standardBase_supported sources.block sources.supported)
  have factor : ProductStabilizerFactorization (D := geometry.diagonalGroup (first m c))
      (E := presentation.ReturnGroup c) (presentation.localBase c) := by
    intro d r
    rw [fixed r]
    simp only [eq_self_iff_true, and_true]
  exact ⟨presentation.localBase c,
    ⟨1, one_smul (geometry.diagonalGroup (first m c)) (presentation.localBase c)⟩,
    factor, (semidirectStabilizerFactors_iff_productStabilizerFactorization
      (presentation.localD c) (presentation.localCompatible c)
      (presentation.localBase c)).mpr factor⟩

end SpinFactorSources

/-- Exhaustive original-factor alternatives. The Spin branch carries its
principal support; the degree-two Type A branch includes SL2(3). -/
inductive FactorSource (presentation : Presentation geometry field root theta0) (c : C) : Type 1 where
  | typeA (source : TypeAFactorSources presentation c)
  | b2 (source : B2FactorSources presentation c)
  | spin (source : SpinFactorSources presentation c)

/-- Specified component classification supplies one of the three raw branches
for every cycle; this record supplies no local representative. -/
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

end ModularRep.PaperProofs.TypeBCurrentLeviFactorSelection


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
