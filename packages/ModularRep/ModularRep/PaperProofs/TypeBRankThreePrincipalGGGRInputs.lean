import ModularRep.PaperProofs.TypeBSpinPrincipalGGGRFieldApplication
import ModularRep.PaperProofs.TypeBPrincipalRootLiftBinding

/-!
# Raw GGGR inputs on a prescribed matrix principal block

The matrix root, specified decomposition, principal block and field actor
are indices of this package. Its fields retain the independent inputs of
the checked specified Spin GGGR construction and central-two transport.
The matrix Brauer fixation theorem applies that construction directly.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalGGGRInputs

open ModularRep OrdinaryIrreducibleCharacter TypeBCliffordCarriers
open TypeBCentralKernelBlockSource TypeBSpinRationalUnipotentClassBinding
open TypeBSpinGGGRPrincipalSeriesBinding TypeBSpinPrincipalGGGRBasisBinding
open TypeBSpinPrincipalDecompositionBinding TypeBSpinPrincipalProjectiveBinding
open TypeBSpinGGGRProjectivityBinding TypeBPrincipalSelectorCorollary413SourceInstantiation
open TypeBGGGRRankProposition412Corollary413Bridge
open TypeBIndexedRationalFieldHandoff
open scoped MonoidAlgebra

local instance finiteTypeFintype (X : Type) [Finite X] : Fintype X :=
  Fintype.ofFinite X

variable {r f : ℕ} {F K O k : Type}
  [Field F] [Finite F] [CharP F r] [Field K] [CharZero K]
  {N : NormSource 3 F} [Finite (Spin 3 F N)]
  [HasEnoughRootsOfUnity K (Nat.card (Spin 3 F N))]
  [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k]
  (parameters : OddFieldParameters F r f)
  (fieldSource : FieldActionSource 3 F r f parameters N)
  (Msys : ModularSystem 2 K O k)
  (C : TypeBCliffordOrthogonalSourceBinding.Source 3 F r f parameters
    (show 3 ≤ 3 from le_rfl) N)
  (matrixRoot : PrimeRegularRootEmbedding 2 k K (TypeBOrthogonalOmegaCarriers.Omega 3 F))
  [Fintype (LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega 3 F))]
  (matrixBlocks : BlockIdempotentDecomposition
    (fun c : LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega 3 F) => c.val))
  (matrixBlock : LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega 3 F))
  (matrixPrincipal : IsPrincipal matrixBlock)

/-- Independent geometric, ordinary, reduction and central transport inputs
on the same coefficients and prescribed matrix principal block. -/
structure Inputs
    {r f : ℕ} {F K O k : Type}
    [Field F] [Finite F] [CharP F r] [Field K] [CharZero K]
    {N : NormSource 3 F} [Finite (Spin 3 F N)]
    [HasEnoughRootsOfUnity K (Nat.card (Spin 3 F N))]
    [CommRing O] [IsDomain O] [Field k] [Algebra O K]
    [CharP k 2] [IsAlgClosed k]
    (parameters : OddFieldParameters F r f)
    (fieldSource : FieldActionSource 3 F r f parameters N)
    (Msys : ModularSystem 2 K O k)
    (C : TypeBCliffordOrthogonalSourceBinding.Source 3 F r f parameters
      (show 3 ≤ 3 from le_rfl) N)
    (matrixRoot : PrimeRegularRootEmbedding 2 k K (TypeBOrthogonalOmegaCarriers.Omega 3 F))
    [Fintype (LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega 3 F))]
    (matrixBlocks : BlockIdempotentDecomposition
      (fun c : LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega 3 F) => c.val))
    (matrixBlock : LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega 3 F))
    (matrixPrincipal : IsPrincipal matrixBlock) where
  orthogonality : OrdinaryOrthogonalitySource (N := N) (K := K)
  GeometricClass : Type
  geometricClass : UnipotentClass (r := r) (N := N) → GeometricClass
  geometricStable : GeometricFieldStable parameters fieldSource geometricClass
  ComponentGroup : GeometricClass → Type
  [componentGroups : ∀ c, Group (ComponentGroup c)]
  inner : ∀ c, ComponentGroup c
  gamma : UnipotentClass (r := r) (N := N) → Spin 3 F N → K
  rational : RationalGGGRSource (K := K) parameters (show 3 ≤ 3 from le_rfl)
    fieldSource geometricClass geometricStable ComponentGroup inner
  gamma_eq : rational.gamma = gamma
  rationalSeries : TypeBConformalDualCarriers.PCSp F 3 → Irr K (Spin 3 F N) → Prop
  quasiIsolated : TypeBConformalDualCarriers.PCSp F 3 → Prop
  normalizedDual : Irr K (Spin 3 F N) → Irr K (Spin 3 F N)
  unipotentSupport : Irr K (Spin 3 F N) → GeometricClass → Prop
  raw : RankThreeChanebSource parameters geometricClass ComponentGroup gamma
    rationalSeries quasiIsolated normalizedDual unipotentSupport
  iota : PrimeRegularRootEmbedding 2 k K (Spin 3 F N)
  hcompat : StableReductionBrauerCharacterCompatibility Msys iota
  b : LiteralPrimitiveBlock k (Spin 3 F N)
  principal : IsPrincipal b
  [spinBlockFintype : Fintype (LiteralPrimitiveBlock k (Spin 3 F N))]
  blocks : BlockIdempotentDecomposition
    (fun c : LiteralPrimitiveBlock k (Spin 3 F N) => c.val)
  ordinary : OrdinaryBlockSource Msys iota blocks
  columns : DecompositionColumnIndependenceSource Msys iota
  series : PrincipalSeriesCertificate parameters (show 3 ≤ 3 from le_rfl)
    ordinary.ordinaryBlock b principal rationalSeries quasiIsolated normalizedDual
  m : ℕ
  classIndex : Fin m ≃ UnipotentClass (r := r) (N := N)
  closure : GeometricClass → GeometricClass → Prop
  ordering : GeometricOrdering geometricClass classIndex closure
  waveFront : WaveFrontClosureCertificate parameters geometricClass gamma
    normalizedDual unipotentSupport closure
  count : PrincipalRationalClassCount parameters iota b principal
  induction : GGGRInductionSource parameters (show 3 ≤ 3 from le_rfl) gamma
  expansion : letI : Finite (Irr K (Spin 3 F N)) := ordinary_finite orthogonality
    OddInductionExpansionCertificate Msys iota hcompat
  centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource 3 r f F N
  oldRoot : PrimeRegularRootEmbedding 2 k K (TypeBSpinCoverSource.Omega N)
  matrixCompatible : TypeBLocalReductionInstantiation.RootResidueCompatible Msys matrixRoot
  oldCompatible : TypeBLocalReductionInstantiation.RootResidueCompatible Msys oldRoot
  spinCompatible : TypeBLocalReductionInstantiation.RootResidueCompatible Msys iota
  kernel : TypeBCentralKernelBrauerInflation.Navarro232Principle 2 k
  regular : TypeBCentralKernelBrauerInflation.PrimeRegularQuotientLiftPrinciple.{0} 2
  centralBlocks : NavarroCentralBlockPrinciple 2 k

variable
  (inputs : Inputs parameters fieldSource Msys C matrixRoot matrixBlocks matrixBlock
    matrixPrincipal)

include inputs matrixBlocks matrixPrincipal in
/-- The checked specified GGGR construction fixes the prescribed matrix
principal Brauer fibre under every element of the same field group. -/
theorem matrixPrincipalBrauer_fixed
    (e : FieldGroup f) (phi : IBr matrixRoot)
    (supported : Supported matrixRoot matrixBlock phi) :
    IrreducibleBrauerCharacter.twist matrixRoot phi
      (TypeBCliffordOrthogonalFullFieldBinding.omegaFieldAction fieldSource
        (show 3 ≤ 3 from le_rfl) C e) = phi := by
  letI := inputs.componentGroups
  letI := inputs.spinBlockFintype
  have matrixLifts : matrixRoot.lift = inputs.oldRoot.lift :=
    TypeBPrincipalRootLiftBinding.matrixLifts_of_residue
      parameters (show 3 ≤ 3 from le_rfl) inputs.centre C Msys matrixRoot inputs.oldRoot
      inputs.matrixCompatible inputs.oldCompatible
  have spinLifts : inputs.iota.lift = inputs.oldRoot.lift :=
    TypeBPrincipalRootLiftBinding.spinLifts_of_residue
      parameters (show 3 ≤ 3 from le_rfl) inputs.centre Msys inputs.iota inputs.oldRoot
      inputs.spinCompatible inputs.oldCompatible
  exact TypeBSpinPrincipalGGGRFieldApplication.matrixPrincipalBrauer_fixed
    (orthogonality := inputs.orthogonality) (parameters := parameters)
    (S := fieldSource) (geometricClass := inputs.geometricClass)
    (geometricStable := inputs.geometricStable) (ComponentGroup := inputs.ComponentGroup)
    (inner := inputs.inner) (gamma := inputs.gamma) (rational := inputs.rational)
    (gamma_eq := inputs.gamma_eq) (rationalSeries := inputs.rationalSeries)
    (quasiIsolated := inputs.quasiIsolated) (normalizedDual := inputs.normalizedDual)
    (unipotentSupport := inputs.unipotentSupport) (raw := inputs.raw)
    (Msys := Msys) (iota := inputs.iota) (hcompat := inputs.hcompat)
    (b := inputs.b) (principal := inputs.principal) (blocks := inputs.blocks)
    (ordinary := inputs.ordinary) (columns := inputs.columns) (series := inputs.series)
    (classIndex := inputs.classIndex) (closure := inputs.closure)
    (ordering := inputs.ordering) (waveFront := inputs.waveFront) (count := inputs.count)
    (induction := inputs.induction) (expansion := inputs.expansion)
    (C := C) (centre := inputs.centre) (oldRoot := inputs.oldRoot)
    (matrixRoot := matrixRoot) (matrixLifts := matrixLifts)
    (spinLifts := spinLifts) (kernel := inputs.kernel) (regular := inputs.regular)
    (centralBlocks := inputs.centralBlocks) (matrixBlocks := matrixBlocks)
    (matrixBlock := matrixBlock) (matrixPrincipal := matrixPrincipal) e phi supported

end ModularRep.PaperProofs.TypeBRankThreePrincipalGGGRInputs


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
