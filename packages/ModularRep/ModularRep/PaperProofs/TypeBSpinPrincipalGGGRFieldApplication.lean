import ModularRep.PaperProofs.TypeBSpinPrincipalGGGRBasisBinding
import ModularRep.PaperProofs.TypeBPrincipalSpinMatrixFieldTransport
import ModularRep.PaperProofs.TypeBIndexedRationalFieldHandoff

/-!
# Actual rank-three Spin GGGR to principal Brauer field fixation

Current manuscript labels: rational-field Lemma4.9, GGGR-rank Proposition4.10,
principal-selector Corollary4.11. Earlier Lean filenames retain older numbers.

The old D, B and projection-naturality records are constructed on the SAME
specified Spin/root/block and actual class-indexed gamma family. No GGGR basis,
Brauer fixation, matrix fixation or iBAW conclusion is an external input.
The final theorem discharges the free Spin-fixation premise of the existing
Spin-to-matrix transport.

The published algebraic finite-point, geometric/component and cyclotomic source
realizations remain explicit obligations. This is the field-fixation part of
Corollary4.11 at rank three, not its full BAW-goodness conclusion or the
rational-span statement of Proposition4.10.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBSpinPrincipalGGGRFieldApplication

open ModularRep OrdinaryIrreducibleCharacter TypeBCliffordCarriers
open TypeBCentralKernelBlockSource TypeBSpinRationalUnipotentClassBinding
open TypeBSpinGGGRPrincipalSeriesBinding TypeBSpinPrincipalGGGRBasisBinding
open TypeBSpinPrincipalDecompositionBinding TypeBSpinPrincipalProjectiveBinding
open TypeBSpinGGGRProjectivityBinding TypeBPrincipalSelectorCorollary413SourceInstantiation
open TypeBGGGRRankProposition412Corollary413Bridge
open TypeBIndexedRationalFieldHandoff
open scoped MonoidAlgebra

variable {r f : ℕ} {F K O k : Type}
  [Field F] [Finite F] [CharP F r] [Field K] [CharZero K]
  {N : NormSource 3 F} [Finite (Spin 3 F N)]
  [HasEnoughRootsOfUnity K (Nat.card (Spin 3 F N))]
  (orthogonality : OrdinaryOrthogonalitySource (N := N) (K := K))

local instance finiteTypeFintype (X : Type) [Finite X] : Fintype X :=
  Fintype.ofFinite X

variable [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k]
  (parameters : OddFieldParameters F r f)
  (S : FieldActionSource 3 F r f parameters N)
  {GeometricClass : Type}
  (geometricClass : UnipotentClass (r := r) (N := N) → GeometricClass)
  (geometricStable : GeometricFieldStable parameters S geometricClass)
  (ComponentGroup : GeometricClass → Type) [∀ C, Group (ComponentGroup C)]
  (inner : ∀ C, ComponentGroup C)
  (gamma : UnipotentClass (r := r) (N := N) → Spin 3 F N → K)
  (rational : RationalGGGRSource (K := K) parameters (show 3 ≤ 3 from le_rfl) S
    geometricClass geometricStable ComponentGroup inner)
  (gamma_eq : rational.gamma = gamma)
  (rationalSeries : TypeBConformalDualCarriers.PCSp F 3 → Irr K (Spin 3 F N) → Prop)
  (quasiIsolated : TypeBConformalDualCarriers.PCSp F 3 → Prop)
  (normalizedDual : Irr K (Spin 3 F N) → Irr K (Spin 3 F N))
  (unipotentSupport : Irr K (Spin 3 F N) → GeometricClass → Prop)
  (raw : RankThreeChanebSource parameters geometricClass ComponentGroup gamma
    rationalSeries quasiIsolated normalizedDual unipotentSupport)
  (Msys : ModularSystem 2 K O k)
  (iota : PrimeRegularRootEmbedding 2 k K (Spin 3 F N))
  (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
  (b : LiteralPrimitiveBlock k (Spin 3 F N)) (principal : IsPrincipal b)
  [Fintype (LiteralPrimitiveBlock k (Spin 3 F N))]
  (blocks : BlockIdempotentDecomposition
    (fun c : LiteralPrimitiveBlock k (Spin 3 F N) => c.val))
  (ordinary : OrdinaryBlockSource Msys iota blocks)
  (columns : DecompositionColumnIndependenceSource Msys iota)
  (series : PrincipalSeriesCertificate parameters (show 3 ≤ 3 from le_rfl)
    ordinary.ordinaryBlock b principal rationalSeries quasiIsolated normalizedDual)
  {m : ℕ} (classIndex : Fin m ≃ UnipotentClass (r := r) (N := N))
  (closure : GeometricClass → GeometricClass → Prop)
  (ordering : GeometricOrdering geometricClass classIndex closure)
  (waveFront : WaveFrontClosureCertificate parameters geometricClass gamma
    normalizedDual unipotentSupport closure)
  (count : PrincipalRationalClassCount parameters iota b principal)
  (induction : GGGRInductionSource parameters (show 3 ≤ 3 from le_rfl) gamma)
  (expansion : letI : Finite (Irr K (Spin 3 F N)) := ordinary_finite orthogonality
    OddInductionExpansionCertificate Msys iota hcompat)

include raw orthogonality hcompat principal ordinary columns series ordering
  waveFront count induction expansion rational gamma_eq in
/-- The specified principal Spin Brauer characters are fixed, using the
constructed GGGR basis and SAME actual rational/component/field data. -/
theorem principalBrauer_fixed :
    ∀ (e : FieldGroup f) (theta : IBr iota), Supported iota b theta →
      IrreducibleBrauerCharacter.twist iota theta (spinFieldAction 3 F S e) = theta := by
  letI : Finite (Irr K (Spin 3 F N)) := ordinary_finite orthogonality
  let D := TypeBSpinPrincipalGGGRBasisBinding.basisSource
    (parameters := parameters) (geometricClass := geometricClass)
    (ComponentGroup := ComponentGroup) (gamma := gamma) (rationalSeries := rationalSeries)
    (quasiIsolated := quasiIsolated) (normalizedDual := normalizedDual)
    (unipotentSupport := unipotentSupport) (raw := raw)
    (orthogonality := orthogonality) (Msys := Msys) (iota := iota) (hcompat := hcompat)
    (b := b) (principal := principal) (blocks := blocks) (ordinary := ordinary)
    (columns := columns) (series := series) (classIndex := classIndex)
    (closure := closure) (ordering := ordering) (waveFront := waveFront) (count := count)
    (induction := induction) (expansion := expansion)
  let field := spinRightFieldHom parameters S
  let brauerStable : ∀ e : FieldGroup f, ∀ phi : IBr iota, Supported iota b phi →
      Supported iota b (IrreducibleBrauerCharacter.twist iota phi (field e).unop) :=
    fun e phi supported =>
      TypeBCentralKernelPrincipalStability.supported_principal_twist
        blocks iota b principal (field e).unop phi supported
  let projectiveStable := TypeBSpinPrincipalProjectiveBinding.projectiveStable
    Msys iota hcompat field b brauerStable
  let B := TypeBSpinPrincipalProjectiveBinding.projectiveBrauerFormulaSource
    orthogonality Msys iota hcompat field b brauerStable columns
  let P : PrincipalProjectionFieldSource field D := by
    refine ⟨?_⟩
    intro e x
    change functionTwistLinearEquiv (field e).unop
        (principalProjection Msys iota b blocks ordinary x) =
      principalProjection Msys iota b blocks ordinary
        (functionTwistLinearEquiv (field e).unop x)
    exact (TypeBSpinPrincipalProjectiveBinding.principalProjection_natural
      Msys iota hcompat field b brauerStable blocks ordinary e x).symm
  letI : ∀ C, MulAction (FieldGroup f) (RationalFibre geometricClass C) :=
    fun C => rationalFibreFieldAction parameters S geometricClass geometricStable C
  let indexed := TypeBSpinRationalUnipotentClassBinding.indexedSource
    parameters S geometricClass geometricStable (show 3 ≤ 3 from le_rfl)
      ComponentGroup inner rational D classIndex (by
        intro j
        change gamma (classIndex j) = rational.gamma (classIndex j)
        rw [gamma_eq])
  have fixed := indexed.corollary_4_13_from_indexed_literal_lemma_4_11
    iota (Supported iota b) brauerStable projectiveStable B P
  letI := principalBrauerFieldAction field iota (Supported iota b) brauerStable
  intro e theta supported
  have h := fixed e ⟨theta, supported⟩
  have values := congrArg Subtype.val h
  change IrreducibleBrauerCharacter.twist iota theta (field e).unop = theta at values
  simpa only [field, spinRightFieldHom_unop] using values

variable
  (C : TypeBCliffordOrthogonalSourceBinding.Source 3 F r f parameters
    (show 3 ≤ 3 from le_rfl) N)
  (centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource 3 r f F N)
  (oldRoot : PrimeRegularRootEmbedding 2 k K (TypeBSpinCoverSource.Omega N))
  (matrixRoot : PrimeRegularRootEmbedding 2 k K (TypeBOrthogonalOmegaCarriers.Omega 3 F))
  (matrixLifts : matrixRoot.lift = oldRoot.lift)
  (spinLifts : iota.lift = oldRoot.lift)
  (kernel : TypeBCentralKernelBrauerInflation.Navarro232Principle 2 k)
  (regular : TypeBCentralKernelBrauerInflation.PrimeRegularQuotientLiftPrinciple.{0} 2)
  (centralBlocks : NavarroCentralBlockPrinciple 2 k)
  [Fintype (LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega 3 F))]
  (matrixBlocks : BlockIdempotentDecomposition
    (fun c : LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega 3 F) => c.val))
  (matrixBlock : LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega 3 F))
  (matrixPrincipal : IsPrincipal matrixBlock)

include raw orthogonality hcompat principal ordinary columns series ordering
  waveFront count induction expansion rational gamma_eq matrixLifts spinLifts kernel
  regular centralBlocks matrixBlocks centre matrixPrincipal in
/-- Actual GGGR-to-matrix endpoint: the former Spin-fixation transport
premise is discharged by the specified source construction above. -/
theorem matrixPrincipalBrauer_fixed :
    ∀ (e : FieldGroup f) (phi : IBr matrixRoot), Supported matrixRoot matrixBlock phi →
      IrreducibleBrauerCharacter.twist matrixRoot phi
        (TypeBCliffordOrthogonalFullFieldBinding.omegaFieldAction S
          (show 3 ≤ 3 from le_rfl) C e) = phi := by
  apply TypeBPrincipalSpinMatrixFieldTransport.matrix_fixed_of_spin_fixed
    parameters (show 3 ≤ 3 from le_rfl) C centre oldRoot matrixRoot matrixLifts
    kernel regular centralBlocks S matrixBlocks iota spinLifts b principal matrixBlock matrixPrincipal
  exact principalBrauer_fixed
    (parameters := parameters) (geometricClass := geometricClass)
    (ComponentGroup := ComponentGroup) (gamma := gamma) (rationalSeries := rationalSeries)
    (quasiIsolated := quasiIsolated) (normalizedDual := normalizedDual)
    (unipotentSupport := unipotentSupport) (raw := raw)
    (orthogonality := orthogonality) (Msys := Msys) (iota := iota) (hcompat := hcompat)
    (b := b) (principal := principal) (blocks := blocks) (ordinary := ordinary)
    (columns := columns) (series := series) (classIndex := classIndex)
    (closure := closure) (ordering := ordering) (waveFront := waveFront) (count := count)
    (induction := induction) (expansion := expansion)
    (S := S) (geometricStable := geometricStable) (inner := inner)
    (rational := rational) (gamma_eq := gamma_eq)

end ModularRep.PaperProofs.TypeBSpinPrincipalGGGRFieldApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
