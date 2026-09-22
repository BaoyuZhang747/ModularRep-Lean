import ModularRep.PaperProofs.TypeBAllRankGGGRCarriers
import ModularRep.PaperProofs.TypeBAllRankGGGRSelection
import ModularRep.PaperProofs.TypeBAllRankGGGRBasisPhysical

/-!
# The specified higher-rank Spin GGGR rational-basis deduction

This is the n >= 4 deduction of `prop:type-b-gggr-rank`. All rows, lower
nonabelian matrices and the specified basis source are constructed inside
the proof. The columns and final Q-basis vectors retain the same exhaustive
index of actual unipotent conjugacy classes in the literal norm kernel.

The external sources are the class/component parametrisations, the upper
Taylor family and restriction facts, the abelian Chaneb identity, actual
series/support/closure facts, and the existing modular-system/PIM inputs.
Their algebraic realizations remain explicitly conditional; neither the
GGGR basis nor the selected nonabelian lower family is an input.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBAllRankGGGRApplication

open ModularRep OrdinaryIrreducibleCharacter TypeBCliffordCarriers
open TypeBCentralKernelBlockSource TypeBSpinPrincipalDecompositionBinding
open TypeBSpinPrincipalProjectiveBinding TypeBSpinRationalUnipotentClassBinding
open TypeBSpinGGGRPrincipalSeriesBinding TypeBSpinGGGRProjectivityBinding
open TypeBSpinGGGRRationalSpanBinding TypeBAllRankGGGRFibres
open TypeBAllRankGGGREntries TypeBAllRankGGGR.BasisPhysical
open scoped MonoidAlgebra

variable {n r f : ℕ} {F K O k : Type}
  [Field F] [Finite F] [CharP F r] [Field K] [CharZero K]
  [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k]
  {N : NormSource n F} (finiteClifford : FiniteCliffordSource n F)

variable [HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F))]

/-- The actual manuscript deduction: principal ordinary rows, a permutation
within each geometric class, the diagonal and triangular equations, and a
Q-basis consisting literally of the original principal GGGR projections.
Lower finiteness, splitting and finite ordinary-character scope are derived
from the same upper Clifford realization and ordinary orthogonality.
-/
theorem manuscript_deduction :
    letI : Finite (SpecialClifford n F) := specialClifford_finite n F finiteClifford
    letI : Finite (Spin n F N) := TypeBAllRankGGGRCarriers.spin_finite N finiteClifford
    letI : HasEnoughRootsOfUnity K (Nat.card (Spin n F N)) :=
      TypeBAllRankGGGRCarriers.spin_roots_of_upper N
    ∀ (orthogonality : OrdinaryOrthogonalitySource (N := N) (K := K)),
    letI : Finite (Irr K (Spin n F N)) := ordinary_finite orthogonality
    ∀ {parameters : OddFieldParameters F r f} {rank : 4 ≤ n}
      {GeometricClass : Type}
      {geometricClass : UnipotentClass (r := r) (N := N) → GeometricClass}
      {upperGeometricClass : UpperUnipotentClass (n := n) (F := F) (r := r) → GeometricClass}
      {geometric_square : ∀ c, upperGeometricClass (upperClassMap c) = geometricClass c}
      {ComponentGroup : GeometricClass → Type} [∀ C, Group (ComponentGroup C)]
      {gamma : UnipotentClass (r := r) (N := N) → Spin n F N → K}
      {upperDual : Irr K (SpecialClifford n F) → Irr K (SpecialClifford n F)}
      {lowerDual : Irr K (Spin n F N) → Irr K (Spin n F N)}
      {rationalSeries : TypeBConformalDualCarriers.PCSp F n → Irr K (Spin n F N) → Prop}
      {quasiIsolated : TypeBConformalDualCarriers.PCSp F n → Prop}
      {unipotentSupport : Irr K (Spin n F N) → GeometricClass → Prop}
      {Msys : ModularSystem 2 K O k}
      {iota : PrimeRegularRootEmbedding 2 k K (Spin n F N)}
      {hcompat : StableReductionBrauerCharacterCompatibility Msys iota}
      {b : LiteralPrimitiveBlock k (Spin n F N)} {principal : IsPrincipal b}
      [Fintype (LiteralPrimitiveBlock k (Spin n F N))]
      {blocks : BlockIdempotentDecomposition
        (fun c : LiteralPrimitiveBlock k (Spin n F N) => c.val)}
      {ordinary : OrdinaryBlockSource Msys iota blocks}
      (columns : DecompositionColumnIndependenceSource Msys iota)
      (series : PrincipalSeriesCertificate parameters
        (Nat.le_trans (show 3 ≤ 4 by decide) rank)
        ordinary.ordinaryBlock b principal rationalSeries quasiIsolated lowerDual)
      {m : ℕ} (classIndex : Fin m ≃ UnipotentClass (r := r) (N := N))
      {closure : GeometricClass → GeometricClass → Prop}
      (ordering : GeometricOrdering geometricClass classIndex closure)
      (waveFront : WaveFrontClosureCertificate parameters rank geometricClass gamma
        lowerDual unipotentSupport closure)
      (count : PrincipalRationalClassCount parameters rank iota b principal)
      (induction : GGGRInductionSource parameters
        (Nat.le_trans (show 3 ≤ 4 by decide) rank) gamma)
      (expansion : OddInductionExpansionCertificate Msys iota hcompat)
      (reciprocity : FrobeniusReciprocitySource (N := N) (K := K))
      (sources : ∀ C, Nonempty (RationalFibre geometricClass C) →
        TypeBAllRankGGGRSelection.LocalSources (geometricClass := geometricClass)
          (upperGeometricClass := upperGeometricClass) (geometric_square := geometric_square)
          (ComponentGroup := ComponentGroup) (gamma := gamma) (upperDual := upperDual)
          (lowerDual := lowerDual) (rationalSeries := rationalSeries)
          (quasiIsolated := quasiIsolated) (unipotentSupport := unipotentSupport)
          (parameters := parameters) (rank := rank) C),
    ∃ rho : Fin m → Irr K (Spin n F N),
      (∀ i, ordinary.ordinaryBlock (rho i) = b) ∧
      ∃ p : Equiv.Perm (Fin m),
        (∀ i, geometricClass (classIndex (p i)) = geometricClass (classIndex i)) ∧
        (∀ i j, geometricClass (classIndex i) = geometricClass (classIndex j) →
          scalarProductRight (rho (p i)).val
            (principalProjection Msys iota b blocks ordinary (gamma (classIndex j))) =
              if i = j then 1 else 0) ∧
        (∀ i j, ordering.code (geometricClass (classIndex i)) <
            ordering.code (geometricClass (classIndex j)) →
          scalarProductRight (rho (p i)).val
            (principalProjection Msys iota b blocks ordinary (gamma (classIndex j))) = 0) ∧
        ∃ B : Module.Basis (Fin m) ℚ (projectiveQSpan Msys iota b),
          ∀ j, (B j).val =
            principalProjection Msys iota b blocks ordinary (gamma (classIndex j)) := by
  classical
  letI : Finite (SpecialClifford n F) := specialClifford_finite n F finiteClifford
  letI : Finite (Spin n F N) := TypeBAllRankGGGRCarriers.spin_finite N finiteClifford
  letI : HasEnoughRootsOfUnity K (Nat.card (Spin n F N)) :=
    TypeBAllRankGGGRCarriers.spin_roots_of_upper N
  intro orthogonality
  letI : Finite (Irr K (Spin n F N)) := ordinary_finite orthogonality
  intro parameters rank GeometricClass geometricClass upperGeometricClass geometric_square
    ComponentGroup componentInstances gamma upperDual lowerDual rationalSeries quasiIsolated
    unipotentSupport Msys iota hcompat b principal blockInstances blocks ordinary columns series
    m classIndex closure ordering waveFront count induction expansion reciprocity sources
  let positive := nonnegative (parameters := parameters) (rank := rank)
    (induction := induction) (orthogonality := orthogonality) (Msys := Msys)
    (iota := iota) (hcompat := hcompat) (expansion := expansion)
  let before := TypeBAllRankGGGRSelection.beforeDual positive reciprocity sources
  let label := TypeBAllRankGGGRSelection.classLabel positive reciprocity sources
  have label_quasi : ∀ c, quasiIsolated (label (geometricClass c)) :=
    TypeBAllRankGGGRSelection.label_quasiIsolated positive reciprocity sources
  have rows_series : ∀ c, rationalSeries (label (geometricClass c)) (before c) :=
    TypeBAllRankGGGRSelection.beforeDual_series positive reciprocity sources
  have rows_support : ∀ c, unipotentSupport (before c) (geometricClass c) :=
    TypeBAllRankGGGRSelection.beforeDual_support positive reciprocity sources
  let diagonal := TypeBAllRankGGGRSelection.diagonalCases positive reciprocity sources
  let D := basisSource (parameters := parameters) (rank := rank)
    (gamma := gamma) (beforeDual := before) (lowerDual := lowerDual)
    (geometricClass := geometricClass) (classLabel := label)
    (unipotentSupport := unipotentSupport)
    (orthogonality := orthogonality) (Msys := Msys) (iota := iota) (hcompat := hcompat)
    (b := b) (principal := principal) (blocks := blocks) (ordinary := ordinary)
    (columns := columns) (series := series) (classIndex := classIndex) (ordering := ordering)
    (label_quasiIsolated := label_quasi) (beforeDual_series := rows_series)
    (beforeDual_support := rows_support) (waveFront := waveFront) (count := count)
    (induction := induction) (expansion := expansion) diagonal
  let B := TypeBAllRankGGGR.Basis.rationalGGGRBasisOfPhysicalSource
    (parameters := parameters) (rank := rank) (orthogonality := orthogonality)
    (columns := columns) (Msys := Msys) (iota := iota) (hcompat := hcompat)
    (b := b) (blocks := blocks) (ordinary := ordinary) (gamma := gamma)
    (classIndex := classIndex) (induction := induction) (expansion := expansion)
    D (fun _ => rfl) rfl
  refine ⟨fun i => lowerDual (before (classIndex i)), ?_, D.rowPermutation,
    ?_, ?_, ?_, B, ?_⟩
  · intro i
    exact selected_principal (parameters := parameters) (rank := rank)
      (beforeDual := before) (lowerDual := lowerDual)
      (geometricClass := geometricClass) (classLabel := label)
      (series := series) (label_quasiIsolated := label_quasi)
      (beforeDual_series := rows_series) (classIndex i)
  · intro i
    exact ordering.code_injective (D.rowPermutation_preserves_class i)
  · intro i j same
    change D.scalarProductMatrix (D.rowPermutation i) j = if i = j then 1 else 0
    exact D.closurePermutationData.same_class_entry i j (congrArg ordering.code same)
  · intro i j higher
    change D.scalarProductMatrix (D.rowPermutation i) j = 0
    apply D.closurePermutationData.closure_vanishing i j
    change D.geometricClass (D.rowPermutation i) < D.geometricClass j
    rw [D.rowPermutation_preserves_class]
    exact higher
  · intro j
    exact TypeBAllRankGGGR.Basis.rationalGGGRBasisOfPhysicalSource_apply
      (parameters := parameters) (rank := rank) (orthogonality := orthogonality)
      (columns := columns) (Msys := Msys) (iota := iota) (hcompat := hcompat)
      (b := b) (blocks := blocks) (ordinary := ordinary) (gamma := gamma)
      (classIndex := classIndex) (induction := induction) (expansion := expansion)
      D (fun _ => rfl) rfl j

end ModularRep.PaperProofs.TypeBAllRankGGGRApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
