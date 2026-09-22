import ModularRep.PaperProofs.TypeBSpinPrincipalGGGRBasisBinding
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The literal rational span of the principal Spin PIM functions

The vectors remain functions on the SAME actual Spin group with values in
the modular system's characteristic-zero field K. Only their span scalars
are rational. Natural PIM expansions prove rational projected membership;
the checked specified rank-three construction supplies linear independence.
No new source, rational-valued character, or rational basis is supplied.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBSpinGGGRRationalSpanBinding

open ModularRep OrdinaryIrreducibleCharacter TypeBCliffordCarriers
open TypeBSpinPrincipalDecompositionBinding TypeBSpinPrincipalProjectiveBinding
open TypeBSpinPrincipalProjectionPIM TypeBSpinGGGRProjectivityBinding
open TypeBSpinRationalUnipotentClassBinding TypeBCentralKernelBlockSource
open TypeBSpinPrincipalGGGRBasisBinding TypeBSpinGGGRPrincipalSeriesBinding
open TypeBGGGRRankProposition412SourceInstantiation
open scoped BigOperators MonoidAlgebra

local instance finiteTypeFintype (X : Type) [Finite X] : Fintype X :=
  Fintype.ofFinite X

section Physical

variable {n : ℕ} {F K O k : Type} [Field F] [Field K] [CharZero K]
  {N : NormSource n F} [Finite (Spin n F N)]
  [HasEnoughRootsOfUnity K (Nat.card (Spin n F N))]
  [Finite (Irr K (Spin n F N))]
  [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k]
  (Msys : ModularSystem 2 K O k)
  (iota : PrimeRegularRootEmbedding 2 k K (Spin n F N))
  (b : LiteralPrimitiveBlock k (Spin n F N))

/-- Rational combinations of the actual supported specified PIM functions.
This is a span inside `Spin → K`, not restriction of the whole K-span. -/
def projectiveQSpan : Submodule ℚ (Spin n F N → K) :=
  Submodule.span ℚ (Set.range (fun phi : {phi : IBr iota // Supported iota b phi} =>
    projectiveIndecomposable Msys iota phi.val))

theorem projectiveIndecomposable_mem_Q
    (phi : {phi : IBr iota // Supported iota b phi}) :
    projectiveIndecomposable Msys iota phi.val ∈ projectiveQSpan Msys iota b :=
  Submodule.subset_span ⟨phi, rfl⟩

/-- Finiteness concerns the rational span of finitely many PIM functions;
no finite-dimensional assumption is made on the ambient functions over ℚ. -/
instance projectiveQSpan_finiteDimensional :
    FiniteDimensional ℚ (projectiveQSpan Msys iota b) :=
  FiniteDimensional.span_of_finite ℚ (Set.finite_range _)

variable (orthogonality : OrdinaryOrthogonalitySource (N := N) (K := K))
  (columns : DecompositionColumnIndependenceSource Msys iota)

include orthogonality columns in
/-- The specified PIM columns remain independent after restricting scalars. -/
theorem projectiveIndecomposable_Q_linearIndependent :
    LinearIndependent ℚ
      (fun phi : {phi : IBr iota // Supported iota b phi} =>
        projectiveIndecomposable Msys iota phi.val) :=
  (projectiveIndecomposable_linearIndependent orthogonality Msys iota columns b).restrict_scalars' ℚ

include orthogonality columns in
/-- The rational dimension is the SAME supported Brauer cardinal. -/
theorem projectiveQSpan_finrank :
    Module.finrank ℚ (projectiveQSpan Msys iota b) =
      Nat.card {phi : IBr iota // Supported iota b phi} := by
  rw [Nat.card_eq_fintype_card]
  exact finrank_span_eq_card
    (projectiveIndecomposable_Q_linearIndependent Msys iota b orthogonality columns)

variable [Fintype (LiteralPrimitiveBlock k (Spin n F N))]
  (blocks : BlockIdempotentDecomposition
    (fun c : LiteralPrimitiveBlock k (Spin n F N) => c.val))
  (ordinary : OrdinaryBlockSource Msys iota blocks)

include orthogonality in
/-- Supported PIMs are fixed by the actual principal projector, and every
unsupported PIM projects to zero; both belong to the rational span. -/
theorem principalProjection_projectiveIndecomposable_mem_Q (phi : IBr iota) :
    principalProjection Msys iota b blocks ordinary
        (projectiveIndecomposable Msys iota phi) ∈ projectiveQSpan Msys iota b := by
  classical
  by_cases supported : Supported iota b phi
  · rw [principalProjection_projectiveIndecomposable orthogonality Msys iota
      b blocks ordinary ⟨phi, supported⟩]
    exact projectiveIndecomposable_mem_Q Msys iota b ⟨phi, supported⟩
  · rw [projection_zero_of_unsupported orthogonality Msys iota b blocks ordinary
      phi supported]
    exact Submodule.zero_mem _

include orthogonality in
/-- The same actual natural PIM expansion also gives rational membership. -/
theorem projected_combination_mem_Q (c : IBr iota →₀ ℕ) :
    principalProjection Msys iota b blocks ordinary
        (Finsupp.linearCombination ℕ (projectiveIndecomposable Msys iota) c) ∈
      projectiveQSpan Msys iota b := by
  classical
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_nsmul]
  apply Submodule.sum_mem
  intro phi hphi
  exact nsmul_mem
    (principalProjection_projectiveIndecomposable_mem_Q Msys iota b orthogonality
      blocks ordinary phi) (c phi)

include orthogonality in
theorem projected_induction_mem_Q
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (source : OddInductionExpansionCertificate Msys iota hcompat)
    (R : Subgroup (Spin n F N)) (chi : Irr K R) (odd : Odd (Nat.card R)) :
    principalProjection Msys iota b blocks ordinary (inducedFunction R chi) ∈
      projectiveQSpan Msys iota b := by
  obtain ⟨c, hc⟩ := source.expansion R chi odd
  rw [hc]
  exact projected_combination_mem_Q Msys iota b orthogonality blocks ordinary c

variable {r f : ℕ} [Finite F] [CharP F r]

include orthogonality in
/-- Literal GGGR induction yields rational membership without a new
projectivity, rationality or span-membership source. -/
theorem principalGGGR_mem_projectiveQ
    (parameters : OddFieldParameters F r f) (rank : 3 ≤ n)
    (gamma : UnipotentClass (r := r) (N := N) → Spin n F N → K)
    (induction : GGGRInductionSource parameters rank gamma)
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (expansion : OddInductionExpansionCertificate Msys iota hcompat)
    (c : UnipotentClass (r := r) (N := N)) :
    principalProjection Msys iota b blocks ordinary (gamma c) ∈
      projectiveQSpan Msys iota b := by
  rw [induction.gamma_induced c]
  exact projected_induction_mem_Q Msys iota b orthogonality blocks ordinary
    hcompat expansion (induction.subgroup c) (induction.localCharacter c)
    (inducing_order_odd parameters rank gamma induction c)

end Physical

section RankThree

variable {r f : ℕ} {F K : Type} [Field F] [Finite F] [CharP F r]
  [Field K] [CharZero K] {N : NormSource 3 F} [Finite (Spin 3 F N)]
  [HasEnoughRootsOfUnity K (Nat.card (Spin 3 F N))]
  {parameters : OddFieldParameters F r f}
  {GeometricClass : Type}
  {geometricClass : UnipotentClass (r := r) (N := N) → GeometricClass}
  {ComponentGroup : GeometricClass → Type} [∀ C, Group (ComponentGroup C)]
  {gamma : UnipotentClass (r := r) (N := N) → Spin 3 F N → K}
  {rationalSeries : TypeBConformalDualCarriers.PCSp F 3 → Irr K (Spin 3 F N) → Prop}
  {quasiIsolated : TypeBConformalDualCarriers.PCSp F 3 → Prop}
  {normalizedDual : Irr K (Spin 3 F N) → Irr K (Spin 3 F N)}
  {unipotentSupport : Irr K (Spin 3 F N) → GeometricClass → Prop}
  {raw : RankThreeChanebSource parameters geometricClass ComponentGroup gamma
    rationalSeries quasiIsolated normalizedDual unipotentSupport}
  {O k : Type} [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k] [Finite (Irr K (Spin 3 F N))]
  {orthogonality : OrdinaryOrthogonalitySource (N := N) (K := K)}
  {Msys : ModularSystem 2 K O k}
  {iota : PrimeRegularRootEmbedding 2 k K (Spin 3 F N)}
  {hcompat : StableReductionBrauerCharacterCompatibility Msys iota}
  {b : LiteralPrimitiveBlock k (Spin 3 F N)} {principal : IsPrincipal b}
  [Fintype (LiteralPrimitiveBlock k (Spin 3 F N))]
  {blocks : BlockIdempotentDecomposition
    (fun c : LiteralPrimitiveBlock k (Spin 3 F N) => c.val)}
  {ordinary : OrdinaryBlockSource Msys iota blocks}
  {columns : DecompositionColumnIndependenceSource Msys iota}
  {series : PrincipalSeriesCertificate parameters (show 3 ≤ 3 from le_rfl)
    ordinary.ordinaryBlock b principal rationalSeries quasiIsolated normalizedDual}
  {m : ℕ} {classIndex : Fin m ≃ UnipotentClass (r := r) (N := N)}
  {closure : GeometricClass → GeometricClass → Prop}
  {ordering : GeometricOrdering geometricClass classIndex closure}
  {waveFront : WaveFrontClosureCertificate parameters geometricClass gamma
    normalizedDual unipotentSupport closure}
  {count : PrincipalRationalClassCount parameters iota b principal}
  {induction : GGGRInductionSource parameters (show 3 ≤ 3 from le_rfl) gamma}
  {expansion : OddInductionExpansionCertificate Msys iota hcompat}

/-- The exact projected GGGR, now as an element of the literal rational
PIM span. Its underlying function is unchanged. -/
def principalGGGRQComponent (j : Fin m) : projectiveQSpan Msys iota b :=
  ⟨principalProjection Msys iota b blocks ordinary (gamma (classIndex j)),
    principalGGGR_mem_projectiveQ Msys iota b orthogonality blocks ordinary
      parameters (show 3 ≤ 3 from le_rfl) gamma induction hcompat expansion (classIndex j)⟩

include raw orthogonality hcompat columns series ordering waveFront count induction expansion in
/-- Linear independence is taken from the internally constructed specified
rank-three source adapter; a basis/source D is never an external input. -/
theorem principalGGGR_K_linearIndependent :
    LinearIndependent K (fun j : Fin m =>
      principalProjection Msys iota b blocks ordinary (gamma (classIndex j))) := by
  let D := basisSource (parameters := parameters) (geometricClass := geometricClass)
    (ComponentGroup := ComponentGroup) (gamma := gamma) (rationalSeries := rationalSeries)
    (quasiIsolated := quasiIsolated) (normalizedDual := normalizedDual)
    (unipotentSupport := unipotentSupport) (raw := raw) (orthogonality := orthogonality)
    (Msys := Msys) (iota := iota) (hcompat := hcompat) (b := b) (principal := principal)
    (blocks := blocks) (ordinary := ordinary) (columns := columns) (series := series)
    (classIndex := classIndex) (closure := closure) (ordering := ordering)
    (waveFront := waveFront) (count := count) (induction := induction) (expansion := expansion)
  have h := D.gggrProjectiveBasis.linearIndependent.map'
    (physicalProjectiveSpace Msys iota b).subtype (Submodule.ker_subtype _)
  have h' : LinearIndependent K (fun j : Fin m => (D.principalGGGRComponent j).val) := by
    simpa only [D.coe_gggrProjectiveBasis, Function.comp_def, Submodule.subtype_apply] using h
  exact h'

include raw columns series ordering waveFront count in
/-- Restricting the actual K-linear independence and passing through the
rational submodule inclusion gives independence in the required Q-space. -/
theorem principalGGGR_Q_linearIndependent :
    LinearIndependent ℚ
      (principalGGGRQComponent (parameters := parameters) (gamma := gamma)
        (orthogonality := orthogonality) (Msys := Msys) (iota := iota)
        (hcompat := hcompat) (b := b) (blocks := blocks) (ordinary := ordinary)
        (classIndex := classIndex) (induction := induction) (expansion := expansion)) := by
  apply LinearIndependent.of_comp (projectiveQSpan Msys iota b).subtype
  exact (principalGGGR_K_linearIndependent (raw := raw) (orthogonality := orthogonality)
    (Msys := Msys) (iota := iota) (hcompat := hcompat) (b := b) (principal := principal)
    (blocks := blocks) (ordinary := ordinary) (columns := columns) (series := series)
    (classIndex := classIndex) (ordering := ordering) (waveFront := waveFront)
    (count := count) (induction := induction) (expansion := expansion)).restrict_scalars' ℚ

include orthogonality columns count classIndex in
/-- The same rational-class/Brauer cardinal certificate counts the Q-span
dimension, using rational PIM independence rather than scalar restriction. -/
theorem classIndex_card_eq_Q_finrank :
    Fintype.card (Fin m) = Module.finrank ℚ (projectiveQSpan Msys iota b) := by
  calc
    Fintype.card (Fin m) = Nat.card (UnipotentClass (r := r) (N := N)) := by
      simpa only [Nat.card_eq_fintype_card] using Nat.card_congr classIndex
    _ = Nat.card {phi : IBr iota // Supported iota b phi} := count.card_eq
    _ = Module.finrank ℚ (projectiveQSpan Msys iota b) :=
      (projectiveQSpan_finrank Msys iota b orthogonality columns).symm

/-- The rank-three basis over Q in current Proposition 4.9. All source
arguments are the existing specified/classwise inputs; the basis is derived. -/
def rationalGGGRBasis : Module.Basis (Fin m) ℚ (projectiveQSpan Msys iota b) :=
  basisOfLinearIndependentOfCardEqFinrank'
    (principalGGGRQComponent (parameters := parameters) (gamma := gamma)
      (orthogonality := orthogonality) (Msys := Msys) (iota := iota)
      (hcompat := hcompat) (b := b) (blocks := blocks) (ordinary := ordinary)
      (classIndex := classIndex) (induction := induction) (expansion := expansion))
    (principalGGGR_Q_linearIndependent (raw := raw) (orthogonality := orthogonality)
      (Msys := Msys) (iota := iota) (hcompat := hcompat) (b := b) (principal := principal)
      (blocks := blocks) (ordinary := ordinary) (columns := columns) (series := series)
      (classIndex := classIndex) (ordering := ordering) (waveFront := waveFront)
      (count := count) (induction := induction) (expansion := expansion))
    (classIndex_card_eq_Q_finrank (orthogonality := orthogonality) (Msys := Msys)
      (iota := iota) (b := b) (principal := principal) (columns := columns)
      (count := count) (classIndex := classIndex))

/-- Each constructed rational basis vector is the literal principal
projection of the SAME GGGR at the SAME exhaustive rational class index. -/
theorem rationalGGGRBasis_apply (j : Fin m) :
    ((rationalGGGRBasis (parameters := parameters) (geometricClass := geometricClass)
      (ComponentGroup := ComponentGroup) (gamma := gamma) (rationalSeries := rationalSeries)
      (quasiIsolated := quasiIsolated) (normalizedDual := normalizedDual)
      (unipotentSupport := unipotentSupport) (raw := raw) (orthogonality := orthogonality)
      (Msys := Msys) (iota := iota) (hcompat := hcompat) (b := b) (principal := principal)
      (blocks := blocks) (ordinary := ordinary) (columns := columns) (series := series)
      (classIndex := classIndex) (closure := closure) (ordering := ordering)
      (waveFront := waveFront) (count := count) (induction := induction)
      (expansion := expansion)) j).val =
      principalProjection Msys iota b blocks ordinary (gamma (classIndex j)) := by
  simp only [rationalGGGRBasis, coe_basisOfLinearIndependentOfCardEqFinrank',
    principalGGGRQComponent]

end RankThree

end ModularRep.PaperProofs.TypeBSpinGGGRRationalSpanBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
