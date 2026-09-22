import ModularRep.PaperProofs.TypeBAllRankPrincipalSelectorApplication
import ModularRep.PaperProofs.TypeBSpinPrincipalGGGRFieldApplication

/-!
# Current principal Spin results in every rank at least three

The common data below describe actual classes, ordinary characters, a modular
system and the literal principal block. The two raw source branches retain the
published Chaneb and Taylor inputs. Neither branch supplies a basis or Brauer
fixation. The rank split is performed in the deduction.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBCurrentPrincipalResults

open ModularRep OrdinaryIrreducibleCharacter TypeBCliffordCarriers
open TypeBCentralKernelBlockSource TypeBSpinPrincipalDecompositionBinding
open TypeBSpinPrincipalProjectiveBinding TypeBSpinRationalUnipotentClassBinding
open TypeBSpinGGGRPrincipalSeriesBinding TypeBSpinGGGRProjectivityBinding
open TypeBSpinGGGRRationalSpanBinding TypeBAllRankGGGRFibres
open TypeBRationalFieldLemma411Relative TypeBLemma411Proposition412LiteralHandoff
open TypeBPrincipalSelectorCorollary413SourceInstantiation
open scoped MonoidAlgebra Pointwise

section RationalField

variable {n r f : ℕ} {F K : Type}
  [Field F] [Finite F] [CharP F r] [Field K] [CharZero K]
  {N : NormSource n F} [Finite (Spin n F N)]
  {parameters : OddFieldParameters F r f} {rank : 3 ≤ n}
  {S : FieldActionSource n F r f parameters N}
  {GeometricClass : Type}
  {geometricClass : UnipotentClass (r := r) (N := N) → GeometricClass}
  {geometricStable : GeometricFieldStable parameters S geometricClass}
  {ComponentGroup : GeometricClass → Type} [∀ C, Group (ComponentGroup C)]
  {inner : ∀ C, ComponentGroup C}
  (rational : RationalGGGRSource (K := K) parameters rank S
    geometricClass geometricStable ComponentGroup inner)

include rational in
/-- Current Lemma 4.7 on every actual rational class; no basis is required. -/
theorem rationalClass_fixed (e : FieldGroup f)
    (c : UnipotentClass (r := r) (N := N)) :
    letI := unipotentClassFieldAction parameters S
    e • c = c := by
  letI := unipotentClassFieldAction parameters S
  letI : ∀ C, MulAction (FieldGroup f) (RationalFibre geometricClass C) :=
    fun C => rationalFibreFieldAction parameters S geometricClass geometricStable C
  have fixed : e • (⟨c, rfl⟩ : RationalFibre geometricClass (geometricClass c)) =
      (⟨c, rfl⟩ : RationalFibre geometricClass (geometricClass c)) :=
    (rational.parameter (geometricClass c)).smul_eq_self e ⟨c, rfl⟩
  exact congrArg Subtype.val fixed

/-- Taylor equivariance gives the same positive field twist on each GGGR. -/
theorem gggr_fixed (e : FieldGroup f)
    (c : UnipotentClass (r := r) (N := N)) :
    functionTwistLinearEquiv (K := K) (spinFieldAction n F S e) (rational.gamma c) =
      rational.gamma c := by
  letI := unipotentClassFieldAction parameters S
  letI := taylorFunctionFieldAction (K := K) (spinRightFieldHom parameters S)
  have fixed := manuscriptRightAction_gamma_eq_self rational.gamma
    rational.taylorEquivariant (rationalClass_fixed rational) e c
  rw [manuscriptRightAction_eq_functionTwist (K := K)
    (spinRightFieldHom parameters S)] at fixed
  simpa only [spinRightFieldHom_unop] using fixed

end RationalField

section Principal

variable {n r f : ℕ} {F K O k : Type}
  [Field F] [Finite F] [CharP F r] [Field K] [CharZero K]
  [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k]
  {N : NormSource n F} [Finite (SpecialClifford n F)] [Finite (Spin n F N)]
  [HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F))]
  [HasEnoughRootsOfUnity K (Nat.card (Spin n F N))]
  [Finite (Irr K (Spin n F N))]
  {parameters : OddFieldParameters F r f} {rank : 3 ≤ n}
  {Msys : ModularSystem 2 K O k}
  {iota : PrimeRegularRootEmbedding 2 k K (Spin n F N)}
  {b : LiteralPrimitiveBlock k (Spin n F N)}
  [Fintype (LiteralPrimitiveBlock k (Spin n F N))]

/-- Shared specified and geometric source data. The ordering concerns the
actual closure relation and the enumeration exhausts the literal Spin classes.
The `series` and `induction` fields are the existing published contracts. -/
structure GGGRContext (parameters : OddFieldParameters F r f) (rank : 3 ≤ n)
    (Msys : ModularSystem 2 K O k)
    (iota : PrimeRegularRootEmbedding 2 k K (Spin n F N))
    (b : LiteralPrimitiveBlock k (Spin n F N)) where
  finiteClifford : FiniteCliffordSource n F
  orthogonality : OrdinaryOrthogonalitySource (N := N) (K := K)
  hcompat : StableReductionBrauerCharacterCompatibility Msys iota
  principal : IsPrincipal b
  blocks : BlockIdempotentDecomposition
    (fun c : LiteralPrimitiveBlock k (Spin n F N) => c.val)
  ordinary : OrdinaryBlockSource Msys iota blocks
  columns : DecompositionColumnIndependenceSource Msys iota
  GeometricClass : Type
  geometricClass : UnipotentClass (r := r) (N := N) → GeometricClass
  ComponentGroup : GeometricClass → Type
  componentInstances : ∀ C, Group (ComponentGroup C)
  gamma : UnipotentClass (r := r) (N := N) → Spin n F N → K
  lowerDual : Irr K (Spin n F N) → Irr K (Spin n F N)
  rationalSeries : TypeBConformalDualCarriers.PCSp F n → Irr K (Spin n F N) → Prop
  quasiIsolated : TypeBConformalDualCarriers.PCSp F n → Prop
  unipotentSupport : Irr K (Spin n F N) → GeometricClass → Prop
  series : PrincipalSeriesCertificate parameters rank ordinary.ordinaryBlock b principal
    rationalSeries quasiIsolated lowerDual
  m : ℕ
  classIndex : Fin m ≃ UnipotentClass (r := r) (N := N)
  closure : GeometricClass → GeometricClass → Prop
  ordering : TypeBAllRankGGGR.BasisPhysical.GeometricOrdering
    geometricClass classIndex closure
  induction : GGGRInductionSource parameters rank gamma
  expansion : OddInductionExpansionCertificate Msys iota hcompat

attribute [instance] GGGRContext.componentInstances

/-- The raw higher-rank sources used by the accepted literal GGGR theorem. -/
structure HigherSources (D : GGGRContext parameters rank Msys iota b) (higher : 4 ≤ n) where
  upperGeometricClass : UpperUnipotentClass (n := n) (F := F) (r := r) → D.GeometricClass
  geometric_square : ∀ c, upperGeometricClass (upperClassMap c) = D.geometricClass c
  upperDual : Irr K (SpecialClifford n F) → Irr K (SpecialClifford n F)
  waveFront : TypeBAllRankGGGR.BasisPhysical.WaveFrontClosureCertificate parameters higher
    D.geometricClass D.gamma D.lowerDual D.unipotentSupport D.closure
  count : TypeBAllRankGGGR.BasisPhysical.PrincipalRationalClassCount parameters higher
    iota b D.principal
  reciprocity : TypeBAllRankGGGREntries.FrobeniusReciprocitySource (N := N) (K := K)
  sources : ∀ C, Nonempty (RationalFibre D.geometricClass C) →
    TypeBAllRankGGGRSelection.LocalSources (geometricClass := D.geometricClass)
      (upperGeometricClass := upperGeometricClass) (geometric_square := geometric_square)
      (ComponentGroup := D.ComponentGroup) (gamma := D.gamma) (upperDual := upperDual)
      (lowerDual := D.lowerDual) (rationalSeries := D.rationalSeries)
      (quasiIsolated := D.quasiIsolated) (unipotentSupport := D.unipotentSupport)
      (parameters := parameters) (rank := higher) C

/-- The exact rank-three Chaneb, support and rational-class count inputs. -/
structure RankThreeSources
    {N : NormSource 3 F} [Finite (SpecialClifford 3 F)] [Finite (Spin 3 F N)]
    [HasEnoughRootsOfUnity K (Nat.card (SpecialClifford 3 F))]
    [HasEnoughRootsOfUnity K (Nat.card (Spin 3 F N))]
    [Finite (Irr K (Spin 3 F N))]
    {iota : PrimeRegularRootEmbedding 2 k K (Spin 3 F N)}
    {b : LiteralPrimitiveBlock k (Spin 3 F N)}
    [Fintype (LiteralPrimitiveBlock k (Spin 3 F N))]
    (D : GGGRContext parameters (show 3 ≤ 3 from le_rfl) Msys iota b) where
  raw : TypeBSpinPrincipalGGGRBasisBinding.RankThreeChanebSource parameters
    D.geometricClass D.ComponentGroup D.gamma D.rationalSeries D.quasiIsolated
    D.lowerDual D.unipotentSupport
  waveFront : TypeBSpinPrincipalGGGRBasisBinding.WaveFrontClosureCertificate parameters
    D.geometricClass D.gamma D.lowerDual D.unipotentSupport D.closure
  count : TypeBSpinPrincipalGGGRBasisBinding.PrincipalRationalClassCount parameters
    iota b D.principal

/-- Both implications are guarded by their actual numerical scope. Their
codomains contain only raw published input, never any desired conclusion. -/
structure RankSources (D : GGGRContext parameters rank Msys iota b) where
  rankThree : ∀ h : n = 3, by subst n; exact RankThreeSources D
  higher : ∀ h : 4 ≤ n, HigherSources D h

/-- Current Proposition 4.9, with its rows, geometric diagonal permutations,
closure triangularity and basis of the literal rational PIM span. -/
def GGGRConclusion (D : GGGRContext parameters rank Msys iota b) : Prop :=
  ∃ rho : Fin D.m → Irr K (Spin n F N),
    (∀ i, D.ordinary.ordinaryBlock (rho i) = b) ∧
    ∃ p : Equiv.Perm (Fin D.m),
      (∀ i, D.geometricClass (D.classIndex (p i)) = D.geometricClass (D.classIndex i)) ∧
      (∀ i j, D.geometricClass (D.classIndex i) = D.geometricClass (D.classIndex j) →
        scalarProductRight (rho (p i)).val
          (principalProjection Msys iota b D.blocks D.ordinary (D.gamma (D.classIndex j))) =
            if i = j then 1 else 0) ∧
      (∀ i j, D.ordering.code (D.geometricClass (D.classIndex i)) <
          D.ordering.code (D.geometricClass (D.classIndex j)) →
        scalarProductRight (rho (p i)).val
          (principalProjection Msys iota b D.blocks D.ordinary (D.gamma (D.classIndex j))) = 0) ∧
      ∃ B : Module.Basis (Fin D.m) ℚ (projectiveQSpan Msys iota b),
        ∀ j, (B j).val =
          principalProjection Msys iota b D.blocks D.ordinary (D.gamma (D.classIndex j))

/-- The actual all-rank deduction. Rank three uses the retained specified
Chaneb source and its rational-span descent; larger ranks use the accepted
nonabelian selection and restriction theorem. -/
theorem gggr_basis (D : GGGRContext parameters rank Msys iota b)
    (raw : RankSources D) : GGGRConclusion D := by
  classical
  by_cases three : n = 3
  · subst n
    let source := raw.rankThree rfl
    let ordering : TypeBSpinPrincipalGGGRBasisBinding.GeometricOrdering
        D.geometricClass D.classIndex D.closure :=
      ⟨D.ordering.code, D.ordering.code_injective, D.ordering.closure_mono,
        D.ordering.consecutive⟩
    let actual := TypeBSpinPrincipalGGGRBasisBinding.basisSource
      (parameters := parameters) (geometricClass := D.geometricClass)
      (ComponentGroup := D.ComponentGroup) (gamma := D.gamma)
      (rationalSeries := D.rationalSeries) (quasiIsolated := D.quasiIsolated)
      (normalizedDual := D.lowerDual) (unipotentSupport := D.unipotentSupport)
      (raw := source.raw) (orthogonality := D.orthogonality)
      (Msys := Msys) (iota := iota) (hcompat := D.hcompat) (b := b)
      (principal := D.principal) (blocks := D.blocks) (ordinary := D.ordinary)
      (columns := D.columns) (series := D.series) (classIndex := D.classIndex)
      (closure := D.closure) (ordering := ordering) (waveFront := source.waveFront)
      (count := source.count) (induction := D.induction) (expansion := D.expansion)
    let B := TypeBSpinGGGRRationalSpanBinding.rationalGGGRBasis
      (parameters := parameters) (geometricClass := D.geometricClass)
      (ComponentGroup := D.ComponentGroup) (gamma := D.gamma)
      (rationalSeries := D.rationalSeries) (quasiIsolated := D.quasiIsolated)
      (normalizedDual := D.lowerDual) (unipotentSupport := D.unipotentSupport)
      (raw := source.raw) (orthogonality := D.orthogonality)
      (Msys := Msys) (iota := iota) (hcompat := D.hcompat) (b := b)
      (principal := D.principal) (blocks := D.blocks) (ordinary := D.ordinary)
      (columns := D.columns) (series := D.series) (classIndex := D.classIndex)
      (closure := D.closure) (ordering := ordering) (waveFront := source.waveFront)
      (count := source.count) (induction := D.induction) (expansion := D.expansion)
    refine ⟨fun i => D.lowerDual (source.raw.beforeDual (D.classIndex i)), ?_,
      actual.rowPermutation, ?_, ?_, ?_, B, ?_⟩
    · intro i
      exact TypeBSpinPrincipalGGGRBasisBinding.selected_principal
        (raw := source.raw) (series := D.series) (D.classIndex i)
    · intro i
      exact ordering.code_injective (actual.rowPermutation_preserves_class i)
    · intro i j same
      change actual.scalarProductMatrix (actual.rowPermutation i) j = if i = j then 1 else 0
      exact actual.closurePermutationData.same_class_entry i j (congrArg ordering.code same)
    · intro i j higher
      change actual.scalarProductMatrix (actual.rowPermutation i) j = 0
      apply actual.closurePermutationData.closure_vanishing i j
      change actual.geometricClass (actual.rowPermutation i) < actual.geometricClass j
      rw [actual.rowPermutation_preserves_class]
      exact higher
    · intro j
      exact TypeBSpinGGGRRationalSpanBinding.rationalGGGRBasis_apply
        (parameters := parameters) (geometricClass := D.geometricClass)
        (ComponentGroup := D.ComponentGroup) (gamma := D.gamma)
        (rationalSeries := D.rationalSeries) (quasiIsolated := D.quasiIsolated)
        (normalizedDual := D.lowerDual) (unipotentSupport := D.unipotentSupport)
        (raw := source.raw) (orthogonality := D.orthogonality)
        (Msys := Msys) (iota := iota) (hcompat := D.hcompat) (b := b)
        (principal := D.principal) (blocks := D.blocks) (ordinary := D.ordinary)
        (columns := D.columns) (series := D.series) (classIndex := D.classIndex)
        (closure := D.closure) (ordering := ordering) (waveFront := source.waveFront)
        (count := source.count) (induction := D.induction) (expansion := D.expansion) j
  · have higher : 4 ≤ n := by omega
    let source := raw.higher higher
    exact TypeBAllRankGGGRApplication.manuscript_deduction D.finiteClifford D.orthogonality
      (parameters := parameters) (rank := higher)
      (geometricClass := D.geometricClass) (upperGeometricClass := source.upperGeometricClass)
      (geometric_square := source.geometric_square) (ComponentGroup := D.ComponentGroup)
      (gamma := D.gamma) (upperDual := source.upperDual) (lowerDual := D.lowerDual)
      (rationalSeries := D.rationalSeries) (quasiIsolated := D.quasiIsolated)
      (unipotentSupport := D.unipotentSupport)
      (Msys := Msys) (iota := iota) (hcompat := D.hcompat) (b := b)
      (principal := D.principal) (blocks := D.blocks) (ordinary := D.ordinary)
      D.columns D.series D.classIndex D.ordering source.waveFront source.count
      D.induction D.expansion source.reciprocity source.sources

/-- The actual geometric fibre and Taylor sources for the SAME GGGR family.
The equality is a family identification, not a fixedness or basis input. -/
structure FieldSources (D : GGGRContext parameters rank Msys iota b)
    (S : FieldActionSource n F r f parameters N) where
  geometricStable : GeometricFieldStable parameters S D.geometricClass
  inner : ∀ C, D.ComponentGroup C
  rational : RationalGGGRSource (K := K) parameters rank S D.geometricClass
    geometricStable D.ComponentGroup inner
  gamma_eq : rational.gamma = D.gamma

/-- Field fixation of every principal Brauer character in all current ranks.
The rational basis and all projected GGGR fixation are proved internally. -/
theorem principalBrauer_fixed (D : GGGRContext parameters rank Msys iota b)
    (raw : RankSources D) (S : FieldActionSource n F r f parameters N)
    (field : FieldSources D S) (e : FieldGroup f) (phi : IBr iota)
    (supported : Supported iota b phi) :
    IrreducibleBrauerCharacter.twist iota phi (spinFieldAction n F S e) = phi := by
  obtain ⟨_, _, _, _, _, _, B, basis_apply⟩ := gggr_basis D raw
  apply TypeBAllRankPrincipalSelectorFixedProjective.principalBrauer_fixed_of_projectedGGGRBasis
    D.orthogonality D.hcompat D.columns D.blocks D.ordinary D.principal
    D.classIndex D.gamma B basis_apply (spinFieldAction n F S e) ?_ phi supported
  intro j
  rw [TypeBAllRankPrincipalSelectorFieldNaturality.principalProjection_field_natural
    Msys iota D.hcompat b D.principal D.blocks D.ordinary]
  rw [← field.gamma_eq]
  exact congrArg (principalProjection Msys iota b D.blocks D.ordinary)
    (gggr_fixed field.rational e (D.classIndex j))

/-- The fixation, literal Clifford stabilizer and honest representation
extension clauses of current Corollary 4.10, including `(n,q)=(3,3)`. -/
theorem principal_selector (D : GGGRContext parameters rank Msys iota b)
    (raw : RankSources D) (S : FieldActionSource n F r f parameters N)
    (field : FieldSources D S)
    (principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} 2 k)
    (phi : IBr iota) (supported : Supported iota b phi) :
    (∀ e : FieldGroup f, IrreducibleBrauerCharacter.twist iota phi
      (spinFieldAction n F S e) = phi) ∧
    (TypeBAllRankPrincipalSelectorSemidirect.cliffordStabilizer S iota phi :
      Set (SpecialClifford n F ⋊[S.action] FieldGroup f)) =
      (((TypeBInertiaHallSource.brauerInertia N iota phi).map
        (SemidirectProduct.inl (φ := S.action))) :
          Set (SpecialClifford n F ⋊[S.action] FieldGroup f)) *
      ((SemidirectProduct.inr (φ := S.action)).range :
        Set (SpecialClifford n F ⋊[S.action] FieldGroup f)) ∧
    ∃ V : FDRep k (Spin n F N), Representation.IsIrreducible V.ρ ∧
      phi.val = Representation.brauerCharacterOfRootEmbedding V.ρ iota ∧
      ∃ rho : Representation k (Spin n F N ⋊[spinFieldAction n F S] FieldGroup f) V.V,
        Representation.IsIrreducible rho ∧
        Nonempty (Representation.Equiv
          (Representation.pullback rho
            (SemidirectProduct.inl (φ := spinFieldAction n F S))) V.ρ) := by
  have fixed := fun e => principalBrauer_fixed D raw S field e phi supported
  refine ⟨fixed, ?_, ?_⟩
  · exact TypeBAllRankPrincipalSelectorSemidirect.cliffordStabilizer_eq_brauerInertia_product
      S iota phi (fun e => fixed e⁻¹)
  · letI : NeZero f := ⟨Nat.ne_of_gt parameters.exponent_pos⟩
    exact TypeBAllRankPrincipalSelectorSemidirect.extends_to_spinField
      S iota phi (fun e => fixed e⁻¹) principle

end Principal

end ModularRep.PaperProofs.TypeBCurrentPrincipalResults


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
