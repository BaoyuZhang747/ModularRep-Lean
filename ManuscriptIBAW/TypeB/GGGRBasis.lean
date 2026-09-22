import ManuscriptIBAW.TypeB.GGGRSelection

/-!
# The principal GGGR basis with a label for each row

The rows are constructed from the two upper families. Their membership
in the principal block follows using each row's literal rational series label. The
finite matrix, projectivity, dimension and rational basis deductions use
the supporting proofs. No common label for a geometric class is imposed.
-/

noncomputable section
set_option autoImplicit false

namespace ManuscriptIBAW.TypeB.GGGRBasis

open ModularRep ModularRep.PaperProofs OrdinaryIrreducibleCharacter TypeBCliffordCarriers
open TypeBCentralKernelBlockSource TypeBSpinPrincipalDecompositionBinding
open TypeBSpinPrincipalProjectiveBinding TypeBSpinRationalUnipotentClassBinding
open TypeBSpinGGGRPrincipalSeriesBinding TypeBSpinGGGRProjectivityBinding
open TypeBSpinGGGRRationalSpanBinding TypeBAllRankGGGRFibres TypeBCurrentPrincipalResults
open TypeBAllRankGGGREntries TypeBAllRankGGGR.BasisPhysical
open TypeBGGGRRankProposition412Relative TypeBGGGRRankProposition412SourceInstantiation
open scoped MonoidAlgebra Pointwise

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


/-- The construction in higher rank uses the two upper families and
proves membership in the principal block using the label of each row. -/
theorem higher_basis (D : GGGRContext parameters rank Msys iota b)
    {higher : 4 ≤ n} (source : GGGRSources.HigherSources D higher) : GGGRConclusion D := by
  classical
  let positive := nonnegative (parameters := parameters) (rank := higher)
    (induction := D.induction) (orthogonality := D.orthogonality) (Msys := Msys)
    (iota := iota) (hcompat := D.hcompat) (expansion := D.expansion)
  let before := GGGRSelection.beforeDual positive source.reciprocity source.sources
  let label := GGGRSelection.rowLabel positive source.reciprocity source.sources
  have label_quasi : ∀ c, D.quasiIsolated (label c) :=
    GGGRSelection.label_quasiIsolated positive source.reciprocity source.sources
  have rows_series : ∀ c, D.rationalSeries (label c) (before c) :=
    GGGRSelection.beforeDual_series positive source.reciprocity source.sources
  have rows_support : ∀ c, D.unipotentSupport (before c) (D.geometricClass c) :=
    GGGRSelection.beforeDual_support positive source.reciprocity source.sources
  have rows_principal : ∀ c, D.ordinary.ordinaryBlock (D.lowerDual (before c)) = b := by
    intro c
    exact selectedDual_principal parameters rank D.ordinary.ordinaryBlock b D.principal
      D.rationalSeries D.quasiIsolated D.lowerDual D.series
      (label c) (before c) (label_quasi c) (rows_series c)
  let diagonal := GGGRSelection.diagonalCases positive source.reciprocity source.sources
  let actual : GGGRBasisSource D.m (physicalProjectiveSpace Msys iota b) := {
    gggr := fun j => D.gamma (D.classIndex j)
    selectedOrdinary := fun i => D.lowerDual (before (D.classIndex i))
    scalarProductRight := fun x => TypeBSpinPrincipalProjectiveBinding.scalarProductRight x
    principalProjection := principalProjection Msys iota b D.blocks D.ordinary
    principalProjection_idempotent :=
      principalProjection_idempotent D.orthogonality Msys iota b D.blocks D.ordinary
    principalProjection_selfAdjoint :=
      principalProjection_selfAdjoint Msys iota b D.blocks D.ordinary
    selectedOrdinary_in_principal := fun i =>
      principalProjection_selected D.orthogonality Msys iota b D.blocks D.ordinary _
        (rows_principal (D.classIndex i))
    principalGGGR_mem_projective := fun j =>
      principalGGGR_mem_projective parameters rank D.gamma D.induction D.orthogonality
        Msys iota D.hcompat b D.blocks D.ordinary D.expansion (D.classIndex j)
    multiplicity := fun i j => multiplicity D.gamma positive
      (D.lowerDual (before (D.classIndex i))) (D.classIndex j)
    scalarProduct_full_eq_multiplicity := fun i j =>
      (multiplicity_cast D.gamma positive
        (D.lowerDual (before (D.classIndex i))) (D.classIndex j)).symm
    geometricClass := numericClass (ordering := D.ordering)
    geometricClass_mono := D.ordering.consecutive
    diagonalSource := numericDiagonalSourceCore (ordering := D.ordering)
      (fun c d => multiplicity D.gamma positive (D.lowerDual (before c)) d) diagonal
    closure_vanishing := fun i j h =>
      closure_vanishing (parameters := parameters) (rank := higher)
        (beforeDual := before) (lowerDual := D.lowerDual)
        (classIndex := D.classIndex) (ordering := D.ordering) (waveFront := source.waveFront)
        (beforeDual_support := rows_support) i j h
    card_eq_finrank := classIndex_card_eq_finrank (parameters := parameters) (rank := higher)
      (orthogonality := D.orthogonality) (Msys := Msys) (columns := D.columns)
      (classIndex := D.classIndex) (count := source.count) }
  let B := TypeBAllRankGGGR.Basis.rationalGGGRBasisOfPhysicalSource
    (parameters := parameters) (rank := higher) (orthogonality := D.orthogonality)
    (columns := D.columns) (Msys := Msys) (iota := iota) (hcompat := D.hcompat)
    (b := b) (blocks := D.blocks) (ordinary := D.ordinary) (gamma := D.gamma)
    (classIndex := D.classIndex) (induction := D.induction) (expansion := D.expansion)
    actual (fun _ => rfl) rfl
  refine ⟨fun i => D.lowerDual (before (D.classIndex i)),
    fun i => rows_principal (D.classIndex i), actual.rowPermutation, ?_, ?_, ?_, B, ?_⟩
  · intro i
    exact D.ordering.code_injective (actual.rowPermutation_preserves_class i)
  · intro i j same
    change actual.scalarProductMatrix (actual.rowPermutation i) j = if i = j then 1 else 0
    exact actual.closurePermutationData.same_class_entry i j (congrArg D.ordering.code same)
  · intro i j h
    change actual.scalarProductMatrix (actual.rowPermutation i) j = 0
    apply actual.closurePermutationData.closure_vanishing i j
    change actual.geometricClass (actual.rowPermutation i) < actual.geometricClass j
    rw [actual.rowPermutation_preserves_class]
    exact h
  · intro j
    exact TypeBAllRankGGGR.Basis.rationalGGGRBasisOfPhysicalSource_apply
      (parameters := parameters) (rank := higher) (orthogonality := D.orthogonality)
      (columns := D.columns) (Msys := Msys) (iota := iota) (hcompat := D.hcompat)
      (b := b) (blocks := D.blocks) (ordinary := D.ordinary) (gamma := D.gamma)
      (classIndex := D.classIndex) (induction := D.induction) (expansion := D.expansion)
      actual (fun _ => rfl) rfl j

/-- The rank three interface is filled with abelian rows proved from the
upper sources. -/
def rankThreeSource
    {N : NormSource 3 F} [Finite (SpecialClifford 3 F)] [Finite (Spin 3 F N)]
    [HasEnoughRootsOfUnity K (Nat.card (SpecialClifford 3 F))]
    [HasEnoughRootsOfUnity K (Nat.card (Spin 3 F N))]
    [Finite (Irr K (Spin 3 F N))]
    {iota : PrimeRegularRootEmbedding 2 k K (Spin 3 F N)}
    {b : LiteralPrimitiveBlock k (Spin 3 F N)}
    [Fintype (LiteralPrimitiveBlock k (Spin 3 F N))]
    (D : GGGRContext parameters (show 3 ≤ 3 from le_rfl) Msys iota b)
    (source : GGGRSources.RankThreeSources D) :
    TypeBCurrentPrincipalResults.RankThreeSources D := by
  classical
  let positive := gggr_scalarProduct_nonnegative parameters (show 3 ≤ 3 from le_rfl)
    D.gamma D.induction D.orthogonality Msys iota D.hcompat D.expansion
  let data := fun (C : D.GeometricClass) (represented : Nonempty (RationalFibre D.geometricClass C)) =>
    GGGRAbelian.rows source.reciprocity positive (source.sources C represented)
  let before := fun (c : UnipotentClass (r := r) (N := N)) =>
    (data (D.geometricClass c) ⟨⟨c, rfl⟩⟩).beforeDual ⟨c, rfl⟩
  let label := fun C : D.GeometricClass =>
    if represented : Nonempty (RationalFibre D.geometricClass C)
      then (data C represented).label else 1
  have before_eq : ∀ (C : D.GeometricClass)
      (represented : Nonempty (RationalFibre D.geometricClass C))
      (c : RationalFibre D.geometricClass C),
      before c.val = (data C represented).beforeDual c := by
    intro C represented c
    rcases c with ⟨c, hc⟩
    cases hc
    rfl
  have label_eq : ∀ (C : D.GeometricClass)
      (represented : Nonempty (RationalFibre D.geometricClass C)),
      label C = (data C represented).label := by
    intro C represented
    simp only [label, dif_pos represented]
  refine {
    raw := {
      beforeDual := before
      classLabel := label
      component_abelian := fun c =>
        (source.sources (D.geometricClass c) ⟨⟨c, rfl⟩⟩).component_abelian
      label_quasiIsolated := ?_
      beforeDual_series := ?_
      beforeDual_support := ?_
      identity_pairing := ?_ }
    waveFront := source.waveFront
    count := source.count }
  · intro c
    rw [label_eq _ ⟨⟨c, rfl⟩⟩]
    exact (data (D.geometricClass c) ⟨⟨c, rfl⟩⟩).label_quasiIsolated
  · intro c
    rw [label_eq _ ⟨⟨c, rfl⟩⟩]
    exact (data (D.geometricClass c) ⟨⟨c, rfl⟩⟩).beforeDual_series ⟨c, rfl⟩
  · intro c
    exact (data (D.geometricClass c) ⟨⟨c, rfl⟩⟩).beforeDual_support ⟨c, rfl⟩
  · intro C _ c d
    rw [before_eq C ⟨c⟩ c]
    exact (data C ⟨c⟩).identity_pairing c d

/-- Rank three uses the proved abelian construction. In higher rank the construction
assigns a label to each row and supplies the basis. -/
theorem gggr_basis (D : GGGRContext parameters rank Msys iota b)
    (raw : GGGRSources.RankSources D) : GGGRConclusion D := by
  by_cases three : n = 3
  · subst n
    exact TypeBCurrentPrincipalResults.gggr_basis D {
      rankThree := fun h => by cases h; exact rankThreeSource D (raw.rankThree rfl)
      higher := fun h => False.elim (by omega) }
  · exact higher_basis D (raw.higher (by omega))

/-- Field automorphisms fix every principal Brauer character in all ranks
at least three. The proof uses the rational basis and the invariance of
the projected GGGRs under these automorphisms. -/
theorem principalBrauer_fixed (D : GGGRContext parameters rank Msys iota b)
    (raw : GGGRSources.RankSources D) (S : FieldActionSource n F r f parameters N)
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

/-- The principal corollary's fixation, Clifford stabilizer and
representation extension clauses, including `(n,q)=(3,3)`. -/
theorem principal_selector (D : GGGRContext parameters rank Msys iota b)
    (raw : GGGRSources.RankSources D) (S : FieldActionSource n F r f parameters N)
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
  · let : NeZero f := ⟨Nat.ne_of_gt parameters.exponent_pos⟩
    exact TypeBAllRankPrincipalSelectorSemidirect.extends_to_spinField
      S iota phi (fun e => fixed e⁻¹) principle


end ManuscriptIBAW.TypeB.GGGRBasis

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
