import ManuscriptIBAW.TypeB.GGGRAbelian

/-!
# Selection from two upper rational series

The singleton rows use the isolated family. The unique fibre of size two
uses the distinguished character from Taylor's original family. Only the
restriction and finite matrix construction use the union of the two sets.
Each selected row retains its own literal rational series label.
-/

noncomputable section
set_option autoImplicit false

namespace ManuscriptIBAW.TypeB.GGGRSelection

open ModularRep ModularRep.PaperProofs OrdinaryIrreducibleCharacter TypeBCliffordCarriers
open TypeBSpinRationalUnipotentClassBinding TypeBSpinOrdinaryRestriction
open TypeBSpinPrincipalProjectiveBinding TypeBAllRankGGGRFibres
open TypeBAllRankGGGREntries TypeBGGGRRankProposition412Relative

attribute [local instance] Classical.propDecidable

local instance selectionFiniteFintype (X : Type) [Finite X] : Fintype X :=
  Fintype.ofFinite X

variable {n r f : ℕ} {F K : Type} [Field F] [Finite F] [CharP F r]
  [Field K] [CharZero K] {N : NormSource n F}
  [Finite (SpecialClifford n F)] [Finite (Spin n F N)]
  [Finite (Irr K (Spin n F N))]
  [HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F))]
  [HasEnoughRootsOfUnity K (Nat.card (Spin n F N))]
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


open GGGRSources

variable {parameters : OddFieldParameters F r f} {rank : 4 ≤ n} {C : GeometricClass}

section WorkingFamily

variable (source : GGGRSources.NonabelianSource (geometricClass := geometricClass)
  (upperGeometricClass := upperGeometricClass) (geometric_square := geometric_square)
  (ComponentGroup := ComponentGroup) (gamma := gamma) (upperDual := upperDual)
  (lowerDual := lowerDual) (rationalSeries := rationalSeries)
  (quasiIsolated := quasiIsolated) (unipotentSupport := unipotentSupport)
  parameters rank C)

local instance selectionUpperGroup : CommGroup source.UpperComponent := source.upperComponentGroup

/-- Keep the original distinguished character `source.distinguished` and the
characters of the selected isolated family `source.isolatedFamily` that pair
with a nonexceptional upper class. Above the fibre of size two, the matrix
selection uses the original distinguished character. -/
def workingFamily : Set (Irr K (SpecialClifford n F)) :=
  {Phi | Phi = source.distinguished ∨
    (Phi ∈ source.isolatedFamily ∧ ∃ u, u ≠ source.parameter.exceptional ∧
      upperScalarProduct (upperDual Phi).val (source.upperGamma u) ≠ 0)}

omit [CharZero K] [HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F))]
  [HasEnoughRootsOfUnity K (Nat.card (Spin n F N))] in
theorem workingFamily_subset :
    workingFamily source ⊆ {source.distinguished} ∪ source.isolatedFamily := by
  intro Phi h
  rcases h with h | ⟨h, _⟩
  · subst Phi
    exact Or.inl rfl
  · exact Or.inr h

variable
  (reciprocity : FrobeniusReciprocitySource (N := N) (K := K))
  (nonnegative : ∀ (rho : Irr K (Spin n F N))
    (c : UnipotentClass (r := r) (N := N)),
    ∃ a : ℕ, scalarProductRight rho.val (gamma c) = (a : K))

include reciprocity nonnegative in
/-- The distinguished character's two constituents force its upper support
onto the exceptional fibre. Only row sums and the restriction proof are used. -/
theorem original_support :
    upperSupport source.unionSource
      ⟨source.distinguished, Or.inl rfl⟩ =
        source.parameter.exceptional := by
  by_contra h
  have one := (singleton_irreducible source.unionSource reciprocity nonnegative
    source.parameter ⟨source.distinguished, Or.inl rfl⟩ h).1
  have two := source.distinguished_two
  simp only [Fintype.card_eq_nat_card] at one two
  omega

include reciprocity nonnegative in
/-- The finite restriction source for the constructed working set. Coverage
is derived from the original character at the exceptional class and the
isolated-family coverage at every other class. -/
theorem workingSource :
    TaylorFamilySource geometricClass upperGeometricClass geometric_square C
      parameters rank gamma source.upperGamma (workingFamily source) upperDual lowerDual := by
  let full := source.unionSource
  refine {
    restriction := {
      nonempty := fun Phi h => full.restriction.nonempty Phi (workingFamily_subset source h)
      dualityRestriction := fun Phi h => full.restriction.dualityRestriction Phi
        (workingFamily_subset source h)
      cliffordTransitive := fun Phi h => full.restriction.cliffordTransitive Phi
        (workingFamily_subset source h)
      dualityConjugation := fun Phi h => full.restriction.dualityConjugation Phi
        (workingFamily_subset source h) }
    upperNonnegative := fun Phi h => full.upperNonnegative Phi (workingFamily_subset source h)
    upperSumOne := fun Phi h => full.upperSumOne Phi (workingFamily_subset source h)
    distinguished := ⟨source.distinguished, Or.inl rfl, source.distinguished_two⟩
    gggrInduction := full.gggrInduction
    gggrConjugation := full.gggrConjugation
    coverage := ?_ }
  intro u
  by_cases exceptional : u = source.parameter.exceptional
  · refine ⟨source.distinguished, Or.inl rfl, ?_⟩
    rw [← upperMultiplicity_cast source.unionSource
      ⟨source.distinguished, Or.inl rfl⟩ u,
      upperMultiplicity_eq, original_support source reciprocity nonnegative,
      if_pos exceptional, Nat.cast_one]
    exact one_ne_zero
  · obtain ⟨Phi, hPhi, hnonzero⟩ := source.isolatedCoverage u
    exact ⟨Phi, Or.inr ⟨hPhi, u, exceptional, hnonzero⟩, hnonzero⟩

include reciprocity nonnegative in
/-- A character with two constituents in the working set is the original
specified Taylor character. This follows from the proved singleton argument. -/
theorem working_two_eq_original (Phi : workingFamily source)
    (two : Fintype.card (Constituent (N := N) Phi.val) = 2) :
    Phi.val = source.distinguished := by
  rcases Phi.property with original | ⟨hPhi, u, hne, hnonzero⟩
  · exact original
  · let work := workingSource source reciprocity nonnegative
    have support : upperSupport work Phi = u := by
      by_contra h
      have zero := upperMultiplicity_eq work Phi u
      rw [if_neg (Ne.symm h)] at zero
      apply hnonzero
      rw [← upperMultiplicity_cast work Phi u, zero, Nat.cast_zero]
    have one := (singleton_irreducible work reciprocity nonnegative source.parameter Phi
      (by rw [support]; exact hne)).1
    simp only [Fintype.card_eq_nat_card] at one two
    omega

include reciprocity nonnegative in
/-- In particular the retained two-row construction uses precisely the
original Taylor character, despite its existential choice interface. -/
theorem distinguishedParent_eq_original :
    (distinguishedParent (workingSource source reciprocity nonnegative)).val =
      source.distinguished :=
  working_two_eq_original source reciprocity nonnegative _
    (distinguishedParent_card (workingSource source reciprocity nonnegative))

/-- Every selected singleton parent belongs to the isolated family. -/
theorem singletonParent_mem_isolated
    (u : {u : UpperRationalFibre upperGeometricClass C // u ≠ source.parameter.exceptional}) :
    (singletonParent (workingSource source reciprocity nonnegative) source.parameter u).val ∈
      source.isolatedFamily := by
  let work := workingSource source reciprocity nonnegative
  let parent := singletonParent work source.parameter u
  rcases parent.property with original | isolated
  · have support := singletonParent_support work source.parameter u
    have one := (singleton_irreducible work reciprocity nonnegative source.parameter parent
      (by rw [support]; exact u.property)).1
    have two : Fintype.card (Constituent (N := N) parent.val) = 2 := by
      rw [original]
      simpa only [Fintype.card_eq_nat_card] using source.distinguished_two
    simp only [Fintype.card_eq_nat_card] at one two
    omega
  · exact isolated.1

end WorkingFamily

variable (nonnegative : ∀ (rho : Irr K (Spin n F N))
    (c : UnipotentClass (r := r) (N := N)),
    ∃ a : ℕ, scalarProductRight rho.val (gamma c) = (a : K))

/-- An internal result of the classwise construction, never a final source. -/
structure SelectedClass (C : GeometricClass) where
  beforeDual : RationalFibre geometricClass C → Irr K (Spin n F N)
  label : RationalFibre geometricClass C → TypeBConformalDualCarriers.PCSp F n
  label_quasiIsolated : ∀ c, quasiIsolated (label c)
  beforeDual_series : ∀ c, rationalSeries (label c) (beforeDual c)
  beforeDual_support : ∀ c, unipotentSupport (beforeDual c) C
  diagonal : Sum
    (AbelianIdentityModel (fun c d : RationalFibre geometricClass C =>
      multiplicity gamma nonnegative (lowerDual (beforeDual c)) d.val))
    (NonabelianFibreModel (fun c d : RationalFibre geometricClass C =>
      multiplicity gamma nonnegative (lowerDual (beforeDual c)) d.val))

variable (reciprocity : FrobeniusReciprocitySource (N := N) (K := K))

/-- Construct the specified rows and diagonal alternative at one geometric
class. Nonabelian entries are the proved restriction construction. -/
def selectClass (C : GeometricClass)
    (raw : GGGRSources.LocalSources (geometricClass := geometricClass)
      (upperGeometricClass := upperGeometricClass) (geometric_square := geometric_square)
      (ComponentGroup := ComponentGroup) (gamma := gamma) (upperDual := upperDual)
      (lowerDual := lowerDual) (rationalSeries := rationalSeries)
      (quasiIsolated := quasiIsolated) (unipotentSupport := unipotentSupport)
      (parameters := parameters) (higher := rank) C) :
    SelectedClass (geometricClass := geometricClass) (gamma := gamma)
      (lowerDual := lowerDual) (rationalSeries := rationalSeries)
      (quasiIsolated := quasiIsolated) (unipotentSupport := unipotentSupport) nonnegative C := by
  classical
  rcases raw with abelian | nonabelian
  · let rows := GGGRAbelian.rows reciprocity nonnegative abelian
    refine
      { beforeDual := rows.beforeDual
        label := fun _ => rows.label
        label_quasiIsolated := fun _ => rows.label_quasiIsolated
        beforeDual_series := rows.beforeDual_series
        beforeDual_support := rows.beforeDual_support
        diagonal := Sum.inl ⟨?_⟩ }
    intro c d
    apply Nat.cast_injective (R := K)
    rw [multiplicity_cast, rows.identity_pairing]
    by_cases h : c = d <;> simp [h]
  · letI := nonabelian.upperComponentGroup
    let work := workingSource nonabelian reciprocity nonnegative
    let rows := selectedFamily work reciprocity nonnegative nonabelian.parameter
    refine
      { beforeDual := rows.beforeDual
        label := fun c => if (rows.parent c).val = nonabelian.distinguished
          then nonabelian.label else nonabelian.isolatedLabel
        label_quasiIsolated := ?_
        beforeDual_series := ?_
        beforeDual_support := ?_
        diagonal := Sum.inr rows.nonabelianModel }
    · intro c
      split_ifs
      · exact nonabelian.label_quasiIsolated
      · exact nonabelian.isolatedLabel_quasiIsolated
    · intro c
      split_ifs with original
      · exact nonabelian.restriction_series _
          (original ▸ nonabelian.distinguished_mem) _ (rows.occurrence c)
      · have isolated : (rows.parent c).val ∈ nonabelian.isolatedFamily := by
          rcases (rows.parent c).property with h | h
          · exact False.elim (original h)
          · exact h.1
        exact nonabelian.isolated_restriction_series _ isolated _ (rows.occurrence c)
    · intro c
      rcases (rows.parent c).property with original | isolated
      · exact nonabelian.restriction_support _
          (original ▸ nonabelian.distinguished_mem) _ (rows.occurrence c)
      · exact nonabelian.isolated_restriction_support _ isolated.1 _ (rows.occurrence c)

variable (sources : ∀ C, Nonempty (RationalFibre geometricClass C) →
    GGGRSources.LocalSources (geometricClass := geometricClass)
      (upperGeometricClass := upperGeometricClass) (geometric_square := geometric_square)
      (ComponentGroup := ComponentGroup) (gamma := gamma) (upperDual := upperDual)
      (lowerDual := lowerDual) (rationalSeries := rationalSeries)
      (quasiIsolated := quasiIsolated) (unipotentSupport := unipotentSupport)
      (parameters := parameters) (higher := rank) C)

/-- The same chosen classwise result, on represented classes only. -/
def classSelection (C : GeometricClass) (represented : Nonempty (RationalFibre geometricClass C)) :=
  selectClass nonnegative reciprocity C (sources C represented)

/-- The global family uses the classwise construction at the original class. -/
def beforeDual (c : UnipotentClass (r := r) (N := N)) : Irr K (Spin n F N) :=
  (classSelection nonnegative reciprocity sources (geometricClass c) ⟨⟨c, rfl⟩⟩).beforeDual
    ⟨c, rfl⟩

/-- The semisimple label is chosen for each actual rational class. -/
def rowLabel (c : UnipotentClass (r := r) (N := N)) : TypeBConformalDualCarriers.PCSp F n :=
  (classSelection nonnegative reciprocity sources (geometricClass c) ⟨⟨c, rfl⟩⟩).label
    ⟨c, rfl⟩

theorem beforeDual_on_fibre (C : GeometricClass)
    (represented : Nonempty (RationalFibre geometricClass C))
    (c : RationalFibre geometricClass C) :
    beforeDual nonnegative reciprocity sources c.val =
      (classSelection nonnegative reciprocity sources C represented).beforeDual c := by
  rcases c with ⟨c, hc⟩
  cases hc
  rfl

theorem label_quasiIsolated (c : UnipotentClass (r := r) (N := N)) :
    quasiIsolated (rowLabel nonnegative reciprocity sources c) :=
  (classSelection nonnegative reciprocity sources (geometricClass c) ⟨⟨c, rfl⟩⟩).label_quasiIsolated
    ⟨c, rfl⟩

theorem beforeDual_series (c : UnipotentClass (r := r) (N := N)) :
    rationalSeries (rowLabel nonnegative reciprocity sources c)
      (beforeDual nonnegative reciprocity sources c) :=
  (classSelection nonnegative reciprocity sources (geometricClass c) ⟨⟨c, rfl⟩⟩).beforeDual_series
    ⟨c, rfl⟩

theorem beforeDual_support (c : UnipotentClass (r := r) (N := N)) :
    unipotentSupport (beforeDual nonnegative reciprocity sources c) (geometricClass c) :=
  (classSelection nonnegative reciprocity sources (geometricClass c) ⟨⟨c, rfl⟩⟩).beforeDual_support
    ⟨c, rfl⟩

/-- The global diagonal alternatives follow from the same chosen classwise
rows. No second selection or free relabelling changes their actual characters. -/
def diagonalCases (C : GeometricClass) (represented : Nonempty (RationalFibre geometricClass C)) :
    Sum
      (AbelianIdentityModel (fun c d : RationalFibre geometricClass C =>
        multiplicity gamma nonnegative
          (lowerDual (beforeDual nonnegative reciprocity sources c.val)) d.val))
      (NonabelianFibreModel (fun c d : RationalFibre geometricClass C =>
        multiplicity gamma nonnegative
          (lowerDual (beforeDual nonnegative reciprocity sources c.val)) d.val)) := by
  have entry_eq : (fun c d : RationalFibre geometricClass C =>
      multiplicity gamma nonnegative
        (lowerDual (beforeDual nonnegative reciprocity sources c.val)) d.val) =
      (fun c d : RationalFibre geometricClass C =>
        multiplicity gamma nonnegative
          (lowerDual ((classSelection nonnegative reciprocity sources C represented).beforeDual c)) d.val) := by
    funext c d
    rw [beforeDual_on_fibre nonnegative reciprocity sources C represented c]
  rw [entry_eq]
  exact (classSelection nonnegative reciprocity sources C represented).diagonal

end ManuscriptIBAW.TypeB.GGGRSelection

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
