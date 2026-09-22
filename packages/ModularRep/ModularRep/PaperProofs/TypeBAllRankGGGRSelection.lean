import ModularRep.PaperProofs.TypeBAllRankGGGREntries

/-!
# Global ordinary rows from the actual all-rank component cases

The abelian input is the exact Chaneb identity statement. The nonabelian
input consists of the actual component presentation, both compatible class
parametrisations, the same upper Taylor family and uniform BEFORE-duality
series/support statements for its actual restriction constituents.

The selected lower family and every nonabelian matrix are constructed here.
No completed lower family, diagonal model, basis or criterion is a source.
The numerical multiplicity input is internal to this helper: the specified
application supplies it from the same odd-induction PIM expansion.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBAllRankGGGRSelection

open ModularRep OrdinaryIrreducibleCharacter TypeBCliffordCarriers
open TypeBSpinRationalUnipotentClassBinding TypeBSpinOrdinaryRestriction
open TypeBSpinPrincipalProjectiveBinding TypeBAllRankGGGRFibres
open TypeBAllRankGGGREntries TypeBGGGRRankProposition412Relative

attribute [local instance] Classical.propDecidable

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

/-- Chaneb 2.8 on an actual abelian component fibre. Its ordinary rows,
label and support are the same before-duality data throughout. -/
structure AbelianSource (parameters : OddFieldParameters F r f) (rank : 4 ≤ n)
    (C : GeometricClass) where
  component_abelian : ∀ x y : ComponentGroup C, x * y = y * x
  beforeDual : RationalFibre geometricClass C → Irr K (Spin n F N)
  label : TypeBConformalDualCarriers.PCSp F n
  label_quasiIsolated : quasiIsolated label
  beforeDual_series : ∀ c, rationalSeries label (beforeDual c)
  beforeDual_support : ∀ c, unipotentSupport (beforeDual c) C
  identity_pairing : ∀ c d : RationalFibre geometricClass C,
    scalarProductRight (lowerDual (beforeDual c)).val (gamma d.val) =
      if c = d then 1 else 0

/-- Exact nonabelian source data on the SAME actual component group.
Uniform series/support clauses apply to all actual constituents of the
chosen family, before any lower row is selected. -/
structure NonabelianSource (parameters : OddFieldParameters F r f) (rank : 4 ≤ n)
    (C : GeometricClass) where
  UpperComponent : Type
  upperComponentGroup : CommGroup UpperComponent
  presentation : letI := upperComponentGroup;
    ComponentPresentation (ComponentGroup C) UpperComponent
  parameter : letI := upperComponentGroup;
    CompatibleComponentParametrisation geometricClass upperGeometricClass geometric_square
      parameters rank C (ComponentGroup C) UpperComponent presentation
  upperGamma : UpperRationalFibre upperGeometricClass C → SpecialClifford n F → K
  family : Set (Irr K (SpecialClifford n F))
  taylor : TaylorFamilySource geometricClass upperGeometricClass geometric_square C
    parameters rank gamma upperGamma family upperDual lowerDual
  label : TypeBConformalDualCarriers.PCSp F n
  label_quasiIsolated : quasiIsolated label
  restriction_series : ∀ Phi ∈ family, ∀ rho : Irr K (Spin n F N),
    occurs N Phi rho → rationalSeries label rho
  restriction_support : ∀ Phi ∈ family, ∀ rho : Irr K (Spin n F N),
    occurs N Phi rho → unipotentSupport rho C

variable {parameters : OddFieldParameters F r f} {rank : 4 ≤ n}

/-- The case sources are supplied only for represented geometric classes.
Neither alternative contains a nonabelian lower matrix or completed basis. -/
abbrev LocalSources (C : GeometricClass) :=
  Sum
    (AbelianSource (geometricClass := geometricClass) (ComponentGroup := ComponentGroup)
      (gamma := gamma) (lowerDual := lowerDual) (rationalSeries := rationalSeries)
      (quasiIsolated := quasiIsolated) (unipotentSupport := unipotentSupport) parameters rank C)
    (NonabelianSource (geometricClass := geometricClass)
      (upperGeometricClass := upperGeometricClass) (geometric_square := geometric_square)
      (ComponentGroup := ComponentGroup) (gamma := gamma) (upperDual := upperDual)
      (lowerDual := lowerDual) (rationalSeries := rationalSeries)
      (quasiIsolated := quasiIsolated) (unipotentSupport := unipotentSupport) parameters rank C)

variable (nonnegative : ∀ (rho : Irr K (Spin n F N))
    (c : UnipotentClass (r := r) (N := N)),
    ∃ a : ℕ, scalarProductRight rho.val (gamma c) = (a : K))

/-- An internal result of the classwise construction, never a final source. -/
structure SelectedClass (C : GeometricClass) where
  beforeDual : RationalFibre geometricClass C → Irr K (Spin n F N)
  label : TypeBConformalDualCarriers.PCSp F n
  label_quasiIsolated : quasiIsolated label
  beforeDual_series : ∀ c, rationalSeries label (beforeDual c)
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
    (raw : LocalSources (geometricClass := geometricClass)
      (upperGeometricClass := upperGeometricClass) (geometric_square := geometric_square)
      (ComponentGroup := ComponentGroup) (gamma := gamma) (upperDual := upperDual)
      (lowerDual := lowerDual) (rationalSeries := rationalSeries)
      (quasiIsolated := quasiIsolated) (unipotentSupport := unipotentSupport)
      (parameters := parameters) (rank := rank) C) :
    SelectedClass (geometricClass := geometricClass) (gamma := gamma)
      (lowerDual := lowerDual) (rationalSeries := rationalSeries)
      (quasiIsolated := quasiIsolated) (unipotentSupport := unipotentSupport) nonnegative C := by
  classical
  rcases raw with abelian | nonabelian
  · refine
      { beforeDual := abelian.beforeDual
        label := abelian.label
        label_quasiIsolated := abelian.label_quasiIsolated
        beforeDual_series := abelian.beforeDual_series
        beforeDual_support := abelian.beforeDual_support
        diagonal := Sum.inl ⟨?_⟩ }
    intro c d
    apply Nat.cast_injective (R := K)
    rw [multiplicity_cast, abelian.identity_pairing]
    by_cases h : c = d <;> simp [h]
  · letI := nonabelian.upperComponentGroup
    let rows := selectedFamily nonabelian.taylor reciprocity nonnegative nonabelian.parameter
    exact
      { beforeDual := rows.beforeDual
        label := nonabelian.label
        label_quasiIsolated := nonabelian.label_quasiIsolated
        beforeDual_series := fun c => nonabelian.restriction_series
          (rows.parent c).val (rows.parent c).property (rows.beforeDual c) (rows.occurrence c)
        beforeDual_support := fun c => nonabelian.restriction_support
          (rows.parent c).val (rows.parent c).property (rows.beforeDual c) (rows.occurrence c)
        diagonal := Sum.inr rows.nonabelianModel }

variable (sources : ∀ C, Nonempty (RationalFibre geometricClass C) →
    LocalSources (geometricClass := geometricClass)
      (upperGeometricClass := upperGeometricClass) (geometric_square := geometric_square)
      (ComponentGroup := ComponentGroup) (gamma := gamma) (upperDual := upperDual)
      (lowerDual := lowerDual) (rationalSeries := rationalSeries)
      (quasiIsolated := quasiIsolated) (unipotentSupport := unipotentSupport)
      (parameters := parameters) (rank := rank) C)

/-- The same chosen classwise result, on represented classes only. -/
def classSelection (C : GeometricClass) (represented : Nonempty (RationalFibre geometricClass C)) :=
  selectClass nonnegative reciprocity C (sources C represented)

/-- The global family uses the classwise construction at the original class. -/
def beforeDual (c : UnipotentClass (r := r) (N := N)) : Irr K (Spin n F N) :=
  (classSelection nonnegative reciprocity sources (geometricClass c) ⟨⟨c, rfl⟩⟩).beforeDual
    ⟨c, rfl⟩

/-- Unrepresented labels have an unused value; no source is requested there. -/
def classLabel (C : GeometricClass) : TypeBConformalDualCarriers.PCSp F n :=
  if h : Nonempty (RationalFibre geometricClass C) then
    (classSelection nonnegative reciprocity sources C h).label else 1

theorem beforeDual_on_fibre (C : GeometricClass)
    (represented : Nonempty (RationalFibre geometricClass C))
    (c : RationalFibre geometricClass C) :
    beforeDual nonnegative reciprocity sources c.val =
      (classSelection nonnegative reciprocity sources C represented).beforeDual c := by
  rcases c with ⟨c, hc⟩
  cases hc
  rfl

theorem label_quasiIsolated (c : UnipotentClass (r := r) (N := N)) :
    quasiIsolated (classLabel nonnegative reciprocity sources (geometricClass c)) := by
  have represented : Nonempty (RationalFibre geometricClass (geometricClass c)) := ⟨⟨c, rfl⟩⟩
  simp only [classLabel, dif_pos represented]
  exact (classSelection nonnegative reciprocity sources (geometricClass c) represented).label_quasiIsolated

theorem beforeDual_series (c : UnipotentClass (r := r) (N := N)) :
    rationalSeries (classLabel nonnegative reciprocity sources (geometricClass c))
      (beforeDual nonnegative reciprocity sources c) := by
  have represented : Nonempty (RationalFibre geometricClass (geometricClass c)) := ⟨⟨c, rfl⟩⟩
  simp only [classLabel, dif_pos represented, beforeDual]
  exact (classSelection nonnegative reciprocity sources (geometricClass c) represented).beforeDual_series
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

end ModularRep.PaperProofs.TypeBAllRankGGGRSelection


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
