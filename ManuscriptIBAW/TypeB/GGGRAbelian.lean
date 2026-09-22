import ManuscriptIBAW.TypeB.GGGRSources

/-!
# Abelian components from the actual upper families

The trivial image of the centre uses upper delta rows and restriction. The
image of order two uses the distinguished character and actual
Clifford conjugation. The lower identity rows are constructed in both
cases.
-/

noncomputable section
set_option autoImplicit false

namespace ManuscriptIBAW.TypeB.GGGRAbelian

open ModularRep ModularRep.PaperProofs OrdinaryIrreducibleCharacter
open TypeBCliffordCarriers TypeBSpinRationalUnipotentClassBinding
open TypeBSpinOrdinaryRestriction TypeBSpinPrincipalProjectiveBinding
open TypeBAllRankGGGRFibres TypeBAllRankGGGREntries TypeBGGGRRankProposition412Relative
open GGGRSources
open scoped BigOperators

attribute [local instance] Classical.propDecidable
local instance finiteFintype (X : Type) [Finite X] : Fintype X :=
  Fintype.ofFinite X

private theorem sum_fintype_eq {X M : Type} [AddCommMonoid M]
    (s t : Fintype X) (a : X → M) :
    @Finset.sum X M _ (@Finset.univ X s) a =
      @Finset.sum X M _ (@Finset.univ X t) a := by
  cases Subsingleton.elim s t
  rfl

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
  {parameters : OddFieldParameters F r f} {C : GeometricClass}
  {V : Type} [Group V]
  {upperGamma : UpperRationalFibre upperGeometricClass C → SpecialClifford n F → K}
  {family : Set (Irr K (SpecialClifford n F))}

local instance upperFinite : Finite (UpperUnipotentClass (n := n) (F := F) (r := r)) := by
  let : Finite (ConjClasses (SpecialClifford n F)) :=
    Finite.of_surjective ConjClasses.mk ConjClasses.mk_surjective
  unfold UpperUnipotentClass
  infer_instance

variable (current : FamilySource (geometricClass := geometricClass)
    (geometric_square := geometric_square) (gamma := gamma)
    (upperDual := upperDual) (lowerDual := lowerDual) V parameters C upperGamma family)
  (reciprocity : FrobeniusReciprocitySource (N := N) (K := K))
  (nonnegative : ∀ (rho : Irr K (Spin n F N))
    (c : UnipotentClass (r := r) (N := N)),
    ∃ a : ℕ, scalarProductRight rho.val (gamma c) = (a : K))

local notation "π" => rationalClassMap geometricClass upperGeometricClass geometric_square C
local notation "act" => ambientClassEquiv geometricClass upperGeometricClass geometric_square C

omit [CharZero K] [HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F))]
  [HasEnoughRootsOfUnity K (Nat.card (Spin n F N))] in
include current reciprocity in
theorem restriction_pairing (Phi : family) (c : RationalFibre geometricClass C) :
    scalarProductRight (restrictionClassFunction N (upperDual Phi.val)) (gamma c.val) =
      upperScalarProduct (upperDual Phi.val).val (upperGamma (π c)) := by
  rw [reciprocity.reciprocity, current.gggrInduction]

omit [HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F))]
  [HasEnoughRootsOfUnity K (Nat.card (Spin n F N))] in
include current in
theorem entry_conjugation (Phi : family) (theta : Constituent (N := N) Phi.val)
    (g : SpecialClifford n F) (c : RationalFibre geometricClass C) :
    multiplicity gamma nonnegative
      (lowerDual (twist K (Spin n F N) theta.val
        (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹))) (act g c).val =
      multiplicity gamma nonnegative (lowerDual theta.val) c.val := by
  apply Nat.cast_injective (R := K)
  rw [multiplicity_cast, multiplicity_cast,
    current.restriction.dualityConjugation Phi.val Phi.property theta g,
    current.gggrConjugation g c]
  exact scalarProductRight_pullback N
    (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹) _ _

omit [HasEnoughRootsOfUnity K (Nat.card (Spin n F N))] in
include current in
/-- The finite character selection in manuscript Lemma 2.11 for the special
Clifford group. Under the stated assumptions on the families and trace
functions, nonnegative integral multiplicities, row sums equal to one and
coverage give distinct characters whose duals have scalar products with
the GGGRs forming the identity matrix. This is used in the abelian
singleton case of Proposition 4.9. -/
theorem upper_delta_selection
    (values : IsolatedValueSource (upperDual := upperDual) C upperGamma family) :
    ∃ select : UpperRationalFibre upperGeometricClass C → family,
      Function.Injective select ∧ ∀ j k,
        upperScalarProduct (upperDual (select j).val).val (upperGamma k) =
          if k = j then 1 else 0 := by
  have covered : ∀ j, ∃ Phi : family,
      upperScalarProduct (upperDual Phi.val).val (upperGamma j) ≠ 0 := by
    intro j
    obtain ⟨Phi, mem, nonzero⟩ := values.coverage j
    exact ⟨⟨Phi, mem⟩, nonzero⟩
  obtain ⟨select, injective, delta⟩ :=
    FiniteCharacterSelection.exists_delta_injection_of_nonnegative
    (fun Phi : family => fun j => upperScalarProduct (upperDual Phi.val).val (upperGamma j))
    (fun Phi j => current.upperNonnegative Phi.val Phi.property j)
    (fun Phi => current.upperSumOne Phi.val Phi.property) covered
  refine ⟨select, injective, ?_⟩
  intro j k
  by_cases h : k = j <;> simpa [h] using delta j k

include current reciprocity nonnegative in
/-- Pick a constituent at each upper delta row. Injectivity of the actual
class map makes all other lower entries vanish. -/
theorem singleton_rows
    (values : IsolatedValueSource (upperDual := upperDual) C upperGamma family)
    (injective : Function.Injective π) :
    ∀ c : RationalFibre geometricClass C, ∃ Phi ∈ family,
      ∃ theta : Constituent (N := N) Phi,
        ∀ d : RationalFibre geometricClass C,
          scalarProductRight (lowerDual theta.val).val (gamma d.val) =
            if c = d then 1 else 0 := by
  classical
  obtain ⟨select, _, delta⟩ := upper_delta_selection current values
  intro c
  let Phi := select (π c)
  have pair : ∀ d : RationalFibre geometricClass C,
      scalarProductRight (restrictionClassFunction N (upperDual Phi.val)) (gamma d.val) =
        if c = d then 1 else 0 := by
    intro d
    rw [restriction_pairing current reciprocity, delta]
    by_cases h : c = d
    · simp [h]
    · have ne : π d ≠ π c := fun eq => h (injective eq).symm
      simp [h, ne]
  have total := lower_column_sum_one (gamma := gamma) (nonnegative := nonnegative)
    current.restriction Phi.val Phi.property c.val (by simpa using pair c)
  have total' : (∑ theta : Constituent (N := N) Phi.val,
      multiplicity gamma nonnegative (lowerDual theta.val) c.val) = 1 :=
    (sum_fintype_eq _ _ _).trans total
  have some_entry : ∃ theta : Constituent (N := N) Phi.val,
      multiplicity gamma nonnegative (lowerDual theta.val) c.val ≠ 0 := by
    by_contra absent
    push Not at absent
    simp [absent] at total'
  obtain ⟨theta, nonzero⟩ := some_entry
  have at_c := FiniteCharacterSelection.nat_row_delta_at
    (fun theta : Constituent (N := N) Phi.val =>
      multiplicity gamma nonnegative (lowerDual theta.val) c.val) total' theta nonzero theta
  refine ⟨Phi.val, Phi.property, theta, ?_⟩
  intro d
  by_cases h : c = d
  · subst d
    rw [← multiplicity_cast gamma nonnegative (lowerDual theta.val) c.val]
    simpa using congrArg (fun a : ℕ => (a : K)) at_c
  · have zero := lower_entry_zero_of_restriction_zero
      (gamma := gamma) (nonnegative := nonnegative) current.restriction
      Phi.val Phi.property d.val (by simpa [h] using pair d) theta
    rw [← multiplicity_cast gamma nonnegative (lowerDual theta.val) d.val, zero]
    simp [h]

/-- An actual permutation exchanging the first two elements exchanges
both coordinates of a carrier with two elements. -/
private theorem exchanges_two {X : Type} (e : Fin 2 ≃ X) (p : Equiv.Perm X)
    (first : p (e 0) = e 1) : ∀ i, p (e i) = e (swapTwo i) := by
  intro i
  fin_cases i
  · simpa using first
  · have different : p (e 1) ≠ e 1 := by
      intro h
      have eq := e.injective (p.injective (first.trans h.symm))
      exact Fin.zero_ne_one eq
    have index : e.symm (p (e 1)) = 0 := by
      have ne : e.symm (p (e 1)) ≠ 1 := by
        intro h
        apply different
        simpa using congrArg e h
      have le := (e.symm (p (e 1))).isLt
      apply Fin.ext
      have neval : (e.symm (p (e 1))).val ≠ 1 := fun h => ne (Fin.ext h)
      change _ = 0
      omega
    simpa using congrArg e index

include current reciprocity nonnegative in
/-- The double case derives its column action from actual conjugation.
Clifford transitivity supplies the row exchange, and the natural column
sums then force a permutation matrix. -/
theorem double_rows
    (classes : Fin 2 ≃ RationalFibre geometricClass C)
    (upper_unique : Subsingleton (UpperRationalFibre upperGeometricClass C))
    (Phi : family) (two : Fintype.card (Constituent (N := N) Phi.val) = 2) :
    ∀ c : RationalFibre geometricClass C, ∃ theta : Constituent (N := N) Phi.val,
      ∀ d : RationalFibre geometricClass C,
        scalarProductRight (lowerDual theta.val).val (gamma d.val) =
          if c = d then 1 else 0 := by
  classical
  let := upper_unique
  let : Nonempty (UpperRationalFibre upperGeometricClass C) := ⟨π (classes 0)⟩
  have upper_one : ∀ u, upperScalarProduct (upperDual Phi.val).val (upperGamma u) = 1 := by
    intro u
    have sum_eq : (∑ v, upperScalarProduct (upperDual Phi.val).val (upperGamma v)) =
        upperScalarProduct (upperDual Phi.val).val (upperGamma u) := by
      apply Finset.sum_eq_single u
      · intro v _ different
        exact False.elim (different (Subsingleton.elim v u))
      · simp
    exact sum_eq.symm.trans (current.upperSumOne Phi.val Phi.property)
  let rows : Fin 2 ≃ Constituent (N := N) Phi.val :=
    (Fintype.equivFinOfCardEq two).symm
  let entry : Fin 2 → Fin 2 → ℕ := fun i j =>
    multiplicity gamma nonnegative (lowerDual (rows i).val) (classes j).val
  have total : ∀ j, entry 0 j + entry 1 j = 1 := by
    intro j
    have sum := lower_column_sum_one (gamma := gamma) (nonnegative := nonnegative)
      current.restriction Phi.val Phi.property (classes j).val
      ((restriction_pairing current reciprocity Phi (classes j)).trans (upper_one _))
    have sum' : (∑ theta : Constituent (N := N) Phi.val,
        multiplicity gamma nonnegative (lowerDual theta.val) (classes j).val) = 1 :=
      (sum_fintype_eq _ _ _).trans sum
    have reindex := Fintype.sum_equiv rows
      (fun i => entry i j)
      (fun theta => multiplicity gamma nonnegative (lowerDual theta.val) (classes j).val)
      (fun _ => rfl)
    rw [← reindex] at sum'
    simpa [Fin.sum_univ_two] using sum'
  obtain ⟨g, first⟩ := current.restriction.cliffordTransitive
    Phi.val Phi.property (rows 0) (rows 1)
  have row_exchange : ∀ i, constituentAction Phi g (rows i) = rows (swapTwo i) :=
    exchanges_two rows (constituentAction Phi g) (Subtype.ext first)
  let classAction : Equiv.Perm (Fin 2) := classes.trans ((act g).trans classes.symm)
  have equivariant : ∀ i j, entry (swapTwo i) (classAction j) = entry i j := by
    intro i j
    have h := entry_conjugation current nonnegative Phi (rows i) g (classes j)
    have rows_eq := congrArg Subtype.val (row_exchange i)
    change twist K (Spin n F N) (rows i).val
      (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹) = (rows (swapTwo i)).val at rows_eq
    rw [rows_eq] at h
    simpa only [entry, classAction, Equiv.trans_apply, Equiv.apply_symm_apply,
      ] using h
  obtain ⟨permutation, permutation_entry⟩ :=
    two_fibre_permutation_block entry classAction equivariant total
  intro c
  refine ⟨rows (permutation (classes.symm c)), ?_⟩
  intro d
  have h := permutation_entry (permutation (classes.symm c)) (classes.symm d)
  have eq_iff : permutation (classes.symm c) = permutation (classes.symm d) ↔ c = d :=
    permutation.injective.eq_iff.trans classes.symm.injective.eq_iff
  simp only [eq_iff] at h
  have cast_h := congrArg (fun a : ℕ => (a : K)) h
  simpa [entry, multiplicity_cast] using cast_h

/-- Internal constructed rows, used to build the retained downstream source. -/
structure Rows (C : GeometricClass) where
  beforeDual : RationalFibre geometricClass C → Irr K (Spin n F N)
  label : TypeBConformalDualCarriers.PCSp F n
  label_quasiIsolated : quasiIsolated label
  beforeDual_series : ∀ c, rationalSeries label (beforeDual c)
  beforeDual_support : ∀ c, unipotentSupport (beforeDual c) C
  identity_pairing : ∀ c d : RationalFibre geometricClass C,
    scalarProductRight (lowerDual (beforeDual c)).val (gamma d.val) =
      if c = d then 1 else 0

variable (source : GGGRSources.AbelianSource (geometricClass := geometricClass)
  (upperGeometricClass := upperGeometricClass) (geometric_square := geometric_square)
  (ComponentGroup := ComponentGroup) (gamma := gamma) (upperDual := upperDual)
  (lowerDual := lowerDual) (rationalSeries := rationalSeries)
  (quasiIsolated := quasiIsolated) (unipotentSupport := unipotentSupport) parameters C)

/-- Construct both abelian alternatives from their upper data. -/
def rows : Rows (geometricClass := geometricClass) (gamma := gamma)
    (lowerDual := lowerDual) (rationalSeries := rationalSeries)
    (quasiIsolated := quasiIsolated) (unipotentSupport := unipotentSupport) C := by
  classical
  letI := source.upperComponentGroup
  have chosen : ∀ c : RationalFibre geometricClass C, ∃ Phi ∈ source.family,
      ∃ theta : Constituent (N := N) Phi,
        ∀ d : RationalFibre geometricClass C,
          scalarProductRight (lowerDual theta.val).val (gamma d.val) =
            if c = d then 1 else 0 := by
    cases source.alternative with
    | inl singleton =>
      exact singleton_rows source.current reciprocity nonnegative
        singleton.isolatedValues singleton.classMap_injective
    | inr double =>
      have mem : double.distinguished ∈ source.family := by
        simp only [double.family_singleton, Set.mem_singleton_iff]
      intro c
      obtain ⟨theta, delta⟩ := double_rows source.current reciprocity nonnegative
        double.lowerClasses double.upperClass_unique
        ⟨double.distinguished, mem⟩ double.distinguished_two c
      exact ⟨double.distinguished, mem, theta, delta⟩
  choose parent mem theta delta using chosen
  exact {
    beforeDual := fun c => (theta c).val
    label := source.label
    label_quasiIsolated := source.label_quasiIsolated
    beforeDual_series := fun c =>
      source.restriction_series (parent c) (mem c) _ (theta c).property
    beforeDual_support := fun c =>
      source.restriction_support (parent c) (mem c) _ (theta c).property
    identity_pairing := delta }

end ManuscriptIBAW.TypeB.GGGRAbelian

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
this package's formalisation report and source records.
-/
