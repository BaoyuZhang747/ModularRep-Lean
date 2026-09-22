import ModularRep.PaperProofs.TypeBAllRankGGGRBasis
import ModularRep.PaperProofs.TypeBAllRankGGGREntriesRestriction

/-!
# Supporting specified-source construction for the all-rank Spin GGGR basis

This is an internal builder, not the final all-rank application.  Its
before-duality family and classwise diagonal alternatives must be constructed
by that application from the abelian source and the specified nonabelian
restriction argument.  Neither may be an external final-endpoint premise.

Principal membership, natural multiplicities, projectivity and dimension
are derived using the existing actual Spin providers.  The classwise models
are transported through the same exhaustive rational-class enumeration and
injective geometric code.  Empty numeric fibres are handled internally.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBAllRankGGGR.BasisPhysical

open ModularRep OrdinaryIrreducibleCharacter TypeBCliffordCarriers
open TypeBSpinRationalUnipotentClassBinding TypeBSpinGGGRPrincipalSeriesBinding
open TypeBSpinPrincipalDecompositionBinding TypeBSpinPrincipalProjectiveBinding
open TypeBSpinGGGRProjectivityBinding TypeBCentralKernelBlockSource
open TypeBGGGRRankProposition412Relative TypeBGGGRRankProposition412SourceInstantiation
open scoped MonoidAlgebra

attribute [local instance] Classical.propDecidable

local instance finiteTypeFintype (X : Type) [Finite X] : Fintype X :=
  Fintype.ofFinite X

/-- Transport of an already derived diagonal alternative. This helper
retains the original nonabelian model and only changes its index carrier. -/
def transportDiagonalModels {I J : Type} [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) (entry : J → J → ℕ)
    (source : Sum (AbelianIdentityModel entry) (NonabelianFibreModel.{0, 0} entry)) :
    Sum (AbelianIdentityModel (fun i j => entry (e i) (e j)))
      (NonabelianFibreModel.{0, 0} (fun i j => entry (e i) (e j))) := by
  rcases source with abelian | nonabelian
  · refine Sum.inl ⟨?_⟩
    intro i j
    rw [abelian.identity_entry]
    by_cases equal : i = j
    · simp only [equal, if_pos rfl]
    · have different : e i ≠ e j := fun h => equal (e.injective h)
      simp only [if_neg different, if_neg equal]
  · exact Sum.inr
      { Singleton := nonabelian.Singleton
        singletonDecidableEq := nonabelian.singletonDecidableEq
        relabel := e.trans nonabelian.relabel
        twoEntry := nonabelian.twoEntry
        entry_relabel := fun i j => nonabelian.entry_relabel (e i) (e j)
        classAction := nonabelian.classAction
        equivariant := nonabelian.equivariant
        column_sum_one := nonabelian.column_sum_one }

variable {n r f : ℕ} {F K : Type} [Field F] [Finite F] [CharP F r]
  [Field K] [CharZero K] {N : NormSource n F} [Finite (Spin n F N)]
  {parameters : OddFieldParameters F r f} {rank : 4 ≤ n}
  {GeometricClass : Type}
  {geometricClass : UnipotentClass (r := r) (N := N) → GeometricClass}
  {gamma : UnipotentClass (r := r) (N := N) → Spin n F N → K}
  {beforeDual : UnipotentClass (r := r) (N := N) → Irr K (Spin n F N)}
  {lowerDual : Irr K (Spin n F N) → Irr K (Spin n F N)}
  {unipotentSupport : Irr K (Spin n F N) → GeometricClass → Prop}

/-- The same exhaustive rational-class enumeration, grouped consecutively
by an injective code that respects the actual geometric closure relation. -/
structure GeometricOrdering {m : ℕ}
    (geometricClass : UnipotentClass (r := r) (N := N) → GeometricClass)
    (classIndex : Fin m ≃ UnipotentClass (r := r) (N := N))
    (closure : GeometricClass → GeometricClass → Prop) where
  code : GeometricClass → ℕ
  code_injective : Function.Injective code
  closure_mono : ∀ C D, closure C D → code C ≤ code D
  consecutive : Monotone (fun j => code (geometricClass (classIndex j)))

/-- Taylor 14.15 and 15.2, only in the support-to-closure direction, on the
actual Spin characters and GGGR values. All source realizations remain U. -/
structure WaveFrontClosureCertificate
    (parameters : OddFieldParameters F r f) (rank : 4 ≤ n)
    (geometricClass : UnipotentClass (r := r) (N := N) → GeometricClass)
    (gamma : UnipotentClass (r := r) (N := N) → Spin n F N → K)
    (lowerDual : Irr K (Spin n F N) → Irr K (Spin n F N))
    (unipotentSupport : Irr K (Spin n F N) → GeometricClass → Prop)
    (closure : GeometricClass → GeometricClass → Prop) : Prop where
  nonzero_implies_closure : ∀ (rho : Irr K (Spin n F N)) (C : GeometricClass)
    (c : UnipotentClass (r := r) (N := N)),
    unipotentSupport rho C →
    scalarProductRight (lowerDual rho).val (gamma c) ≠ 0 →
      closure (geometricClass c) C

/-- The selected ordinary row is the normalized dual of the internally
constructed before-duality family, at its actual rational class. -/
def selectedOrdinary (c : UnipotentClass (r := r) (N := N)) : Irr K (Spin n F N) :=
  lowerDual (beforeDual c)

variable {m : ℕ} {classIndex : Fin m ≃ UnipotentClass (r := r) (N := N)}
  {closure : GeometricClass → GeometricClass → Prop}
  {ordering : GeometricOrdering geometricClass classIndex closure}

/-- Numeric fibres use the actual class map composed with classIndex. -/
def numericClass (j : Fin m) : ℕ := ordering.code (geometricClass (classIndex j))

/-- The exact actual-rational/numeric fibre join induced by classIndex.
The underlying rational class is literally classIndex of the numeric row. -/
def numericFibreEquiv (C : GeometricClass) :
    GeometricFibre (numericClass (ordering := ordering)) (ordering.code C) ≃
      RationalFibre geometricClass C where
  toFun i := ⟨classIndex i.val, ordering.code_injective i.property⟩
  invFun c := ⟨classIndex.symm c.val, by
    change ordering.code (geometricClass (classIndex (classIndex.symm c.val))) = ordering.code C
    rw [classIndex.apply_symm_apply, c.property]⟩
  left_inv i := by
    apply Subtype.ext
    exact classIndex.symm_apply_apply i.val
  right_inv c := by
    apply Subtype.ext
    exact classIndex.apply_symm_apply c.val

@[simp] theorem numericFibreEquiv_val (C : GeometricClass)
    (i : GeometricFibre (numericClass (ordering := ordering)) (ordering.code C)) :
    ((numericFibreEquiv (ordering := ordering) C) i).val = classIndex i.val := rfl

/-- The same literal fibre equivalence at an equal numeric code. Its
structure and inverse proofs are terms, with no dependent tactic transport. -/
def numericFibreEquivAt (C : GeometricClass) (a : ℕ) (same : ordering.code C = a) :
    GeometricFibre (numericClass (ordering := ordering)) a ≃
      RationalFibre geometricClass C where
  toFun i := ⟨classIndex i.val, ordering.code_injective (i.property.trans same.symm)⟩
  invFun c := ⟨classIndex.symm c.val,
    (congrArg ordering.code
      ((congrArg geometricClass (classIndex.apply_symm_apply c.val)).trans c.property)).trans same⟩
  left_inv i := Subtype.ext (classIndex.symm_apply_apply i.val)
  right_inv c := Subtype.ext (classIndex.apply_symm_apply c.val)

/-- Transport a literal entry function through the exhaustive classIndex.
Only the actual class map and internally constructed diagonal alternatives are used. -/
def numericDiagonalSourceCore
    (matrixEntry : UnipotentClass (r := r) (N := N) →
      UnipotentClass (r := r) (N := N) → ℕ)
    (classwise : ∀ C, Nonempty (RationalFibre geometricClass C) →
      Sum
        (AbelianIdentityModel
          (fun c d : RationalFibre geometricClass C => matrixEntry c.val d.val))
        (NonabelianFibreModel.{0, 0}
          (fun c d : RationalFibre geometricClass C => matrixEntry c.val d.val)))
    (a : ℕ) :
    Sum
      (AbelianIdentityModel
        (fun i j : GeometricFibre (numericClass (ordering := ordering)) a =>
          matrixEntry (classIndex i.val) (classIndex j.val)))
      (NonabelianFibreModel.{0, 0}
        (fun i j : GeometricFibre (numericClass (ordering := ordering)) a =>
          matrixEntry (classIndex i.val) (classIndex j.val))) :=
  if represented : ∃ i : Fin m, numericClass (ordering := ordering) i = a then
    let i := Classical.choose represented
    let C := geometricClass (classIndex i)
    transportDiagonalModels
      (numericFibreEquivAt (ordering := ordering) C a (Classical.choose_spec represented))
      (fun c d : RationalFibre geometricClass C => matrixEntry c.val d.val)
      (classwise C ⟨⟨classIndex i, rfl⟩⟩)
  else
    Sum.inl ⟨fun i _ => False.elim (represented ⟨i.val, i.property⟩)⟩

section Physical

variable [HasEnoughRootsOfUnity K (Nat.card (Spin n F N))]
  [Finite (Irr K (Spin n F N))]
  {O k : Type} [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k]
  {orthogonality : OrdinaryOrthogonalitySource (N := N) (K := K)}
  {Msys : ModularSystem 2 K O k}
  {iota : PrimeRegularRootEmbedding 2 k K (Spin n F N)}
  {hcompat : StableReductionBrauerCharacterCompatibility Msys iota}
  {b : LiteralPrimitiveBlock k (Spin n F N)} {principal : IsPrincipal b}
  [Fintype (LiteralPrimitiveBlock k (Spin n F N))]
  {blocks : BlockIdempotentDecomposition
    (fun c : LiteralPrimitiveBlock k (Spin n F N) => c.val)}
  {ordinary : OrdinaryBlockSource Msys iota blocks}
  {columns : DecompositionColumnIndependenceSource Msys iota}
  {rationalSeries : TypeBConformalDualCarriers.PCSp F n → Irr K (Spin n F N) → Prop}
  {quasiIsolated : TypeBConformalDualCarriers.PCSp F n → Prop}
  {classLabel : GeometricClass → TypeBConformalDualCarriers.PCSp F n}
  {series : PrincipalSeriesCertificate parameters
    (Nat.le_trans (show 3 ≤ 4 by decide) rank)
    ordinary.ordinaryBlock b principal rationalSeries quasiIsolated lowerDual}

/-- The literal rational-class/principal-Brauer count, prior to either PIM
dimension formula. Its Chaneb/CE algebraic interpretation remains explicit U. -/
structure PrincipalRationalClassCount
    (parameters : OddFieldParameters F r f) (rank : 4 ≤ n)
    (iota : PrimeRegularRootEmbedding 2 k K (Spin n F N))
    (b : LiteralPrimitiveBlock k (Spin n F N)) (principal : IsPrincipal b)
    [ordinaryCharacteristic : CharZero K] [residueCharacteristic : CharP k 2]
    [splittingResidue : IsAlgClosed k]
    [ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card (Spin n F N))] : Prop where
  card_eq : Nat.card (UnipotentClass (r := r) (N := N)) =
    Nat.card {phi : IBr iota // Supported iota b phi}

variable {label_quasiIsolated : ∀ c, quasiIsolated (classLabel (geometricClass c))}
  {beforeDual_series : ∀ c, rationalSeries (classLabel (geometricClass c)) (beforeDual c)}
  {beforeDual_support : ∀ c, unipotentSupport (beforeDual c) (geometricClass c)}
  {waveFront : WaveFrontClosureCertificate parameters rank geometricClass gamma
    lowerDual unipotentSupport closure}
  {count : PrincipalRationalClassCount parameters rank iota b principal}
  {induction : GGGRInductionSource parameters
    (Nat.le_trans (show 3 ≤ 4 by decide) rank) gamma}
  {expansion : OddInductionExpansionCertificate Msys iota hcompat}

include series label_quasiIsolated beforeDual_series in
/-- Principal membership is derived for the SAME selected family from its
quasi-isolated labels before duality and the literal principal-series source. -/
theorem selected_principal (c : UnipotentClass (r := r) (N := N)) :
    ordinary.ordinaryBlock (selectedOrdinary (beforeDual := beforeDual) (lowerDual := lowerDual) c) = b :=
  selectedDual_principal parameters (Nat.le_trans (show 3 ≤ 4 by decide) rank)
    ordinary.ordinaryBlock b principal rationalSeries quasiIsolated lowerDual series
    (classLabel (geometricClass c)) (beforeDual c)
    (label_quasiIsolated c) (beforeDual_series c)

include induction orthogonality expansion in
/-- The natural scalar-product certificate used by the specified entries
writer is obtained from the SAME actual odd-induction/PIM expansion. -/
theorem nonnegative (theta : Irr K (Spin n F N))
    (c : UnipotentClass (r := r) (N := N)) :
    ∃ a : ℕ, scalarProductRight theta.val (gamma c) = (a : K) :=
  gggr_scalarProduct_nonnegative parameters (Nat.le_trans (show 3 ≤ 4 by decide) rank)
    gamma induction orthogonality Msys iota hcompat expansion theta c

/-- Exactly the entries module's multiplicity, with nonnegativity derived
from the specified PIM expansion. Other proofs of this same proposition agree
by proof irrelevance. -/
def entry (c d : UnipotentClass (r := r) (N := N)) : ℕ :=
  TypeBAllRankGGGREntries.multiplicity gamma
    (nonnegative (parameters := parameters) (rank := rank) (induction := induction)
      (orthogonality := orthogonality) (Msys := Msys) (iota := iota)
      (hcompat := hcompat) (expansion := expansion))
    (lowerDual (beforeDual c)) d

local notation "actualEntry" => entry (parameters := parameters) (rank := rank)
  (gamma := gamma) (beforeDual := beforeDual) (lowerDual := lowerDual)
  (induction := induction) (orthogonality := orthogonality) (Msys := Msys)
  (iota := iota) (hcompat := hcompat) (expansion := expansion)

theorem entry_cast (c d : UnipotentClass (r := r) (N := N)) :
    scalarProductRight (lowerDual (beforeDual c)).val (gamma d) = (actualEntry c d : K) :=
  (TypeBAllRankGGGREntries.multiplicity_cast gamma
    (nonnegative (parameters := parameters) (rank := rank) (induction := induction)
      (orthogonality := orthogonality) (Msys := Msys) (iota := iota)
      (hcompat := hcompat) (expansion := expansion))
    (lowerDual (beforeDual c)) d).symm

/-- Transport the INTERNAL derived classwise alternative through the
actual classIndex. The specified cases are explicit; the structural work is
performed by numericDiagonalSourceCore with these exact natural entries. -/
def numericDiagonalSource
    (diagonalCases : ∀ C, Nonempty (RationalFibre geometricClass C) →
      Sum
        (AbelianIdentityModel
          (fun c d : RationalFibre geometricClass C =>
            entry (parameters := parameters) (rank := rank)
              (gamma := gamma) (beforeDual := beforeDual) (lowerDual := lowerDual)
              (induction := induction) (orthogonality := orthogonality) (Msys := Msys)
              (iota := iota) (hcompat := hcompat) (expansion := expansion) c.val d.val))
        (NonabelianFibreModel.{0, 0}
          (fun c d : RationalFibre geometricClass C =>
            entry (parameters := parameters) (rank := rank)
              (gamma := gamma) (beforeDual := beforeDual) (lowerDual := lowerDual)
              (induction := induction) (orthogonality := orthogonality) (Msys := Msys)
              (iota := iota) (hcompat := hcompat) (expansion := expansion) c.val d.val)))
    (a : ℕ) :
    Sum
      (AbelianIdentityModel
        (fun i j : GeometricFibre (numericClass (ordering := ordering)) a =>
          entry (parameters := parameters) (rank := rank)
              (gamma := gamma) (beforeDual := beforeDual) (lowerDual := lowerDual)
              (induction := induction) (orthogonality := orthogonality) (Msys := Msys)
              (iota := iota) (hcompat := hcompat) (expansion := expansion) (classIndex i.val) (classIndex j.val)))
      (NonabelianFibreModel.{0, 0}
        (fun i j : GeometricFibre (numericClass (ordering := ordering)) a =>
          entry (parameters := parameters) (rank := rank)
              (gamma := gamma) (beforeDual := beforeDual) (lowerDual := lowerDual)
              (induction := induction) (orthogonality := orthogonality) (Msys := Msys)
              (iota := iota) (hcompat := hcompat) (expansion := expansion) (classIndex i.val) (classIndex j.val))) :=
  numericDiagonalSourceCore (ordering := ordering)
    (entry (parameters := parameters) (rank := rank)
              (gamma := gamma) (beforeDual := beforeDual) (lowerDual := lowerDual)
              (induction := induction) (orthogonality := orthogonality) (Msys := Msys)
              (iota := iota) (hcompat := hcompat) (expansion := expansion)) diagonalCases a

include orthogonality columns count classIndex in
/-- The specified dimension is derived from exhaustive actual class indexing,
the literal principal-Brauer count and the same decomposition-column theorem. -/
theorem classIndex_card_eq_finrank :
    Fintype.card (Fin m) = Module.finrank K (physicalProjectiveSpace Msys iota b) := by
  calc
    Fintype.card (Fin m) = Nat.card (UnipotentClass (r := r) (N := N)) := by
      simpa only [Nat.card_eq_fintype_card] using Nat.card_congr classIndex
    _ = Nat.card {phi : IBr iota // Supported iota b phi} := count.card_eq
    _ = Module.finrank K (physicalProjectiveSpace Msys iota b) :=
      (physicalProjectiveSpace_finrank orthogonality Msys iota columns b).symm

include waveFront beforeDual_support in
/-- Closure vanishing specializes the uniform support statement to the SAME
internally selected before-duality rows and the SAME actual GGGR columns. -/
theorem closure_vanishing (i j : Fin m)
    (higher : numericClass (ordering := ordering) i < numericClass (ordering := ordering) j) :
    scalarProductRight (lowerDual (beforeDual (classIndex i))).val (gamma (classIndex j)) = 0 := by
  by_contra nonzero
  have below := waveFront.nonzero_implies_closure (beforeDual (classIndex i))
    (geometricClass (classIndex i)) (classIndex j) (beforeDual_support (classIndex i)) nonzero
  exact (Nat.not_lt_of_ge (ordering.closure_mono _ _ below)) higher

/-- Supporting internal specified construction. The application must construct
beforeDual and diagonalCases; exposing either completed selected data or the
diagonal model as a final source would bypass the nonabelian deduction. -/
def basisSource
    (diagonalCases : ∀ C, Nonempty (RationalFibre geometricClass C) →
      Sum
        (AbelianIdentityModel
          (fun c d : RationalFibre geometricClass C =>
            entry (parameters := parameters) (rank := rank)
              (gamma := gamma) (beforeDual := beforeDual) (lowerDual := lowerDual)
              (induction := induction) (orthogonality := orthogonality) (Msys := Msys)
              (iota := iota) (hcompat := hcompat) (expansion := expansion) c.val d.val))
        (NonabelianFibreModel.{0, 0}
          (fun c d : RationalFibre geometricClass C =>
            entry (parameters := parameters) (rank := rank)
              (gamma := gamma) (beforeDual := beforeDual) (lowerDual := lowerDual)
              (induction := induction) (orthogonality := orthogonality) (Msys := Msys)
              (iota := iota) (hcompat := hcompat) (expansion := expansion) c.val d.val)))
    : GGGRBasisSource m (physicalProjectiveSpace Msys iota b) where
  gggr j := gamma (classIndex j)
  selectedOrdinary i := lowerDual (beforeDual (classIndex i))
  scalarProductRight := fun x => TypeBSpinPrincipalProjectiveBinding.scalarProductRight x
  principalProjection := principalProjection Msys iota b blocks ordinary
  principalProjection_idempotent :=
    principalProjection_idempotent orthogonality Msys iota b blocks ordinary
  principalProjection_selfAdjoint := principalProjection_selfAdjoint Msys iota b blocks ordinary
  selectedOrdinary_in_principal i :=
    principalProjection_selected orthogonality Msys iota b blocks ordinary _
      (selected_principal (parameters := parameters) (rank := rank)
        (beforeDual := beforeDual) (lowerDual := lowerDual)
        (series := series) (label_quasiIsolated := label_quasiIsolated)
        (beforeDual_series := beforeDual_series) (classIndex i))
  principalGGGR_mem_projective j :=
    principalGGGR_mem_projective parameters (Nat.le_trans (show 3 ≤ 4 by decide) rank)
      gamma induction orthogonality Msys iota hcompat b blocks ordinary expansion (classIndex j)
  multiplicity i j := actualEntry (classIndex i) (classIndex j)
  scalarProduct_full_eq_multiplicity i j :=
    entry_cast (parameters := parameters) (rank := rank) (gamma := gamma)
      (beforeDual := beforeDual) (lowerDual := lowerDual) (induction := induction)
      (orthogonality := orthogonality) (Msys := Msys) (iota := iota)
      (hcompat := hcompat) (expansion := expansion) (classIndex i) (classIndex j)
  geometricClass := numericClass (ordering := ordering)
  geometricClass_mono := ordering.consecutive
  diagonalSource := numericDiagonalSource (parameters := parameters) (rank := rank)
    (gamma := gamma) (beforeDual := beforeDual) (lowerDual := lowerDual)
    (orthogonality := orthogonality) (Msys := Msys) (iota := iota)
    (hcompat := hcompat) (induction := induction) (expansion := expansion)
    (classIndex := classIndex) (ordering := ordering) diagonalCases
  closure_vanishing i j higher :=
    closure_vanishing (parameters := parameters) (rank := rank)
      (beforeDual := beforeDual) (lowerDual := lowerDual)
      (classIndex := classIndex) (ordering := ordering) (waveFront := waveFront)
      (beforeDual_support := beforeDual_support) i j higher
  card_eq_finrank := classIndex_card_eq_finrank (parameters := parameters) (rank := rank)
    (orthogonality := orthogonality)
    (Msys := Msys) (columns := columns) (classIndex := classIndex) (count := count)

/- The output equations mention these cases in their statements. -/
variable
    (diagonalCases : ∀ C, Nonempty (RationalFibre geometricClass C) →
      Sum
        (AbelianIdentityModel
          (fun c d : RationalFibre geometricClass C =>
            entry (parameters := parameters) (rank := rank)
              (gamma := gamma) (beforeDual := beforeDual) (lowerDual := lowerDual)
              (induction := induction) (orthogonality := orthogonality) (Msys := Msys)
              (iota := iota) (hcompat := hcompat) (expansion := expansion) c.val d.val))
        (NonabelianFibreModel.{0, 0}
          (fun c d : RationalFibre geometricClass C =>
            entry (parameters := parameters) (rank := rank)
              (gamma := gamma) (beforeDual := beforeDual) (lowerDual := lowerDual)
              (induction := induction) (orthogonality := orthogonality) (Msys := Msys)
              (iota := iota) (hcompat := hcompat) (expansion := expansion) c.val d.val)))

local notation "physicalSource" => basisSource (parameters := parameters) (rank := rank)
  (gamma := gamma) (beforeDual := beforeDual) (lowerDual := lowerDual)
  (orthogonality := orthogonality) (Msys := Msys) (iota := iota) (hcompat := hcompat)
  (b := b) (principal := principal) (blocks := blocks) (ordinary := ordinary)
  (columns := columns) (series := series) (classIndex := classIndex) (ordering := ordering)
  (label_quasiIsolated := label_quasiIsolated) (beforeDual_series := beforeDual_series)
  (beforeDual_support := beforeDual_support) (waveFront := waveFront) (count := count)
  (induction := induction) (expansion := expansion) diagonalCases

@[simp] theorem basisSource_gggr (j : Fin m) :
    (physicalSource).gggr j = gamma (classIndex j) := rfl

@[simp] theorem basisSource_principalProjection :
    (physicalSource).principalProjection = principalProjection Msys iota b blocks ordinary := rfl

@[simp] theorem basisSource_selectedOrdinary (j : Fin m) :
    (physicalSource).selectedOrdinary j = lowerDual (beforeDual (classIndex j)) := rfl

/-- The actual projected scalar-product matrix has the SAME derived
natural entries used in the specified restriction argument. -/
theorem basisSource_scalarProductMatrix_apply (i j : Fin m) :
    (physicalSource).scalarProductMatrix i j = (actualEntry (classIndex i) (classIndex j) : K) :=
  (physicalSource).scalarProductMatrix_apply i j

/-- The row permutation constructed by the checked finite argument stays
inside the SAME actual geometric class, not merely its numeric label. -/
theorem basisSource_rowPermutation_preserves_geometricClass (i : Fin m) :
    geometricClass (classIndex ((physicalSource).rowPermutation i)) =
      geometricClass (classIndex i) :=
  ordering.code_injective ((physicalSource).rowPermutation_preserves_class i)

/-- The diagonal permutation equation is on the SAME actual geometric
classes and on the actual projected scalar-product matrix. -/
theorem basisSource_same_geometricClass_entry (i j : Fin m)
    (same : geometricClass (classIndex i) = geometricClass (classIndex j)) :
    (physicalSource).scalarProductMatrix ((physicalSource).rowPermutation i) j =
      if i = j then 1 else 0 :=
  (physicalSource).closurePermutationData.same_class_entry i j (congrArg ordering.code same)

/-- The projected scalar-product matrix has the required closure vanishing
after the internally derived row permutation. -/
theorem basisSource_projected_closure_vanishing (i j : Fin m)
    (higher : numericClass (ordering := ordering) i < numericClass (ordering := ordering) j) :
    (physicalSource).scalarProductMatrix ((physicalSource).rowPermutation i) j = 0 := by
  apply (physicalSource).closurePermutationData.closure_vanishing i j
  change (physicalSource).geometricClass ((physicalSource).rowPermutation i) <
    (physicalSource).geometricClass j
  rw [(physicalSource).rowPermutation_preserves_class]
  exact higher

end Physical

end ModularRep.PaperProofs.TypeBAllRankGGGR.BasisPhysical


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
