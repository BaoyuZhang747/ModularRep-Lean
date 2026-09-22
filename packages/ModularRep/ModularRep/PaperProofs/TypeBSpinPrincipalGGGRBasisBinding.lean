import ModularRep.PaperProofs.TypeBSpinGGGRProjectivityBinding
import ModularRep.PaperProofs.TypeBSpinGGGRPrincipalSeriesBinding
import ModularRep.PaperProofs.TypeBGGGRRankProposition412SourceInstantiation

/-!
# The rank-three GGGR basis on the specified Spin principal block

The published inputs concern actual unprojected characters, one geometric
class at a time. The component groups, geometric labels/closure, rational
series, support and normalized duality require their stated algebraic
realizations. No basis, selected-principal, projective membership or finrank
conclusion is supplied. Principal membership, projected projectivity and
dimension are obtained from the previously checked specified deductions.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBSpinPrincipalGGGRBasisBinding

open ModularRep OrdinaryIrreducibleCharacter TypeBCliffordCarriers
open TypeBSpinRationalUnipotentClassBinding TypeBSpinGGGRPrincipalSeriesBinding
open TypeBSpinPrincipalDecompositionBinding TypeBSpinPrincipalProjectiveBinding
open TypeBSpinGGGRProjectivityBinding TypeBCentralKernelBlockSource
open TypeBGGGRRankProposition412SourceInstantiation
open scoped MonoidAlgebra BigOperators

attribute [local instance] Classical.propDecidable

variable {r f : ℕ} {F K : Type} [Field F] [Finite F] [CharP F r]
  [Field K] [CharZero K] {N : NormSource 3 F} [Finite (Spin 3 F N)]

local instance finiteTypeFintype (X : Type) [Finite X] : Fintype X := Fintype.ofFinite X

variable {parameters : OddFieldParameters F r f}
  {GeometricClass : Type}
  {geometricClass : UnipotentClass (r := r) (N := N) → GeometricClass}
  {ComponentGroup : GeometricClass → Type} [∀ C, Group (ComponentGroup C)]
  {gamma : UnipotentClass (r := r) (N := N) → Spin 3 F N → K}
  {rationalSeries : TypeBConformalDualCarriers.PCSp F 3 → Irr K (Spin 3 F N) → Prop}
  {quasiIsolated : TypeBConformalDualCarriers.PCSp F 3 → Prop}
  {normalizedDual : Irr K (Spin 3 F N) → Irr K (Spin 3 F N)}
  {unipotentSupport : Irr K (Spin 3 F N) → GeometricClass → Prop}

/-- Chaneb 2.8 on each actual represented geometric fibre, with the
rank-three component-abelian input from FYZ's proof of Corollary 5.17.
The before-duality characters and their common class label are literal.
All geometric/component/source interpretations remain explicit U. -/
structure RankThreeChanebSource
    (parameters : OddFieldParameters F r f)
    (geometricClass : UnipotentClass (r := r) (N := N) → GeometricClass)
    (ComponentGroup : GeometricClass → Type) [∀ C, Group (ComponentGroup C)]
    (gamma : UnipotentClass (r := r) (N := N) → Spin 3 F N → K)
    (rationalSeries : TypeBConformalDualCarriers.PCSp F 3 → Irr K (Spin 3 F N) → Prop)
    (quasiIsolated : TypeBConformalDualCarriers.PCSp F 3 → Prop)
    (normalizedDual : Irr K (Spin 3 F N) → Irr K (Spin 3 F N))
    (unipotentSupport : Irr K (Spin 3 F N) → GeometricClass → Prop)
    [ordinaryCharacteristic : CharZero K]
    [ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card (Spin 3 F N))] where
  beforeDual : UnipotentClass (r := r) (N := N) → Irr K (Spin 3 F N)
  classLabel : GeometricClass → TypeBConformalDualCarriers.PCSp F 3
  component_abelian : ∀ c : UnipotentClass (r := r) (N := N),
    ∀ x y : ComponentGroup (geometricClass c), x * y = y * x
  label_quasiIsolated : ∀ c, quasiIsolated (classLabel (geometricClass c))
  beforeDual_series : ∀ c,
    rationalSeries (classLabel (geometricClass c)) (beforeDual c)
  beforeDual_support : ∀ c, unipotentSupport (beforeDual c) (geometricClass c)
  identity_pairing : ∀ C,
    (∀ x y : ComponentGroup C, x * y = y * x) →
    ∀ c d : RationalFibre geometricClass C,
      scalarProductRight (normalizedDual (beforeDual c.val)).val (gamma d.val) =
        if c = d then 1 else 0

/-- Taylor 14.15 and 15.2, composed only in the stated one-way support
direction. Closure is on the SAME geometric labels, with its actual
algebraic interpretation still required at source realization. -/
structure WaveFrontClosureCertificate
    (parameters : OddFieldParameters F r f)
    (geometricClass : UnipotentClass (r := r) (N := N) → GeometricClass)
    (gamma : UnipotentClass (r := r) (N := N) → Spin 3 F N → K)
    (normalizedDual : Irr K (Spin 3 F N) → Irr K (Spin 3 F N))
    (unipotentSupport : Irr K (Spin 3 F N) → GeometricClass → Prop)
    (closure : GeometricClass → GeometricClass → Prop)
    [ordinaryCharacteristic : CharZero K]
    [ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card (Spin 3 F N))] : Prop where
  nonzero_implies_closure : ∀ (rho : Irr K (Spin 3 F N)) (C : GeometricClass)
    (c : UnipotentClass (r := r) (N := N)),
    unipotentSupport rho C →
    scalarProductRight (normalizedDual rho).val (gamma c) ≠ 0 →
      closure (geometricClass c) C

/-- Enumeration data, not a source identity for geometric closure. Numeric
codes are injectively attached to the actual coarse label and composed with
the same exhaustive rational classIndex. -/
structure GeometricOrdering {m : ℕ}
    (geometricClass : UnipotentClass (r := r) (N := N) → GeometricClass)
    (classIndex : Fin m ≃ UnipotentClass (r := r) (N := N))
    (closure : GeometricClass → GeometricClass → Prop) where
  code : GeometricClass → ℕ
  code_injective : Function.Injective code
  closure_mono : ∀ C D, closure C D → code C ≤ code D
  consecutive : Monotone (fun j => code (geometricClass (classIndex j)))

variable [HasEnoughRootsOfUnity K (Nat.card (Spin 3 F N))]
  {raw : RankThreeChanebSource parameters geometricClass ComponentGroup gamma
    rationalSeries quasiIsolated normalizedDual unipotentSupport}

/-- The selected ordinary character is the normalized dual of the source
character before duality, on the actual rational Spin class. -/
def selectedOrdinary (c : UnipotentClass (r := r) (N := N)) : Irr K (Spin 3 F N) :=
  normalizedDual (raw.beforeDual c)

section Physical

variable {O k : Type} [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k]
  [Finite (Irr K (Spin 3 F N))]
  {orthogonality : OrdinaryOrthogonalitySource (N := N) (K := K)}
  {Msys : ModularSystem 2 K O k}
  {iota : PrimeRegularRootEmbedding 2 k K (Spin 3 F N)}
  {hcompat : StableReductionBrauerCharacterCompatibility Msys iota}
  {b : LiteralPrimitiveBlock k (Spin 3 F N)} {principal : IsPrincipal b}
  [Fintype (LiteralPrimitiveBlock k (Spin 3 F N))]
  {blocks : BlockIdempotentDecomposition
    (fun b : LiteralPrimitiveBlock k (Spin 3 F N) => b.val)}
  {ordinary : OrdinaryBlockSource Msys iota blocks}
  {columns : DecompositionColumnIndependenceSource Msys iota}

/-- Chaneb 2.7 and CE 21.14 give this literal rational-class/principal-
Brauer cardinal equality. It is not a projective-dimension source. -/
structure PrincipalRationalClassCount
    (parameters : OddFieldParameters F r f)
    (iota : PrimeRegularRootEmbedding 2 k K (Spin 3 F N))
    (b : LiteralPrimitiveBlock k (Spin 3 F N)) (principal : IsPrincipal b)
    [ordinaryCharacteristic : CharZero K] [residueCharacteristic : CharP k 2]
    [splittingResidue : IsAlgClosed k]
    [ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card (Spin 3 F N))] : Prop where
  card_eq : Nat.card (UnipotentClass (r := r) (N := N)) =
    Nat.card {phi : IBr iota // Supported iota b phi}

variable {series : PrincipalSeriesCertificate parameters (show 3 ≤ 3 from le_rfl)
    ordinary.ordinaryBlock b principal rationalSeries quasiIsolated normalizedDual}

include series in
/-- Principal membership follows through the literal PCSp two-series
certificate and duality, rather than being a field of the Chaneb data. -/
theorem selected_principal (c : UnipotentClass (r := r) (N := N)) :
    ordinary.ordinaryBlock
      (selectedOrdinary (raw := raw) c) = b :=
  selectedDual_principal parameters (show 3 ≤ 3 from le_rfl) ordinary.ordinaryBlock b principal
    rationalSeries quasiIsolated normalizedDual series
    (raw.classLabel (geometricClass c)) (raw.beforeDual c)
    (raw.label_quasiIsolated c) (raw.beforeDual_series c)

variable {m : ℕ} {classIndex : Fin m ≃ UnipotentClass (r := r) (N := N)}
  {closure : GeometricClass → GeometricClass → Prop}
  {ordering : GeometricOrdering geometricClass classIndex closure}
  {waveFront : WaveFrontClosureCertificate parameters geometricClass gamma
    normalizedDual unipotentSupport closure}
  {count : PrincipalRationalClassCount parameters iota b principal}
  {induction : GGGRInductionSource parameters (show 3 ≤ 3 from le_rfl) gamma}
  {expansion : OddInductionExpansionCertificate Msys iota hcompat}

/-- Nonnegative multiplicity is constructed from the SAME odd-induction
expansion and specified PIM coefficients. There is no external integrality
or multiplicity-matrix certificate. -/
def multiplicity (c d : UnipotentClass (r := r) (N := N)) : ℕ :=
  Classical.choose (gggr_scalarProduct_nonnegative parameters (show 3 ≤ 3 from le_rfl)
    gamma induction orthogonality Msys iota hcompat expansion
    (selectedOrdinary (raw := raw) c) d)

theorem multiplicity_cast (c d : UnipotentClass (r := r) (N := N)) :
    scalarProductRight (selectedOrdinary (raw := raw) c).val (gamma d) =
      (multiplicity (raw := raw) (induction := induction) (orthogonality := orthogonality)
        (Msys := Msys) (iota := iota) (hcompat := hcompat) (expansion := expansion) c d : K) :=
  Classical.choose_spec (gggr_scalarProduct_nonnegative parameters (show 3 ≤ 3 from le_rfl)
    gamma induction orthogonality Msys iota hcompat expansion
    (selectedOrdinary (raw := raw) c) d)

/-- The rank-three abelian branch gives the identity entry on the SAME
geometric fibre. No nonabelian fibre model is introduced. -/
theorem multiplicity_identity (c d : UnipotentClass (r := r) (N := N))
    (same : geometricClass c = geometricClass d) :
    multiplicity (raw := raw) (induction := induction) (orthogonality := orthogonality)
      (Msys := Msys) (iota := iota) (hcompat := hcompat) (expansion := expansion) c d =
        if c = d then 1 else 0 := by
  apply Nat.cast_injective (R := K)
  rw [← multiplicity_cast]
  have h := raw.identity_pairing (geometricClass c) (raw.component_abelian c)
    ⟨c, rfl⟩ ⟨d, same.symm⟩
  by_cases equal : c = d
  · have equal' : (⟨c, rfl⟩ : RationalFibre geometricClass (geometricClass c)) =
        ⟨d, same.symm⟩ := Subtype.ext equal
    simpa only [selectedOrdinary, if_pos equal', if_pos equal, Nat.cast_one] using h
  · have different : (⟨c, rfl⟩ : RationalFibre geometricClass (geometricClass c)) ≠
        ⟨d, same.symm⟩ := fun heq => equal (congrArg Subtype.val heq)
    simpa only [selectedOrdinary, if_neg different, if_neg equal, Nat.cast_zero] using h

include orthogonality columns count classIndex in
/-- The final dimension is composed from exhaustive class indexing, the
literal published count, and the specified PIM-span dimension theorem. -/
theorem classIndex_card_eq_finrank :
    Fintype.card (Fin m) = Module.finrank K (physicalProjectiveSpace Msys iota b) := by
  calc
    Fintype.card (Fin m) = Nat.card (UnipotentClass (r := r) (N := N)) := by
      simpa only [Nat.card_eq_fintype_card] using Nat.card_congr classIndex
    _ = Nat.card {phi : IBr iota // Supported iota b phi} := count.card_eq
    _ = Module.finrank K (physicalProjectiveSpace Msys iota b) :=
      (physicalProjectiveSpace_finrank orthogonality Msys iota columns b).symm

include waveFront in
theorem closure_vanishing (i j : Fin m)
    (higher : ordering.code (geometricClass (classIndex i)) <
      ordering.code (geometricClass (classIndex j))) :
    scalarProductRight
      (selectedOrdinary (raw := raw) (classIndex i)).val (gamma (classIndex j)) = 0 := by
  by_contra nonzero
  have below := waveFront.nonzero_implies_closure (raw.beforeDual (classIndex i))
    (geometricClass (classIndex i)) (classIndex j) (raw.beforeDual_support (classIndex i)) nonzero
  exact (Nat.not_lt_of_ge (ordering.closure_mono _ _ below)) higher

/-- The old GGGR rank interface is constructed entirely on the actual Spin
principal fibre. Every target-shaped field is filled by a checked deduction;
the external sources are only the displayed raw published statements. -/
def basisSource : GGGRBasisSource m (physicalProjectiveSpace Msys iota b) where
  gggr j := gamma (classIndex j)
  selectedOrdinary i := selectedOrdinary (raw := raw) (classIndex i)
  scalarProductRight := fun x => TypeBSpinPrincipalProjectiveBinding.scalarProductRight x
  principalProjection := principalProjection Msys iota b blocks ordinary
  principalProjection_idempotent :=
    principalProjection_idempotent orthogonality Msys iota b blocks ordinary
  principalProjection_selfAdjoint := principalProjection_selfAdjoint Msys iota b blocks ordinary
  selectedOrdinary_in_principal i :=
    principalProjection_selected orthogonality Msys iota b blocks ordinary _
      (selected_principal (raw := raw) (series := series) (classIndex i))
  principalGGGR_mem_projective j :=
    principalGGGR_mem_projective parameters (show 3 ≤ 3 from le_rfl) gamma induction
      orthogonality Msys iota hcompat b blocks ordinary expansion (classIndex j)
  multiplicity i j := multiplicity (raw := raw) (induction := induction)
    (orthogonality := orthogonality) (Msys := Msys) (iota := iota) (hcompat := hcompat)
    (expansion := expansion) (classIndex i) (classIndex j)
  scalarProduct_full_eq_multiplicity i j := multiplicity_cast (raw := raw) (induction := induction)
    (orthogonality := orthogonality) (Msys := Msys) (iota := iota) (hcompat := hcompat)
    (expansion := expansion) (classIndex i) (classIndex j)
  geometricClass i := ordering.code (geometricClass (classIndex i))
  geometricClass_mono := ordering.consecutive
  diagonalSource c := Sum.inl
    { identity_entry := by
        intro i j
        have same := ordering.code_injective (i.property.trans j.property.symm)
        have h := multiplicity_identity (raw := raw) (induction := induction)
          (orthogonality := orthogonality) (Msys := Msys) (iota := iota) (hcompat := hcompat)
          (expansion := expansion)
          (classIndex i.val) (classIndex j.val) same
        by_cases equal : i = j
        · have sameClass : classIndex i.val = classIndex j.val := congrArg (fun a => classIndex a.val) equal
          simpa only [if_pos equal, if_pos sameClass] using h
        · have different : classIndex i.val ≠ classIndex j.val := by
            intro sameClass
            exact equal (Subtype.ext (classIndex.injective sameClass))
          simpa only [if_neg equal, if_neg different] using h }
  closure_vanishing i j higher :=
    closure_vanishing (raw := raw) (classIndex := classIndex) (ordering := ordering)
      (waveFront := waveFront) i j higher
  card_eq_finrank := classIndex_card_eq_finrank (orthogonality := orthogonality)
    (Msys := Msys) (columns := columns) (classIndex := classIndex) (count := count)

end Physical

end ModularRep.PaperProofs.TypeBSpinPrincipalGGGRBasisBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
