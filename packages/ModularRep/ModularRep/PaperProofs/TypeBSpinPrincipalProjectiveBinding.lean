import ModularRep.PaperProofs.TypeBCliffordCarriers
import ModularRep.PaperProofs.TypeBPrincipalSelectorCorollary413SourceInstantiation
import ModularRep.PaperProofs.TypeBSpinPrincipalDecompositionBinding
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

/-!
# Literal Spin projective-character formulas

The scalar product and Fourier projection are explicit on all functions on
the actual Clifford-kernel Spin carrier. Ordinary orthogonality is retained
over the chosen splitting field; algebraic closure of that fraction field
is not assumed. The resulting finite-dimensional calculations are kernel
deductions. The specified decomposition-number adapter is defined below.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBSpinPrincipalProjectiveBinding

open ModularRep OrdinaryIrreducibleCharacter TypeBCliffordCarriers
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {n : ℕ} {F K : Type} [Field F] [Field K] [CharZero K]
  {N : NormSource n F} [Finite (Spin n F N)]

local instance finiteTypeFintype (X : Type) [Finite X] : Fintype X :=
  Fintype.ofFinite X

/-- The ordinary bilinear scalar product, linear in its right argument. -/
def scalarProductRight (x : Spin n F N → K) : (Spin n F N → K) →ₗ[K] K where
  toFun y := (Nat.card (Spin n F N) : K)⁻¹ * ∑ g, x g⁻¹ * y g
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a y := by
    simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

theorem scalarProductRight_apply (x y : Spin n F N → K) :
    scalarProductRight x y =
      (Nat.card (Spin n F N) : K)⁻¹ * ∑ g, x g⁻¹ * y g := rfl

theorem scalarProductRight_comm (x y : Spin n F N → K) :
    scalarProductRight x y = scalarProductRight y x := by
  rw [scalarProductRight_apply, scalarProductRight_apply]
  apply congrArg (fun t : K => (Nat.card (Spin n F N) : K)⁻¹ * t)
  exact Fintype.sum_bijective (fun g : Spin n F N => g⁻¹) inv_bijective
    (fun g => x g⁻¹ * y g) (fun g => y g⁻¹ * x g)
    (fun g => by simp [mul_comm])

def scalarProduct : (Spin n F N → K) →ₗ[K] (Spin n F N → K) →ₗ[K] K where
  toFun := scalarProductRight
  map_add' x y := by
    apply LinearMap.ext
    intro z
    change scalarProductRight (x + y) z = scalarProductRight x z + scalarProductRight y z
    rw [scalarProductRight_comm (x + y) z, map_add,
      scalarProductRight_comm z x, scalarProductRight_comm z y]
  map_smul' a x := by
    apply LinearMap.ext
    intro z
    change scalarProductRight (a • x) z = a • scalarProductRight x z
    rw [scalarProductRight_comm (a • x) z, map_smul, scalarProductRight_comm z x]

/-- The usual ordinary orthogonality clause on the literal character
carrier over a sufficient splitting field. This is not a PIM basis input. -/
structure OrdinaryOrthogonalitySource
    [ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card (Spin n F N))] : Prop where
  orthogonal : ∀ chi psi : Irr K (Spin n F N),
    scalarProductRight chi.val psi.val = if chi = psi then 1 else 0

variable [HasEnoughRootsOfUnity K (Nat.card (Spin n F N))]
  (orthogonality : OrdinaryOrthogonalitySource (N := N) (K := K))

include orthogonality in
theorem ordinary_linearIndependent :
    LinearIndependent K (fun chi : Irr K (Spin n F N) => chi.val) := by
  classical
  refine linearIndependent_iff'.mpr ?_
  intro s c h chi hchi
  have h' := congrArg (scalarProductRight chi.val) h
  simpa [map_sum, orthogonality.orthogonal, hchi, eq_comm] using h'

include orthogonality in
/-- Finiteness is deduced from orthogonality inside the finite-dimensional
space of all functions, rather than supplied as another source field. -/
theorem ordinary_finite : Finite (Irr K (Spin n F N)) :=
  (ordinary_linearIndependent orthogonality).finite_of_isNoetherian

section FiniteOrdinary

variable [Finite (Irr K (Spin n F N))]

/-- The explicit finite Fourier expansion with prescribed coefficients. -/
def ordinaryExpansion : (Irr K (Spin n F N) → K) →ₗ[K] (Spin n F N → K) where
  toFun c := ∑ chi, c chi • chi.val
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.smul_sum, smul_smul]

theorem ordinaryExpansion_apply (c : Irr K (Spin n F N) → K) :
    ordinaryExpansion c = ∑ chi, c chi • chi.val := rfl

def ordinaryCoordinates : (Spin n F N → K) →ₗ[K] (Irr K (Spin n F N) → K) where
  toFun x chi := scalarProductRight chi.val x
  map_add' x y := by ext chi; exact map_add _ x y
  map_smul' a x := by ext chi; exact map_smul _ a x

@[simp]
theorem ordinaryCoordinates_apply (x : Spin n F N → K) (chi : Irr K (Spin n F N)) :
    ordinaryCoordinates x chi = scalarProductRight chi.val x := rfl

include orthogonality in
theorem coordinates_expansion (c : Irr K (Spin n F N) → K) :
    ordinaryCoordinates (ordinaryExpansion c) = c := by
  classical
  ext chi
  simp [ordinaryExpansion, ordinaryCoordinates, map_sum,
    orthogonality.orthogonal, eq_comm]

def ordinarySpace : Submodule K (Spin n F N → K) := ordinaryExpansion.range

include orthogonality in
theorem expansion_coordinates {x : Spin n F N → K} (hx : x ∈ ordinarySpace) :
    ordinaryExpansion (ordinaryCoordinates x) = x := by
  obtain ⟨c, rfl⟩ := hx
  rw [coordinates_expansion orthogonality]

include orthogonality in
theorem coordinates_separate {x y : Spin n F N → K}
    (hx : x ∈ ordinarySpace) (hy : y ∈ ordinarySpace)
    (h : ordinaryCoordinates x = ordinaryCoordinates y) : x = y := by
  rw [← expansion_coordinates orthogonality hx,
    ← expansion_coordinates orthogonality hy, h]

/-- A specified all-functions extension of the principal Fourier operator.
The eventual predicate below is the specified ordinary block selector. -/
def fourierProjection (selected : Irr K (Spin n F N) → Prop) :
    (Spin n F N → K) →ₗ[K] (Spin n F N → K) := by
  classical
  let mask : (Spin n F N → K) →ₗ[K] (Irr K (Spin n F N) → K) :=
    { toFun := fun x chi => if selected chi then ordinaryCoordinates x chi else 0
      map_add' := by intro x y; ext chi; by_cases h : selected chi <;> simp [h]
      map_smul' := by intro a x; ext chi; by_cases h : selected chi <;> simp [h] }
  exact ordinaryExpansion.comp mask

theorem fourierProjection_apply (selected : Irr K (Spin n F N) → Prop)
    (x : Spin n F N → K) :
    fourierProjection selected x =
      ∑ chi, (if selected chi then scalarProductRight chi.val x else 0) • chi.val := rfl

include orthogonality in
theorem coordinates_fourier (selected : Irr K (Spin n F N) → Prop)
    (x : Spin n F N → K) :
    ordinaryCoordinates (fourierProjection selected x) =
      fun chi => if selected chi then ordinaryCoordinates x chi else 0 :=
  coordinates_expansion orthogonality _

include orthogonality in
theorem fourierProjection_idempotent (selected : Irr K (Spin n F N) → Prop) :
    (fourierProjection selected).comp (fourierProjection selected) =
      fourierProjection selected := by
  classical
  apply LinearMap.ext
  intro x
  apply congrArg ordinaryExpansion
  funext chi
  change (if selected chi then ordinaryCoordinates (fourierProjection selected x) chi else 0) =
    if selected chi then ordinaryCoordinates x chi else 0
  rw [coordinates_fourier orthogonality]
  by_cases hs : selected chi <;> simp [hs]

include orthogonality in
theorem fourierProjection_ordinary (selected : Irr K (Spin n F N) → Prop)
    (chi : Irr K (Spin n F N)) :
    fourierProjection selected chi.val = if selected chi then chi.val else 0 := by
  classical
  rw [fourierProjection_apply, Finset.sum_eq_single chi]
  · by_cases hs : selected chi <;> simp [orthogonality.orthogonal, hs]
  · intro psi hpsi hne
    simp [orthogonality.orthogonal, hne]
  · simp

theorem fourierProjection_selfAdjoint (selected : Irr K (Spin n F N) → Prop)
    (x y : Spin n F N → K) :
    scalarProductRight x (fourierProjection selected y) =
      scalarProductRight (fourierProjection selected x) y := by
  classical
  rw [scalarProductRight_comm (fourierProjection selected x) y]
  simp only [fourierProjection_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro chi hchi
  by_cases hs : selected chi
  · simp [hs, scalarProductRight_comm, smul_eq_mul, mul_comm]
  · simp [hs]

theorem scalarProductRight_twist (alpha : MulAut (Spin n F N))
    (x y : Spin n F N → K) :
    scalarProductRight (fun g => x (alpha g)) (fun g => y (alpha g)) =
      scalarProductRight x y := by
  simp only [scalarProductRight_apply, map_inv]
  congr 1
  exact alpha.toEquiv.sum_comp (fun g => x g⁻¹ * y g)

def ordinaryTwistEquiv (alpha : MulAut (Spin n F N)) :
    Irr K (Spin n F N) ≃ Irr K (Spin n F N) where
  toFun chi := OrdinaryIrreducibleCharacter.twist K _ chi alpha
  invFun chi := OrdinaryIrreducibleCharacter.twist K _ chi alpha.symm
  left_inv chi := by ext g; simp
  right_inv chi := by ext g; simp

theorem ordinaryExpansion_natural (alpha : MulAut (Spin n F N))
    (c d : Irr K (Spin n F N) → K)
    (natural : ∀ chi, d (OrdinaryIrreducibleCharacter.twist K _ chi alpha) = c chi) :
    ordinaryExpansion d =
      TypeBPrincipalSelectorCorollary413SourceInstantiation.functionTwistLinearEquiv
        alpha (ordinaryExpansion c) := by
  ext g
  simp only [ordinaryExpansion, LinearMap.coe_mk, AddHom.coe_mk,
    TypeBPrincipalSelectorCorollary413SourceInstantiation.functionTwistLinearEquiv_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  symm
  exact Fintype.sum_equiv (ordinaryTwistEquiv alpha)
    (fun chi => c chi * chi (alpha g)) (fun chi => d chi * chi g)
    (fun chi => by rw [show d (ordinaryTwistEquiv alpha chi) = c chi from natural chi]; rfl)

theorem fourierProjection_natural (selected : Irr K (Spin n F N) → Prop)
    (alpha : MulAut (Spin n F N))
    (selected_natural : ∀ chi,
      selected (OrdinaryIrreducibleCharacter.twist K _ chi alpha) ↔ selected chi)
    (x : Spin n F N → K) :
    fourierProjection selected
        (TypeBPrincipalSelectorCorollary413SourceInstantiation.functionTwistLinearEquiv alpha x) =
      TypeBPrincipalSelectorCorollary413SourceInstantiation.functionTwistLinearEquiv
        alpha (fourierProjection selected x) := by
  apply ordinaryExpansion_natural
  intro chi
  change (if selected (OrdinaryIrreducibleCharacter.twist K _ chi alpha) then
      scalarProductRight (OrdinaryIrreducibleCharacter.twist K _ chi alpha).val
        (TypeBPrincipalSelectorCorollary413SourceInstantiation.functionTwistLinearEquiv alpha x)
      else 0) = if selected chi then scalarProductRight chi.val x else 0
  simp only [selected_natural chi]
  by_cases hs : selected chi
  · simp only [if_pos hs]
    exact scalarProductRight_twist alpha chi.val x
  · simp only [if_neg hs]

section Physical

open TypeBSpinPrincipalDecompositionBinding TypeBCentralKernelBlockSource
open TypeBPrincipalSelectorCorollary413SourceInstantiation
open scoped MonoidAlgebra

variable {O k : Type} [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k]
  (Msys : ModularSystem 2 K O k)
  (iota : PrimeRegularRootEmbedding 2 k K (Spin n F N))

/-- Navarro's PIM formula with the companion file's actual nonnegative
stable-reduction multiplicities. No coefficient function is supplied. -/
def projectiveIndecomposable (phi : IBr iota) : Spin n F N → K :=
  ordinaryExpansion (fun chi => (decompositionNumber Msys iota chi phi : K))

theorem projectiveIndecomposable_apply (phi : IBr iota) (g : Spin n F N) :
    projectiveIndecomposable Msys iota phi g =
      ∑ chi : Irr K (Spin n F N), (decompositionNumber Msys iota chi phi : K) * chi g := by
  simp [projectiveIndecomposable, ordinaryExpansion]

/-- The specified block projective space. In the principal application `b`
is the same primitive principal idempotent used by `Supported iota b`. -/
def physicalProjectiveSpace (b : LiteralPrimitiveBlock k (Spin n F N)) :
    Submodule K (Spin n F N → K) :=
  Submodule.span K (Set.range (fun phi : {phi : IBr iota // Supported iota b phi} =>
    projectiveIndecomposable Msys iota phi.val))

theorem projectiveIndecomposable_mem (b : LiteralPrimitiveBlock k (Spin n F N))
    (phi : {phi : IBr iota // Supported iota b phi}) :
    projectiveIndecomposable Msys iota phi.val ∈ physicalProjectiveSpace Msys iota b :=
  Submodule.subset_span ⟨phi, rfl⟩

theorem physicalProjectiveSpace_le_ordinarySpace
    (b : LiteralPrimitiveBlock k (Spin n F N)) :
    physicalProjectiveSpace Msys iota b ≤ ordinarySpace := by
  apply Submodule.span_le.mpr
  rintro x ⟨phi, rfl⟩
  exact ⟨fun chi => (decompositionNumber Msys iota chi phi.val : K), rfl⟩

include orthogonality in
theorem projectiveIndecomposable_coordinates (phi : IBr iota) :
    ordinaryCoordinates (projectiveIndecomposable Msys iota phi) =
      fun chi => (decompositionNumber Msys iota chi phi : K) :=
  coordinates_expansion orthogonality _

include orthogonality in
theorem projectiveIndecomposable_linearIndependent
    (columns : DecompositionColumnIndependenceSource Msys iota)
    (b : LiteralPrimitiveBlock k (Spin n F N)) :
    LinearIndependent K
      (fun phi : {phi : IBr iota // Supported iota b phi} =>
        projectiveIndecomposable Msys iota phi.val) := by
  apply LinearIndependent.of_comp ordinaryCoordinates
  simpa only [Function.comp_def, projectiveIndecomposable_coordinates orthogonality] using
    columns.independent.comp
      (fun phi : {phi : IBr iota // Supported iota b phi} => phi.val) Subtype.val_injective

include orthogonality in
/-- The specified PIM-span dimension follows from the actual decomposition
columns; there is no source-supplied projective basis or dimension. -/
theorem physicalProjectiveSpace_finrank
    (columns : DecompositionColumnIndependenceSource Msys iota)
    (b : LiteralPrimitiveBlock k (Spin n F N)) :
    Module.finrank K (physicalProjectiveSpace Msys iota b) =
      Nat.card {phi : IBr iota // Supported iota b phi} := by
  rw [Nat.card_eq_fintype_card]
  exact finrank_span_eq_card
    (projectiveIndecomposable_linearIndependent orthogonality Msys iota columns b)

variable (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)

include hcompat in
theorem projectiveIndecomposable_twist (alpha : MulAut (Spin n F N)) (phi : IBr iota) :
    projectiveIndecomposable Msys iota (IrreducibleBrauerCharacter.twist iota phi alpha) =
      functionTwistLinearEquiv alpha (projectiveIndecomposable Msys iota phi) := by
  apply ordinaryExpansion_natural
  intro chi
  exact congrArg (fun a : ℕ => (a : K))
    (decompositionNumber_twist Msys iota hcompat alpha chi phi)

variable {E : Type} [Group E] (field : E →* (MulAut (Spin n F N))ᵐᵒᵖ)
  (b : LiteralPrimitiveBlock k (Spin n F N))
  (brauerStable : ∀ e : E, ∀ phi : IBr iota, Supported iota b phi →
    Supported iota b (IrreducibleBrauerCharacter.twist iota phi (field e).unop))

include hcompat brauerStable in
theorem projectiveStable : ∀ e : E, ∀ x : Spin n F N → K,
    x ∈ physicalProjectiveSpace Msys iota b →
      functionTwistLinearEquiv (field e).unop x ∈ physicalProjectiveSpace Msys iota b := by
  intro e x hx
  have stable : physicalProjectiveSpace Msys iota b ≤
      (physicalProjectiveSpace Msys iota b).comap
        (functionTwistLinearEquiv (field e).unop).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro y ⟨phi, rfl⟩
    change functionTwistLinearEquiv (field e).unop
      (projectiveIndecomposable Msys iota phi.val) ∈ physicalProjectiveSpace Msys iota b
    rw [← projectiveIndecomposable_twist Msys iota hcompat]
    exact projectiveIndecomposable_mem Msys iota b
      ⟨IrreducibleBrauerCharacter.twist iota phi.val (field e).unop,
        brauerStable e phi.val phi.property⟩
  exact stable hx

/-- The existing projective--Brauer adapter, now filled entirely by the
literal PIM/span/scalar-product formulas and the actual coefficient matrix.
The only column input is global Navarro rank for that very matrix. -/
def projectiveBrauerFormulaSource
    (columns : DecompositionColumnIndependenceSource Msys iota) :
    ProjectiveBrauerFormulaSource field iota (Supported iota b) brauerStable
      (physicalProjectiveSpace Msys iota b)
      (projectiveStable Msys iota hcompat field b brauerStable) where
  projectiveIndecomposable phi :=
    ⟨projectiveIndecomposable Msys iota phi.val,
      projectiveIndecomposable_mem Msys iota b phi⟩
  coefficient P chi := scalarProductRight chi.val P.val
  decompositionNumber chi phi := (decompositionNumber Msys iota chi phi.val : K)
  coefficient_projectiveIndecomposable phi chi :=
    congrFun (projectiveIndecomposable_coordinates orthogonality Msys iota phi.val) chi
  coefficient_separates P Q h := by
    apply Subtype.ext
    apply coordinates_separate orthogonality
      (physicalProjectiveSpace_le_ordinarySpace Msys iota b P.property)
      (physicalProjectiveSpace_le_ordinarySpace Msys iota b Q.property)
    exact funext h
  decompositionColumns_linearIndependent :=
    columns.independent.comp
      (fun phi : {phi : IBr iota // Supported iota b phi} => phi.val) Subtype.val_injective
  coefficient_natural := by
    dsimp only
    intro e P chi
    exact scalarProductRight_twist (field e).unop chi.val P.val
  decompositionNumber_natural := by
    dsimp only
    intro e chi phi
    exact congrArg (fun a : ℕ => (a : K))
      (decompositionNumber_twist Msys iota hcompat (field e).unop chi phi.val)

variable [Fintype (LiteralPrimitiveBlock k (Spin n F N))]
  (blocks : BlockIdempotentDecomposition
    (fun c : LiteralPrimitiveBlock k (Spin n F N) => c.val))
  (source : OrdinaryBlockSource Msys iota blocks)

/-- The specified Fourier projection uses the SAME source selector whose
support was bound to the actual stable-reduction coefficients. -/
def principalProjection : (Spin n F N → K) →ₗ[K] (Spin n F N → K) :=
  fourierProjection (fun chi => source.ordinaryBlock chi = b)

theorem principalProjection_apply (x : Spin n F N → K) :
    principalProjection Msys iota b blocks source x =
      ∑ chi : Irr K (Spin n F N),
        (if source.ordinaryBlock chi = b then scalarProductRight chi.val x else 0) • chi.val := by
  rw [principalProjection, fourierProjection_apply]
  apply Finset.sum_congr rfl
  intro chi hchi
  by_cases hs : source.ordinaryBlock chi = b
  · simp only [if_pos hs]
  · simp only [if_neg hs]

include orthogonality in
theorem principalProjection_idempotent :
    (principalProjection Msys iota b blocks source).comp
        (principalProjection Msys iota b blocks source) =
      principalProjection Msys iota b blocks source :=
  fourierProjection_idempotent orthogonality _

theorem principalProjection_selfAdjoint (x y : Spin n F N → K) :
    scalarProductRight x (principalProjection Msys iota b blocks source y) =
      scalarProductRight (principalProjection Msys iota b blocks source x) y :=
  fourierProjection_selfAdjoint _ x y

include orthogonality in
theorem principalProjection_selected (chi : Irr K (Spin n F N))
    (selected : source.ordinaryBlock chi = b) :
    principalProjection Msys iota b blocks source chi.val = chi.val := by
  unfold principalProjection
  simpa only [if_pos selected] using
    fourierProjection_ordinary orthogonality (fun psi => source.ordinaryBlock psi = b) chi

include orthogonality in
theorem principalProjection_projectiveIndecomposable
    (phi : {phi : IBr iota // Supported iota b phi}) :
    principalProjection Msys iota b blocks source
        (projectiveIndecomposable Msys iota phi.val) =
      projectiveIndecomposable Msys iota phi.val := by
  apply congrArg ordinaryExpansion
  funext chi
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [projectiveIndecomposable_coordinates orthogonality]
  by_cases hs : source.ordinaryBlock chi = b
  · simp [hs]
  · have hd : decompositionNumber Msys iota chi phi.val = 0 := by
      by_contra hn
      exact hs ((ordinaryBlock_eq_iff Msys iota blocks source chi b).mpr
        ⟨phi.val, hn, phi.property⟩)
    simp [hs, hd]

include hcompat brauerStable in
theorem principalSelector_natural (e : E) (chi : Irr K (Spin n F N)) :
    source.ordinaryBlock (OrdinaryIrreducibleCharacter.twist K _ chi (field e).unop) = b ↔
      source.ordinaryBlock chi = b := by
  letI := ordinaryIrrFieldAction (K := K) field
  have forward : ∀ e : E, ∀ chi : Irr K (Spin n F N),
      source.ordinaryBlock chi = b → source.ordinaryBlock (e • chi) = b := by
    intro d psi hp
    obtain ⟨phi, hd, hb⟩ := (ordinaryBlock_eq_iff Msys iota blocks source psi b).mp hp
    apply (ordinaryBlock_eq_iff Msys iota blocks source _ b).mpr
    refine ⟨IrreducibleBrauerCharacter.twist iota phi (field d).unop, ?_,
      brauerStable d phi hb⟩
    change decompositionNumber Msys iota
      (OrdinaryIrreducibleCharacter.twist K _ psi (field d).unop)
      (IrreducibleBrauerCharacter.twist iota phi (field d).unop) ≠ 0
    simpa only [decompositionNumber_twist Msys iota hcompat] using hd
  change source.ordinaryBlock (e • chi) = b ↔ source.ordinaryBlock chi = b
  constructor
  · intro h
    simpa only [inv_smul_smul] using forward e⁻¹ (e • chi) h
  · exact forward e chi

include hcompat brauerStable in
theorem principalProjection_natural (e : E) (x : Spin n F N → K) :
    principalProjection Msys iota b blocks source (functionTwistLinearEquiv (field e).unop x) =
      functionTwistLinearEquiv (field e).unop (principalProjection Msys iota b blocks source x) :=
  fourierProjection_natural _ _
    (principalSelector_natural Msys iota hcompat field b brauerStable blocks source e) x

end Physical

end FiniteOrdinary

end ModularRep.PaperProofs.TypeBSpinPrincipalProjectiveBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
