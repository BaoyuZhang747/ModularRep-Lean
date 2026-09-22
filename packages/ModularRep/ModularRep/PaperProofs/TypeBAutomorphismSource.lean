import ModularRep.PaperProofs.TypeBWeightStabilizerSource
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Tactic.Group

/-!
# The natural automorphism map in Type B criterion clause (1)

The ambient group and its pointwise Spin automorphism are exactly those
already used by `TypeBWeightStabilizerSource`. This file proves that the
pointwise construction is a group homomorphism, and that its kernel is
the centralizer of the actual embedded Spin subgroup. The centre of the
special Clifford group is embedded by the semidirect left inclusion.

The E1 structural source retains Spin perfectness, the centre-kernel,
surjectivity and cyclic quotient assertions on these literal maps. The
finite derived-subgroup equality follows from perfectness and the norm
to the commutative scalar group; no passage from an algebraic derived
subgroup equality to its finite points is assumed. The
quotient isomorphism with `MulAut Spin` is induced by the constructed map;
no independent automorphism carrier or unrelated isomorphism is supplied.
There is no character, weight, block-goodness or iBAW target in this input.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBAutomorphismSource

open ModularRep TypeBCliffordCarriers TypeBWeightStabilizerSource

variable {n p f : ℕ} {F : Type}
variable [Field F] [Finite F] [CharP F p]
variable {N : NormSource n F}
variable {parameters : OddFieldParameters F p f}
variable (S : FieldActionSource n F p f parameters N)

/-- The natural homomorphism uses the already defined pointwise ambient
Spin automorphism, with its actual conjugation and Frobenius factors. -/
def ambientAutomorphism : Ambient S →* MulAut (Spin n F N) where
  toFun := ambientSpinAutomorphism S
  map_one' := by
    simp [ambientSpinAutomorphism]
  map_mul' a b := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change (a.left * S.action a.right b.left) *
        S.action (a.right * b.right) x.1 * (a.left * S.action a.right b.left)⁻¹ =
      a.left * S.action a.right (b.left * S.action b.right x.1 * b.left⁻¹) * a.left⁻¹
    simp only [map_mul, MulAut.mul_apply, map_inv, mul_inv_rev]
    group

@[simp]
theorem ambientAutomorphism_apply (a : Ambient S) :
    ambientAutomorphism S a = ambientSpinAutomorphism S a := rfl

@[simp]
theorem ambientAutomorphism_coe (a : Ambient S) (x : Spin n F N) :
    (ambientAutomorphism S a x).1 =
      a.left * S.action a.right x.1 * a.left⁻¹ := rfl

@[simp]
theorem ambientAutomorphism_inl (m : SpecialClifford n F) :
    ambientAutomorphism S (SemidirectProduct.inl m) =
      MulAut.conjNormal (H := SpinSubgroup n F N) m :=
  by simp [ambientAutomorphism, ambientSpinAutomorphism]

@[simp]
theorem ambientAutomorphism_inr (e : FieldGroup f) :
    ambientAutomorphism S (SemidirectProduct.inr e) =
      spinFieldAction n F S e :=
  by simp [ambientAutomorphism, ambientSpinAutomorphism]

/-- Literal conjugation of a special Clifford element inside the already
fixed semidirect product. -/
theorem conjugate_inl (a : Ambient S) (m : SpecialClifford n F) :
    a * SemidirectProduct.inl m * a⁻¹ =
      SemidirectProduct.inl (a.left * S.action a.right m * a.left⁻¹) := by
  apply SemidirectProduct.ext
  · simp [mul_assoc]
  · simp

/-- The actual Spin inclusion is injective. -/
theorem spinEmbedding_injective : Function.Injective (spinEmbedding S) := by
  intro x y h
  apply Subtype.ext
  exact congrArg SemidirectProduct.left h

/-- The constructed homomorphism is the restriction of ambient
conjugation through the actual Spin inclusion. -/
theorem spinEmbedding_natural (a : Ambient S) (x : Spin n F N) :
    spinEmbedding S (ambientAutomorphism S a x) =
      a * spinEmbedding S x * a⁻¹ := by
  change SemidirectProduct.inl (a.left * S.action a.right x.1 * a.left⁻¹) =
    a * SemidirectProduct.inl x.1 * a⁻¹
  exact (conjugate_inl S a x.1).symm

/-- The Spin subgroup in the criterion's actual ambient group. -/
def embeddedSpin : Subgroup (Ambient S) := (spinEmbedding S).range

/-- The centre `Z(M)` in the criterion means its actual image under
`M -> M semidirect E`, rather than the centre of the entire semidirect
product, which need not coincide with it. -/
def embeddedCenter : Subgroup (Ambient S) :=
  (Subgroup.center (SpecialClifford n F)).map SemidirectProduct.inl

@[simp]
theorem mem_embeddedCenter (a : Ambient S) :
    a ∈ embeddedCenter S ↔
      ∃ z : SpecialClifford n F,
        z ∈ Subgroup.center (SpecialClifford n F) ∧ SemidirectProduct.inl z = a :=
  Iff.rfl

/-- Field automorphisms preserve the literal special Clifford centre. -/
theorem field_preserves_center (e : FieldGroup f) (z : SpecialClifford n F)
    (hz : z ∈ Subgroup.center (SpecialClifford n F)) :
    S.action e z ∈ Subgroup.center (SpecialClifford n F) := by
  rw [Subgroup.mem_center_iff]
  intro m
  obtain ⟨m, rfl⟩ := (S.action e).surjective m
  simpa only [map_mul] using congrArg (S.action e) (Subgroup.mem_center_iff.mp hz m)

/-- The embedded centre is normal by field preservation and actual
semidirect conjugation; no centre-kernel source statement is needed. -/
instance embeddedCenter_normal : (embeddedCenter S).Normal where
  conj_mem _ hz a := by
    obtain ⟨z, hz, rfl⟩ := hz
    rw [conjugate_inl]
    have hf := field_preserves_center S a.right z hz
    refine ⟨S.action a.right z, hf, ?_⟩
    apply congrArg SemidirectProduct.inl
    symm
    rw [Subgroup.mem_center_iff.mp hf a.left]
    simp [mul_assoc]

/-- Triviality of the actual automorphism is equivalent to commuting with
every embedded Spin element. -/
theorem mem_kernel_iff (a : Ambient S) :
    a ∈ (ambientAutomorphism S).ker ↔
      ∀ x : Spin n F N, a * spinEmbedding S x = spinEmbedding S x * a := by
  change ambientAutomorphism S a = 1 ↔ _
  constructor
  · intro ha x
    have h := spinEmbedding_natural S a x
    have hx : ambientAutomorphism S a x = x := by
      rw [ha]
      rfl
    rw [hx] at h
    have heq := congrArg (fun y : Ambient S => y * a) h
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using heq.symm
  · intro h
    apply MulEquiv.ext
    intro x
    apply spinEmbedding_injective S
    change spinEmbedding S (ambientAutomorphism S a x) = spinEmbedding S x
    rw [spinEmbedding_natural, h x]
    simp [mul_assoc]

/-- The natural map's kernel is exactly the literal centralizer of Spin.
This is a kernel deduction before any classification source is applied. -/
theorem kernel_eq_centralizer :
    (ambientAutomorphism S).ker =
      Subgroup.centralizer (embeddedSpin S : Set (Ambient S)) := by
  ext a
  rw [mem_kernel_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h x hx
    obtain ⟨y, rfl⟩ := hx
    exact (h y).symm
  · intro h x
    exact (h (spinEmbedding S x) ⟨x, rfl⟩).symm

/-- The inner automorphisms are literally the range of conjugation by
the same Spin carrier. -/
def innerAutomorphisms (N : NormSource n F) : Subgroup (MulAut (Spin n F N)) :=
  (MulAut.conj : Spin n F N →* MulAut (Spin n F N)).range

/-- Conjugating an inner automorphism by an actual automorphism gives
conjugation by the actual image of its defining Spin element. -/
instance innerAutomorphisms_normal (N : NormSource n F) :
    (innerAutomorphisms N).Normal where
  conj_mem _ ha β := by
    obtain ⟨g, rfl⟩ := ha
    refine ⟨β g, ?_⟩
    apply MulEquiv.ext
    intro x
    change β g * x * (β g)⁻¹ = β (g * β⁻¹ x * g⁻¹)
    simp only [map_mul, map_inv, MulAut.apply_inv_self]

/-- The outer automorphism carrier in the criterion is the literal
automorphism group modulo the actual inner automorphisms. -/
abbrev OuterAutomorphism (N : NormSource n F) :=
  MulAut (Spin n F N) ⧸ innerAutomorphisms N

/-- The actual field group is cyclic by its fixed `ZMod f` carrier. -/
theorem fieldGroup_cyclic (f : ℕ) : IsCyclic (FieldGroup f) := inferInstance

/-- The literal norm has commutative target, so every special Clifford
commutator belongs to the actual norm-one subgroup. -/
theorem commutator_le_spin (N : NormSource n F) :
    commutator (SpecialClifford n F) ≤ SpinSubgroup n F N := by
  rw [commutator_def]
  apply Subgroup.commutator_le.mpr
  intro g _ h _
  change N.norm (g * h * g⁻¹ * h⁻¹) = 1
  simp [map_mul, map_inv, mul_comm, mul_left_comm, mul_assoc]

/-- Perfectness of the same finite Spin carrier supplies the reverse
inclusion through the literal subgroup embedding. -/
theorem spin_le_commutator (N : NormSource n F)
    (hperfect : commutator (Spin n F N) = ⊤) :
    SpinSubgroup n F N ≤ commutator (SpecialClifford n F) := by
  have h : ⁅SpinSubgroup n F N, SpinSubgroup n F N⁆ = SpinSubgroup n F N := by
    rw [← Subgroup.map_subtype_commutator, hperfect,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← h]
  exact Subgroup.commutator_mono le_top le_top

/-- This finite derived-group statement is a deduction from norm and
Spin perfectness. In the generic cover lane `hperfect` is precisely
`GenericSpinCoverSource.perfect` on this same norm kernel. -/
theorem derived_eq_spin (N : NormSource n F)
    (hperfect : commutator (Spin n F N) = ⊤) :
    commutator (SpecialClifford n F) = SpinSubgroup n F N :=
  le_antisymm (commutator_le_spin N) (spin_le_commutator N hperfect)

/-- Exact E1/U structural inputs for FLZ Theorem 2.1(1). The rank and
odd-field scope are fixed. FLZ Section 3.1, p. 541, gives the algebraic
regular embedding; the finite derived equality is separately proved
above using finite Spin perfectness, which is the existing covering
source's exact perfectness clause. FLZ Section 3.5, p. 546, together with
GLS Number 3, Theorem 2.5.12, pp. 58--59, gives the natural automorphism
description. The cyclic `M/Spin` quotient is the norm quotient of order
`q-1`, not the effective diagonal quotient of order two. These are source
statements about the displayed homomorphism and literal subgroups, not
the full criterion or its character-theoretic target. The outer-group
commutativity assertion is on `Aut(Spin)/Inn(Spin)` itself, with the same
FLZ Section 3.5/GLS automorphism source. -/
structure StructuralSource : Prop where
  rank : 3 ≤ n
  spin_perfect : commutator (Spin n F N) = ⊤
  kernel : (ambientAutomorphism S).ker = embeddedCenter S
  surjective : Function.Surjective (ambientAutomorphism S)
  quotient_cyclic : IsCyclic (SpecialClifford n F ⧸ SpinSubgroup n F N)
  outer_abelian : IsMulCommutative (OuterAutomorphism N)

/-- The actual centralizer statement is deduced from the natural-map
kernel, rather than supplied as an unrelated second structural assertion. -/
theorem centralizer_eq_embeddedCenter (source : StructuralSource S) :
    Subgroup.centralizer (embeddedSpin S : Set (Ambient S)) = embeddedCenter S :=
  (kernel_eq_centralizer S).symm.trans source.kernel

/-- The automorphism-group equivalence is induced by the constructed
natural map, with the quotient literally taken by the embedded `Z(M)`. -/
def quotientEquivAut (source : StructuralSource S) :
    Ambient S ⧸ embeddedCenter S ≃* MulAut (Spin n F N) :=
  (QuotientGroup.quotientMulEquivOfEq source.kernel.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (ambientAutomorphism S) source.surjective)

/-- The quotient equivalence has the prescribed natural value on every
actual ambient element, so its relation to conjugation is explicit. -/
@[simp]
theorem quotientEquivAut_mk (source : StructuralSource S) (a : Ambient S) :
    quotientEquivAut S source (QuotientGroup.mk' (embeddedCenter S) a) =
      ambientAutomorphism S a := rfl

end ModularRep.PaperProofs.TypeBAutomorphismSource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
