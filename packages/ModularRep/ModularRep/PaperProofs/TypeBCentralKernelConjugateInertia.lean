import ModularRep.PaperProofs.TypeBCentralKernelTripleCarriers
import ModularRep.PaperProofs.TypeBCentralKernelButterflyAmbientIsomorphism

/-!
# Actual inertias under simultaneous ambient conjugation

These are the group and raw-representative joins needed when a published
pair theorem selects a conjugate character. Every map is the restriction
of the same ambient conjugation. The weight is its actual right twist,
with the inverse required by the existing opposite-automorphism action.
No triple, source certificate or character-to-weight correspondence is
assumed here.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBCentralKernelConjugateInertia

open ModularRep TypeBCentralKernelCarriers TypeBCentralKernelInertia
open TypeBCentralKernelTripleCarriers TypeBCentralKernelTripleCertificate

universe u

variable {p : ℕ} {k K A : Type u}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
  [Group A] [Finite A] (G : Subgroup A) [G.Normal]

def conjugateWeight (a : A) (W : CharacterWeight p K G) : CharacterWeight p K G :=
  W.rightTwist (originalAction G a⁻¹)

@[simp] theorem isoOf_conjugateWeight (a : A) (W : CharacterWeight p K G) :
    isoOf (conjugateWeight G a W) = conjugationOp G a • isoOf W := rfl

@[simp] theorem classOf_conjugateWeight (a : A) (W : CharacterWeight p K G) :
    classOf (conjugateWeight G a W) = conjugationOp G a • classOf W := rfl

theorem characterInertia_conjugate
    (root : PrimeRegularRootEmbedding p k K G) (theta : IBr root) (a : A) :
    T G root (conjugationOp G a • theta) =
      (T G root theta).map (MulAut.conj a).toMonoidHom := by
  ext b
  obtain ⟨t, rfl⟩ := (MulAut.conj a).surjective b
  rw [Subgroup.mem_map_equiv]
  simp only [MulEquiv.symm_apply_apply]
  change (conjugationOp G (a * t * a⁻¹) •
      (conjugationOp G a • theta) = conjugationOp G a • theta) ↔
    conjugationOp G t • theta = theta
  simp only [map_mul, map_inv, mul_smul, inv_smul_smul, smul_left_cancel_iff]

theorem rawInertia_conjugate (W : CharacterWeight p K G) (a : A) :
    U G (conjugateWeight G a W) =
      (U G W).map (MulAut.conj a).toMonoidHom := by
  ext b
  obtain ⟨t, rfl⟩ := (MulAut.conj a).surjective b
  rw [Subgroup.mem_map_equiv]
  simp only [MulEquiv.symm_apply_apply]
  change (conjugationOp G (a * t * a⁻¹) •
      (conjugationOp G a • isoOf W) = conjugationOp G a • isoOf W) ↔
    conjugationOp G t • isoOf W = isoOf W
  simp only [map_mul, map_inv, mul_smul, inv_smul_smul, smul_left_cancel_iff]

def characterInertiaEquiv
    (root : PrimeRegularRootEmbedding p k K G) (theta : IBr root) (a : A) :
    T G root theta ≃* T G root (conjugationOp G a • theta) :=
  ((T G root theta).equivMapOfInjective (MulAut.conj a).toMonoidHom
    (MulAut.conj a).injective).trans
      (MulEquiv.subgroupCongr (characterInertia_conjugate G root theta a).symm)

@[simp] theorem characterInertiaEquiv_value
    (root : PrimeRegularRootEmbedding p k K G) (theta : IBr root) (a : A)
    (t : T G root theta) :
    (characterInertiaEquiv G root theta a t : A) = a * (t : A) * a⁻¹ := rfl

theorem characterInertiaEquiv_symm_value
    (root : PrimeRegularRootEmbedding p k K G) (theta : IBr root) (a : A)
    (t : T G root (conjugationOp G a • theta)) :
    ((characterInertiaEquiv G root theta a).symm t : A) =
      (MulAut.conj a).symm (t : A) := by
  apply (MulAut.conj a).injective
  have h := congrArg Subtype.val ((characterInertiaEquiv G root theta a).apply_symm_apply t)
  exact h.trans ((MulAut.conj a).apply_symm_apply t.val).symm

def rawInertiaEquiv (W : CharacterWeight p K G) (a : A) :
    U G W ≃* U G (conjugateWeight G a W) :=
  ((U G W).equivMapOfInjective (MulAut.conj a).toMonoidHom
    (MulAut.conj a).injective).trans
      (MulEquiv.subgroupCongr (rawInertia_conjugate G W a).symm)

@[simp] theorem rawInertiaEquiv_value (W : CharacterWeight p K G) (a : A)
    (t : U G W) :
    (rawInertiaEquiv G W a t : A) = a * (t : A) * a⁻¹ := rfl

def baseEquiv (root : PrimeRegularRootEmbedding p k K G)
    (theta : IBr root) (a : A) :
    inside G (T G root theta) ≃*
      inside G (T G root (conjugationOp G a • theta)) :=
  (((insideEquiv G (T G root theta) (G_le_T G root theta)).symm).trans
    (originalAction G a)).trans
      (insideEquiv G (T G root (conjugationOp G a • theta))
        (G_le_T G root (conjugationOp G a • theta)))

@[simp] theorem baseEquiv_value
    (root : PrimeRegularRootEmbedding p k K G) (theta : IBr root) (a : A)
    (x : inside G (T G root theta)) :
    (baseEquiv G root theta a x).val.val = a * x.val.val * a⁻¹ := rfl

theorem base_anchor
    (root : PrimeRegularRootEmbedding p k K G) (theta : IBr root) (a : A)
    (x : inside G (T G root theta)) :
    characterInertiaEquiv G root theta a x.val = (baseEquiv G root theta a x).val := by
  apply Subtype.ext
  rfl

theorem conjugate_raw_le_character
    (root : PrimeRegularRootEmbedding p k K G) (theta : IBr root)
    (W : CharacterWeight p K G) (a : A) (included : U G W ≤ T G root theta) :
    U G (conjugateWeight G a W) ≤ T G root (conjugationOp G a • theta) := by
  rw [rawInertia_conjugate, characterInertia_conjugate]
  exact Subgroup.map_mono included

/-- The local ambient in the conjugate triple is the actual image of the
original raw inertia inside the actual character inertia. -/
theorem localAmbient_image
    (root : PrimeRegularRootEmbedding p k K G) (theta : IBr root)
    (W : CharacterWeight p K G) (a : A) :
    (inside (U G W) (T G root theta)).map
        (characterInertiaEquiv G root theta a).toMonoidHom =
      inside (U G (conjugateWeight G a W))
        (T G root (conjugationOp G a • theta)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change a * x.val * a⁻¹ ∈ U G (conjugateWeight G a W)
    rw [rawInertia_conjugate]
    exact ⟨x.val, hx, rfl⟩
  · intro hy
    let x := (characterInertiaEquiv G root theta a).symm y
    refine ⟨x, ?_, (characterInertiaEquiv G root theta a).apply_symm_apply y⟩
    change y.val ∈ U G (conjugateWeight G a W) at hy
    rw [rawInertia_conjugate, Subgroup.mem_map_equiv] at hy
    change ((characterInertiaEquiv G root theta a).symm y : A) ∈ U G W
    rw [characterInertiaEquiv_symm_value]
    exact hy

/-- A witness's existing centralizer condition identifies the constructed
Butterfly local group with the specified conjugate raw inertia. -/
theorem butterflyLocal_eq
    (root : PrimeRegularRootEmbedding p k K G) (theta : IBr root)
    (W : CharacterWeight p K G) (a : A)
    (centralizer_le :
      Subgroup.centralizer (inside G (T G root theta) : Set (T G root theta)) ≤
        inside (U G W) (T G root theta)) :
    TypeBCentralKernelButterflyCertificate.secondLocalAmbient
        (inside G (T G root theta))
        (inside G (T G root (conjugationOp G a • theta)))
        (baseEquiv G root theta a) (inside (U G W) (T G root theta)) =
      inside (U G (conjugateWeight G a W))
        (T G root (conjugationOp G a • theta)) :=
  (TypeBCentralKernelButterflyAmbientIsomorphism.secondLocalAmbient_eq_map
    (inside G (T G root theta))
    (inside G (T G root (conjugationOp G a • theta)))
    (characterInertiaEquiv G root theta a) (baseEquiv G root theta a)
    (base_anchor G root theta a) (inside (U G W) (T G root theta))
    centralizer_le).trans (localAmbient_image G root theta W a)

/-- Equality of actual weight classes supplies an actual inner conjugating
element. Raw equality uses the checked character-weight isomorphism lemma. -/
theorem exists_inner_conjugate_of_class_eq
    (W V : CharacterWeight p K G) (same : classOf W = classOf V) :
    ∃ g : G, conjugateWeight G (g : A) W = V := by
  obtain ⟨g, hg⟩ := Quotient.exact same.symm
  change g • isoOf W = isoOf V at hg
  rw [← iso_action_inner G g] at hg
  exact ⟨g, CharacterWeight.eq_of_isomorphic (Quotient.exact hg)⟩

theorem inner_fixes_character
    (root : PrimeRegularRootEmbedding p k K G) (theta : IBr root) (g : G) :
    conjugationOp G (g : A) • theta = theta := G_le_T G root theta g.property

end ModularRep.PaperProofs.TypeBCentralKernelConjugateInertia


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
