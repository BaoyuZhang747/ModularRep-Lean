import ModularRep.PaperProofs.TypeBCliffordOrthogonalSourceBinding
import ModularRep.PaperProofs.TypeBCliffordOrthogonalFieldAction

/-!
# Scalars, the actual SO quotient and its full field action

The scalar subgroup is the range of the literal field-unit embedding.
Its equality with the constructed SO projection kernel yields the first
isomorphism theorem on those exact carriers. Every prescribed field-group
element preserves scalars by the checked scalar naturality formula, so its
action descends and is transported through this same quotient equivalence.

The semidirect map is the actual SO projection on the Clifford coordinate
and the identity on the field coordinate. Its kernel is exactly the
embedded scalar subgroup. No new source or automorphism-image claim occurs.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBCliffordOrthogonalAmbientQuotient

open TypeBCliffordCarriers TypeBCliffordScalarNorm
open TypeBCliffordOrthogonalSourceBinding

section Scalars

variable (n : ℕ) (F : Type) [Field F]

/-- Scalars mean the actual algebra-map units, not a renamed centre. -/
def scalarSubgroup : Subgroup (SpecialClifford n F) := (scalar n F).range

theorem scalarSubgroup_le_center :
    scalarSubgroup n F ≤ Subgroup.center (SpecialClifford n F) := by
  rintro g ⟨z, rfl⟩
  exact scalar_mem_center n F z

instance scalarSubgroup_normal : (scalarSubgroup n F).Normal where
  conj_mem _ hg a := by
    obtain ⟨z, rfl⟩ := hg
    refine ⟨z, ?_⟩
    rw [Subgroup.mem_center_iff.mp (scalar_mem_center n F z) a,
      mul_assoc, mul_inv_cancel, mul_one]

abbrev ScalarQuotient := SpecialClifford n F ⧸ scalarSubgroup n F

variable {p f : ℕ} [Finite F] [CharP F p]
variable (parameters : OddFieldParameters F p f) (rank : 3 ≤ n) (N : NormSource n F)
variable (source : Source n F p f parameters rank N)

theorem scalarSubgroup_eq_kernel :
    scalarSubgroup n F = (projection n F source.det_one).ker := by
  ext g
  constructor
  · rintro ⟨z, rfl⟩
    exact projection_scalar n F source.det_one z
  · intro hg
    obtain ⟨z, hz⟩ := (source.scalar_kernel g).mp hg
    exact ⟨z, toClifford_injective n F ((toClifford_scalar n F z).trans hz.symm)⟩

/-- The quotient equivalence induced by the same actual SO projection. -/
def scalarQuotientEquiv : ScalarQuotient n F ≃*
    TypeBOrthogonalOmegaCarriers.SpecialOrthogonal n F :=
  (QuotientGroup.quotientMulEquivOfEq
    (scalarSubgroup_eq_kernel n F parameters rank N source)).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (projection n F source.det_one) source.onto)

@[simp] theorem scalarQuotientEquiv_mk (g : SpecialClifford n F) :
    scalarQuotientEquiv n F parameters rank N source
        (QuotientGroup.mk' (scalarSubgroup n F) g) =
      projection n F source.det_one g := rfl

end Scalars

section FieldDescent

variable {n p f : ℕ} {F : Type} [Field F] [Finite F] [CharP F p]
variable {N : NormSource n F} {parameters : OddFieldParameters F p f}
variable (field : FieldActionSource n F p f parameters N)

theorem scalarSubgroup_map_field (e : FieldGroup f) :
    (scalarSubgroup n F).map (field.action e).toMonoidHom = scalarSubgroup n F := by
  ext g
  constructor
  · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
    exact ⟨field.scalarAction e z,
      (TypeBCliffordOrthogonalFieldAction.scalar_natural field e z).symm⟩
  · rintro ⟨z, rfl⟩
    refine ⟨scalar n F (field.scalarAction e⁻¹ z), ⟨field.scalarAction e⁻¹ z, rfl⟩, ?_⟩
    change field.action e (scalar n F (field.scalarAction e⁻¹ z)) = scalar n F z
    rw [TypeBCliffordOrthogonalFieldAction.scalar_natural]
    rw [map_inv]
    exact congrArg (scalar n F) ((field.scalarAction e).apply_symm_apply z)

def quotientFieldAutomorphism (e : FieldGroup f) : MulAut (ScalarQuotient n F) :=
  QuotientGroup.congr (scalarSubgroup n F) (scalarSubgroup n F)
    (field.action e) (scalarSubgroup_map_field field e)

@[simp] theorem quotientFieldAutomorphism_mk (e : FieldGroup f) (g : SpecialClifford n F) :
    quotientFieldAutomorphism field e (QuotientGroup.mk' (scalarSubgroup n F) g) =
      QuotientGroup.mk' (scalarSubgroup n F) (field.action e g) := rfl

/-- Descent of the already fixed complete cyclic field action. -/
def quotientFieldAction : FieldGroup f →* MulAut (ScalarQuotient n F) where
  toFun := quotientFieldAutomorphism field
  map_one' := by
    apply MulEquiv.ext
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (scalarSubgroup n F) x
    rw [quotientFieldAutomorphism_mk, map_one]
    rfl
  map_mul' e d := by
    apply MulEquiv.ext
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (scalarSubgroup n F) x
    change quotientFieldAutomorphism field (e * d) (QuotientGroup.mk' (scalarSubgroup n F) g) =
      quotientFieldAutomorphism field e
        (quotientFieldAutomorphism field d (QuotientGroup.mk' (scalarSubgroup n F) g))
    rw [quotientFieldAutomorphism_mk, quotientFieldAutomorphism_mk,
      quotientFieldAutomorphism_mk, map_mul]
    rfl

@[simp] theorem quotientFieldAction_mk (e : FieldGroup f) (g : SpecialClifford n F) :
    quotientFieldAction field e (QuotientGroup.mk' (scalarSubgroup n F) g) =
      QuotientGroup.mk' (scalarSubgroup n F) (field.action e g) := rfl

end FieldDescent

section SOField

variable (n : ℕ) (F : Type) [Field F]
variable {p f : ℕ} [Finite F] [CharP F p]
variable (parameters : OddFieldParameters F p f) (rank : 3 ≤ n) (N : NormSource n F)
variable (source : Source n F p f parameters rank N)
variable (field : FieldActionSource n F p f parameters N)

/-- Transport the descended action through the actual scalar quotient,
retaining the same full FieldGroup and its distinguished generator. -/
def soFieldAction : FieldGroup f →* MulAut
    (TypeBOrthogonalOmegaCarriers.SpecialOrthogonal n F) :=
  (MulAut.congr (scalarQuotientEquiv n F parameters rank N source)).toMonoidHom.comp
    (quotientFieldAction field)

theorem soFieldAction_quotient (e : FieldGroup f) (x : ScalarQuotient n F) :
    soFieldAction n F parameters rank N source field e
        (scalarQuotientEquiv n F parameters rank N source x) =
      scalarQuotientEquiv n F parameters rank N source (quotientFieldAction field e x) := by
  change scalarQuotientEquiv n F parameters rank N source
      (quotientFieldAction field e
        ((scalarQuotientEquiv n F parameters rank N source).symm
          (scalarQuotientEquiv n F parameters rank N source x))) = _
  rw [MulEquiv.symm_apply_apply]

/-- Exact all-field-element naturality of the same SO projection. -/
theorem projection_field (e : FieldGroup f) (g : SpecialClifford n F) :
    projection n F source.det_one (field.action e g) =
      soFieldAction n F parameters rank N source field e (projection n F source.det_one g) := by
  have h := soFieldAction_quotient n F parameters rank N source field e
    (QuotientGroup.mk' (scalarSubgroup n F) g)
  rw [quotientFieldAction_mk, scalarQuotientEquiv_mk, scalarQuotientEquiv_mk] at h
  exact h.symm

/-- The target ambient is actual SO with the transported actual field action. -/
abbrev OrthogonalAmbient := TypeBOrthogonalOmegaCarriers.SpecialOrthogonal n F
  ⋊[soFieldAction n F parameters rank N source field] FieldGroup f

/-- The map on the already fixed source semidirect product is pi on the
Clifford coordinate and the identity on the actual cyclic field coordinate. -/
def ambientProjection : TypeBWeightStabilizerSource.Ambient field →*
    OrthogonalAmbient n F parameters rank N source field :=
  SemidirectProduct.map (projection n F source.det_one) (MonoidHom.id (FieldGroup f))
    (by
      intro e
      apply MonoidHom.ext
      exact projection_field n F parameters rank N source field e)

@[simp] theorem ambientProjection_left (a : TypeBWeightStabilizerSource.Ambient field) :
    (ambientProjection n F parameters rank N source field a).left =
      projection n F source.det_one a.left := rfl

@[simp] theorem ambientProjection_right (a : TypeBWeightStabilizerSource.Ambient field) :
    (ambientProjection n F parameters rank N source field a).right = a.right := rfl

@[simp] theorem ambientProjection_inl (g : SpecialClifford n F) :
    ambientProjection n F parameters rank N source field (SemidirectProduct.inl g) =
      SemidirectProduct.inl (projection n F source.det_one g) := by
  apply SemidirectProduct.ext <;> rfl

@[simp] theorem ambientProjection_inr (e : FieldGroup f) :
    ambientProjection n F parameters rank N source field (SemidirectProduct.inr e) =
      SemidirectProduct.inr e := by
  apply SemidirectProduct.ext
  · exact map_one _
  · rfl

theorem ambientProjection_surjective :
    Function.Surjective (ambientProjection n F parameters rank N source field) := by
  intro a
  obtain ⟨g, hg⟩ := source.onto a.left
  refine ⟨⟨g, a.right⟩, ?_⟩
  apply SemidirectProduct.ext
  · exact hg
  · rfl

theorem ambientProjection_eq_one_iff (a : TypeBWeightStabilizerSource.Ambient field) :
    ambientProjection n F parameters rank N source field a = 1 ↔
      a.right = 1 ∧ a.left ∈ scalarSubgroup n F := by
  constructor
  · intro h
    refine ⟨congrArg SemidirectProduct.right h, ?_⟩
    rw [scalarSubgroup_eq_kernel n F parameters rank N source]
    exact congrArg SemidirectProduct.left h
  · rintro ⟨hr, hl⟩
    apply SemidirectProduct.ext
    · rw [scalarSubgroup_eq_kernel n F parameters rank N source] at hl
      exact hl
    · exact hr

/-- The actual scalar subgroup in the semidirect ambient has field
coordinate one. It is not declared to be the ambient centre. -/
def embeddedScalars : Subgroup (TypeBWeightStabilizerSource.Ambient field) :=
  (scalarSubgroup n F).map SemidirectProduct.inl

theorem ambient_kernel_eq_embeddedScalars :
    (ambientProjection n F parameters rank N source field).ker =
      embeddedScalars n F parameters N field := by
  ext a
  constructor
  · intro ha
    obtain ⟨hr, hl⟩ := (ambientProjection_eq_one_iff n F parameters rank N source field a).mp ha
    refine ⟨a.left, hl, ?_⟩
    apply SemidirectProduct.ext
    · rfl
    · exact hr.symm
  · rintro ⟨g, hg, rfl⟩
    exact (ambientProjection_eq_one_iff n F parameters rank N source field
      (SemidirectProduct.inl g)).mpr ⟨rfl, hg⟩

end SOField

end ModularRep.PaperProofs.TypeBCliffordOrthogonalAmbientQuotient


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
