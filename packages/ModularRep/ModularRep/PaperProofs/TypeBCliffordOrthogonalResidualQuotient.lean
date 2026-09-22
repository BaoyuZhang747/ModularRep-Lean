import ModularRep.PaperProofs.TypeBCliffordOrthogonalAmbientQuotient
import ModularRep.PaperProofs.TypeBCentralKernelSpinBinding

/-!
# The actual Spin-centre quotient and its residual scalar kernel

The source ambient is the fixed special-Clifford semidirect product. The
subgroup being divided out is exactly `TypeBCentralKernelSpinBinding.P`,
the image of the literal Spin centre. Its inclusion in the SO projection
kernel is deduced from the existing centre-order source and the checked
Spin-kernel theorem. Mathlib's quotient lift then gives the actual map
from this quotient to the already constructed SO semidirect field group.

The residual kernel is the image of the embedded scalar subgroup. The
scalar-unit map to this image kills exactly the two scalar signs. No
ambient centrality, full-automorphism identification or new source occurs.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBCliffordOrthogonalResidualQuotient

open TypeBCliffordCarriers TypeBCliffordScalarNorm
open TypeBCliffordOrthogonalSourceBinding TypeBCliffordOrthogonalAmbientQuotient
open TypeBCentralKernelCarriers

variable (n : ℕ) (F : Type) [Field F]
variable {p f : ℕ} [Finite F] [CharP F p]
variable (parameters : OddFieldParameters F p f) (N : NormSource n F)
variable (field : FieldActionSource n F p f parameters N)

/-- This is the existing literal ambient quotient by the embedded Spin centre. -/
abbrev ResidualAmbient := QuotientA (TypeBCentralKernelSpinBinding.P field)

/-- The residual scalars are defined as the actual scalar subgroup image. -/
def residualScalars : Subgroup (ResidualAmbient n F parameters N field) :=
  (embeddedScalars n F parameters N field).map
    (qA (TypeBCentralKernelSpinBinding.P field))

/-- Actual field units, embedded in the Clifford coordinate, then quotiented. -/
def residualScalarMap : Fˣ →* ResidualAmbient n F parameters N field :=
  (qA (TypeBCentralKernelSpinBinding.P field)).comp
    (SemidirectProduct.inl.comp (scalar n F))

@[simp] theorem residualScalarMap_value (z : Fˣ) :
    residualScalarMap n F parameters N field z =
      qA (TypeBCentralKernelSpinBinding.P field)
        (SemidirectProduct.inl (scalar n F z)) := rfl

theorem residualScalarMap_range :
    (residualScalarMap n F parameters N field).range =
      residualScalars n F parameters N field := by
  ext a
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨SemidirectProduct.inl (scalar n F z),
      ⟨scalar n F z, ⟨z, rfl⟩, rfl⟩, rfl⟩
  · rintro ⟨a, ⟨g, ⟨z, rfl⟩, rfl⟩, rfl⟩
    exact ⟨z, rfl⟩

variable (rank : 3 ≤ n)
variable (source : Source n F p f parameters rank N)
variable (centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n p f F N)

include centre in
/-- The actual Spin centre, rather than the entire Clifford scalar group,
is killed by the already constructed ambient projection. -/
theorem spinCentre_le_ambient_kernel :
    TypeBCentralKernelSpinBinding.P field ≤
      (ambientProjection n F parameters rank N source field).ker := by
  rintro a ⟨g, hg, rfl⟩
  have hk : spinProjection n F parameters rank N source g = 1 := by
    rw [← spin_kernel_eq_center n F N parameters rank source centre] at hg
    exact hg
  apply SemidirectProduct.ext
  · exact congrArg Subtype.val hk
  · rfl

include rank source centre in
theorem spinCentre_le_embeddedScalars :
    TypeBCentralKernelSpinBinding.P field ≤ embeddedScalars n F parameters N field := by
  rw [← ambient_kernel_eq_embeddedScalars n F parameters rank N source field]
  exact spinCentre_le_ambient_kernel n F parameters N field rank source centre

/-- The quotient factor uses the existing actual Spin-centre subgroup and
the same SO/field projection. Its descent guard is a checked deduction. -/
def residualProjection : ResidualAmbient n F parameters N field →*
    OrthogonalAmbient n F parameters rank N source field :=
  QuotientGroup.lift (TypeBCentralKernelSpinBinding.P field)
    (ambientProjection n F parameters rank N source field)
    (spinCentre_le_ambient_kernel n F parameters N field rank source centre)

@[simp] theorem residualProjection_mk (a : TypeBWeightStabilizerSource.Ambient field) :
    residualProjection n F parameters N field rank source centre
        (qA (TypeBCentralKernelSpinBinding.P field) a) =
      ambientProjection n F parameters rank N source field a := rfl

theorem residualProjection_comp_qA :
    (residualProjection n F parameters N field rank source centre).comp
        (qA (TypeBCentralKernelSpinBinding.P field)) =
      ambientProjection n F parameters rank N source field := rfl

@[simp] theorem residualProjection_mk_left (a : TypeBWeightStabilizerSource.Ambient field) :
    (residualProjection n F parameters N field rank source centre
        (qA (TypeBCentralKernelSpinBinding.P field) a)).left =
      projection n F source.det_one a.left := rfl

@[simp] theorem residualProjection_mk_right (a : TypeBWeightStabilizerSource.Ambient field) :
    (residualProjection n F parameters N field rank source centre
        (qA (TypeBCentralKernelSpinBinding.P field) a)).right = a.right := rfl

@[simp] theorem residualProjection_inl (g : SpecialClifford n F) :
    residualProjection n F parameters N field rank source centre
        (qA (TypeBCentralKernelSpinBinding.P field) (SemidirectProduct.inl g)) =
      SemidirectProduct.inl (projection n F source.det_one g) := by
  exact ambientProjection_inl n F parameters rank N source field g

@[simp] theorem residualProjection_inr (e : FieldGroup f) :
    residualProjection n F parameters N field rank source centre
        (qA (TypeBCentralKernelSpinBinding.P field) (SemidirectProduct.inr e)) =
      SemidirectProduct.inr e := by
  exact ambientProjection_inr n F parameters rank N source field e

@[simp] theorem residualProjection_spinEmbedding (g : Spin n F N) :
    residualProjection n F parameters N field rank source centre
        (qA (TypeBCentralKernelSpinBinding.P field)
          (TypeBWeightStabilizerSource.spinEmbedding field g)) =
      SemidirectProduct.inl (spinProjection n F parameters rank N source g).val := by
  exact ambientProjection_inl n F parameters rank N source field g.val

theorem residualProjection_surjective :
    Function.Surjective (residualProjection n F parameters N field rank source centre) :=
  QuotientGroup.lift_surjective_of_surjective
    (TypeBCentralKernelSpinBinding.P field)
    (ambientProjection n F parameters rank N source field)
    (ambientProjection_surjective n F parameters rank N source field)
    (spinCentre_le_ambient_kernel n F parameters N field rank source centre)

/-- The remaining kernel is the image of the actual embedded scalars. -/
theorem residualProjection_kernel :
    (residualProjection n F parameters N field rank source centre).ker =
      residualScalars n F parameters N field := by
  change (QuotientGroup.lift (TypeBCentralKernelSpinBinding.P field)
    (ambientProjection n F parameters rank N source field)
    (spinCentre_le_ambient_kernel n F parameters N field rank source centre)).ker = _
  rw [QuotientGroup.ker_lift,
    ambient_kernel_eq_embeddedScalars n F parameters rank N source field]
  rfl

theorem residualProjection_eq_one_iff (a : ResidualAmbient n F parameters N field) :
    residualProjection n F parameters N field rank source centre a = 1 ↔
      a ∈ residualScalars n F parameters N field := by
  change a ∈ (residualProjection n F parameters N field rank source centre).ker ↔ _
  rw [residualProjection_kernel]

include rank source centre in
/-- In this literal quotient, precisely the scalar signs become trivial. -/
theorem residualScalarMap_eq_one_iff (z : Fˣ) :
    residualScalarMap n F parameters N field z = 1 ↔ z = 1 ∨ z = -1 := by
  change qA (TypeBCentralKernelSpinBinding.P field)
    (SemidirectProduct.inl (scalar n F z)) = 1 ↔ _
  rw [show (qA (TypeBCentralKernelSpinBinding.P field)
      (SemidirectProduct.inl (scalar n F z)) = 1) ↔
      SemidirectProduct.inl (scalar n F z) ∈ TypeBCentralKernelSpinBinding.P field from
    QuotientGroup.eq_one_iff (N := TypeBCentralKernelSpinBinding.P field) _]
  constructor
  · rintro ⟨g, hg, heq⟩
    have gvalue : g.val = scalar n F z := congrArg SemidirectProduct.left heq
    have hk : spinProjection n F parameters rank N source g = 1 := by
      rw [← spin_kernel_eq_center n F N parameters rank source centre] at hg
      exact hg
    rcases (spinProjection_eq_one_iff n F N parameters rank source g).mp hk with rfl | rfl
    · left
      apply scalar_injective n F
      exact gvalue.symm.trans (map_one (scalar n F)).symm
    · right
      exact scalar_injective n F gvalue.symm
  · rintro (rfl | rfl)
    · exact ⟨1, (Subgroup.center (Spin n F N)).one_mem, by
        apply SemidirectProduct.ext
        · exact (map_one (scalar n F)).symm
        · rfl⟩
    · exact ⟨minusOneSpin n F N, minusOneSpin_central n F N, rfl⟩

/-- The first-isomorphism identification uses the same scalar-unit map.
The preceding theorem identifies this kernel literally as the scalar signs. -/
def scalarSignsQuotientEquiv :
    (Fˣ ⧸ (residualScalarMap n F parameters N field).ker) ≃*
      residualScalars n F parameters N field :=
  (QuotientGroup.quotientKerEquivRange (residualScalarMap n F parameters N field)).trans
    (MulEquiv.subgroupCongr (residualScalarMap_range n F parameters N field))

@[simp] theorem scalarSignsQuotientEquiv_mk (z : Fˣ) :
    (scalarSignsQuotientEquiv n F parameters N field
      (QuotientGroup.mk' (residualScalarMap n F parameters N field).ker z) :
        ResidualAmbient n F parameters N field) =
      qA (TypeBCentralKernelSpinBinding.P field)
        (SemidirectProduct.inl (scalar n F z)) := rfl

end ModularRep.PaperProofs.TypeBCliffordOrthogonalResidualQuotient


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
