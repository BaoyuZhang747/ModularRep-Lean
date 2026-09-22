import ModularRep.PaperProofs.TypeBPrincipalRawInertiaGeometry
import ModularRep.PaperProofs.TypeBSemidirectFixedFieldFactorization

/-!
# Principal selectors on the actual semidirect product

Field fixation of a weight class permits an inner correction of each field
actor. The corrected actor fixes the prescribed raw representative. This
gives the literal M-times-GE raw-inertia product without asserting that the
uncorrected field actor fixes that representative.

The principal application supplies field containment from the actual FYZ
class action. The character containment comes from the internally derived
Spin selector and its calibrated matrix transport.
-/

noncomputable section
set_option autoImplicit false

open scoped Pointwise

namespace ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionSelectors

open ModularRep TypeBCriterionHypotheses
open TypeBSpinRawWeightSeparationBinding
open TypeBSemidirectFixedFieldFactorization

variable {ell : ℕ} {K M E : Type}
variable [Field K] [CharZero K]
variable [Group M] [Finite M] [Group E] [Finite E]
variable (G : Subgroup M) [G.Normal] (field : E →* MulAut M)
variable (action : NaturalAction G field)

/-- The same raw weight has the published class-inertia product. -/
theorem weightClassFactorization_of_field_fixed (W : CharacterWeight ell K G)
    (field_le : embeddedE field ≤
      weightClassInertia G field action (classOf G W)) :
    WeightClassFactorization G field action W :=
  subgroup_eq_product_of_inr_le field
    (weightClassInertia G field action (classOf G W)) field_le

/-- An inner correction retains the prescribed representative and gives
the stronger raw-normalizer product used in the cyclic criterion. -/
theorem rawNormalizerFactorization_of_class_field_fixed
    (W : CharacterWeight ell K G)
    (field_le : embeddedE field ≤
      weightClassInertia G field action (classOf G W)) :
    RawNormalizerFactorization G field action W := by
  let I := rawNormalizerInertia G field action W
  change (I : Set (Ambient field)) =
    ((I ⊓ embeddedM field : Subgroup (Ambient field)) : Set (Ambient field)) *
      ((I ⊓ baseFieldGroup G field : Subgroup (Ambient field)) : Set (Ambient field))
  apply Set.Subset.antisymm
  · intro a ha
    obtain ⟨g, s, hs, hgs⟩ := classInertia_has_base_raw_factors
      G field action W (SemidirectProduct.inr a.right)
      (field_le ⟨a.right, rfl⟩)
    have hsI : s ∈ I := by
      change s ∈ rawNormalizerInertia G field action W
      rw [rawNormalizerInertia_eq_rawInertia]
      exact hs
    have hsRight : s.right = a.right := by
      have h := congrArg (fun z : Ambient field => z.right) hgs
      simpa [baseEmbedding] using h
    have hsGE : s ∈ baseFieldGroup G field := by
      have hbase : baseEmbedding G field g ∈ baseFieldGroup G field :=
        (show embeddedG G field ≤ baseFieldGroup G field from le_sup_left) ⟨g, rfl⟩
      have hfield : SemidirectProduct.inr a.right ∈ baseFieldGroup G field :=
        (show embeddedE field ≤ baseFieldGroup G field from le_sup_right) ⟨a.right, rfl⟩
      have h := (baseFieldGroup G field).mul_mem
        ((baseFieldGroup G field).inv_mem hbase) hfield
      rw [← hgs] at h
      simpa only [inv_mul_cancel_left] using h
    have hmM : a * s⁻¹ ∈ embeddedM field := by
      change a * s⁻¹ ∈ (SemidirectProduct.inl (φ := field)).range
      rw [SemidirectProduct.range_inl_eq_ker_rightHom]
      change (a * s⁻¹).right = 1
      simp [hsRight]
    exact ⟨a * s⁻¹, ⟨I.mul_mem ha (I.inv_mem hsI), hmM⟩,
      s, ⟨hsI, hsGE⟩, by simp only [inv_mul_cancel_right]⟩
  · rintro _ ⟨m, hm, s, hs, rfl⟩
    exact I.mul_mem hm.1 hs.1

variable {k : Type} [Field k] [CharP k ell] [IsAlgClosed k]
variable (root : PrimeRegularRootEmbedding ell k K G)

/-- The actual field containment gives the character-selector product. -/
theorem brauerFactorization_of_field_fixed (phi : IBr root)
    (field_le : embeddedE field ≤ brauerInertia G field action root phi) :
    BrauerFactorization G field action root phi :=
  subgroup_eq_product_of_inr_le field
    (brauerInertia G field action root phi) field_le

end ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionSelectors


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
