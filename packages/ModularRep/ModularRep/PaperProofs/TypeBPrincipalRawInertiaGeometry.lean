import ModularRep.PaperProofs.TypeBSpinRawWeightSeparationBinding

/-!+# Raw inertia inside the inertia of the same weight class

Every raw weight has its literal radical-normalizer inertia contained in
the ambient inertia of its own conjugacy class. Multiplication on the left
by the embedded base group gives that whole class inertia.

These deductions apply to every representative. A principal application
identifies this same class with a matched principal weight class; no raw
field fixation, representative selection or factorization source is used.
-/

noncomputable section
set_option autoImplicit false

open scoped Pointwise

namespace ModularRep.PaperProofs.TypeBPrincipalRawInertiaGeometry

open ModularRep TypeBCriterionHypotheses
open TypeBSpinRawWeightSeparationBinding

variable {ell : ℕ} {K M E : Type}
variable [Field K] [CharZero K]
variable [Group M] [Finite M] [Group E] [Finite E]
variable (G : Subgroup M) [G.Normal] (field : E →* MulAut M)
variable (action : NaturalAction G field)

/-- The inertia retaining the actual embedded radical normalizer is
contained in the inertia of the conjugacy class of the same raw weight. -/
theorem rawNormalizerInertia_le_classInertia (W : CharacterWeight ell K G) :
    rawNormalizerInertia G field action W ≤
      weightClassInertia G field action (classOf G W) :=
  inf_le_left.trans (rawInertia_le_classInertia G field action W)

/-- Every class-fixed actor is an embedded base element followed by an
actor fixing this very raw weight. The product order is base then raw. -/
theorem embeddedG_mul_rawNormalizerInertia_eq_classInertia
    (W : CharacterWeight ell K G) :
    (embeddedG G field : Set (Ambient field)) *
        (rawNormalizerInertia G field action W : Set (Ambient field)) =
      (weightClassInertia G field action (classOf G W) : Set (Ambient field)) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨g, hg, r, hr, rfl⟩
    exact (weightClassInertia G field action (classOf G W)).mul_mem
      (embeddedG_le_classInertia G field action W hg)
      (rawNormalizerInertia_le_classInertia G field action W hr)
  · intro a ha
    obtain ⟨g, r, hr, hgr⟩ :=
      classInertia_has_base_raw_factors G field action W a ha
    have hrN : r ∈ rawNormalizerInertia G field action W := by
      rw [rawNormalizerInertia_eq_rawInertia]
      exact hr
    exact ⟨baseEmbedding G field g, ⟨g, rfl⟩, r, hrN, hgr⟩

end ModularRep.PaperProofs.TypeBPrincipalRawInertiaGeometry


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
