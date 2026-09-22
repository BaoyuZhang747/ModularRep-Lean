import ModularRep.PaperProofs.TypeBCriterionCarrierBindings

/-!
# Binding the published Type B weight stabilizers to the criterion

The source and criterion use the same special Clifford/Spin/Frobenius
carriers. This file identifies their raw normalizer inertias and the range
of the actual Spin-field embedding. The FLZ Proposition 7.5 certificate is
then applied to the criterion's literal factors. No equality of actions,
inertias or unnamed local carriers is an additional source input.
-/

noncomputable section

open scoped Pointwise

namespace ModularRep.PaperProofs.TypeBSourceStabilizerBindings

open ModularRep TypeBCliffordCarriers
open TypeBCriterionHypotheses TypeBCriterionCarrierBindings

variable {n p f ell : ℕ} {F K : Type}
variable [Field F] [Finite F] [CharP F p] [NeZero f]
variable [Field K] [CharZero K] [IsAlgClosed K]
variable (N : NormSource n F) [Finite (SpecialClifford n F)]
variable {parameters : OddFieldParameters F p f}
variable (fs : FieldActionSource n F p f parameters N)

/-- The source's Spin-field embedding has exactly the criterion's G E range. -/
theorem spinField_range :
    (TypeBWeightStabilizerSource.spinFieldEmbedding fs).range =
      baseFieldGroup (SpinSubgroup n F N) fs.action := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    have ha : TypeBWeightStabilizerSource.spinFieldEmbedding fs a =
        baseEmbedding (SpinSubgroup n F N) fs.action a.left *
          SemidirectProduct.inr a.right := by
      apply SemidirectProduct.ext <;> simp [baseEmbedding]
    rw [ha]
    exact (baseFieldGroup (SpinSubgroup n F N) fs.action).mul_mem
      ((show embeddedG (SpinSubgroup n F N) fs.action ≤
        baseFieldGroup (SpinSubgroup n F N) fs.action from le_sup_left) ⟨a.left, rfl⟩)
      ((show embeddedE fs.action ≤ baseFieldGroup (SpinSubgroup n F N) fs.action from
        le_sup_right) ⟨a.right, rfl⟩)
  · apply sup_le
    · rintro _ ⟨g, rfl⟩
      exact ⟨SemidirectProduct.inl g, rfl⟩
    · rintro _ ⟨e, rfl⟩
      exact ⟨SemidirectProduct.inr e, rfl⟩

/-- The two raw stabilizer definitions agree on the actual quotient of
character weights, including the normalizer and inverse-action convention. -/
theorem rawNormalizer_set_eq (W : CharacterWeight ell K (Spin n F N)) :
    (rawNormalizerInertia (SpinSubgroup n F N) fs.action (naturalAction N fs) W :
        Set (Ambient fs.action)) =
      TypeBWeightStabilizerSource.normalizerInertia fs W := by
  ext a
  change
    (CharacterWeight.rightTwistIsoClass
        (TypeBAutomorphismSource.ambientAutomorphism fs a⁻¹)
        (Quotient.mk'' W) = Quotient.mk'' W ∧
      a ∈ Subgroup.normalizer
        (TypeBWeightStabilizerSource.embeddedRadical fs W : Set (Ambient fs.action))) ↔
    (a ∈ Subgroup.normalizer
        (TypeBWeightStabilizerSource.embeddedRadical fs W : Set (Ambient fs.action)) ∧
      CharacterWeight.Isomorphic
        (W.rightTwist (TypeBWeightStabilizerSource.ambientSpinAutomorphism fs a)⁻¹) W)
  rw [map_inv]
  exact ⟨fun h => ⟨h.2, Quotient.exact h.1⟩,
    fun h => ⟨Quotient.sound h.2, h.1⟩⟩

/-- Read FLZ Proposition 7.5 on exactly the literal inertia factors of the
criterion. The original source retains all its rank, prime and field
hypotheses, and its set of raw weights. -/
theorem rawFactorization_of_theorem75
    (source : TypeBWeightStabilizerSource.Theorem75Source (K := K) (ell := ell) fs)
    (W : CharacterWeight ell K (Spin n F N)) :
    RawNormalizerFactorization (SpinSubgroup n F N) fs.action (naturalAction N fs) W := by
  change (rawNormalizerInertia (SpinSubgroup n F N) fs.action (naturalAction N fs) W :
      Set (Ambient fs.action)) =
    ((rawNormalizerInertia (SpinSubgroup n F N) fs.action (naturalAction N fs) W :
      Set (Ambient fs.action)) ∩ (embeddedM fs.action : Set (Ambient fs.action))) *
    ((rawNormalizerInertia (SpinSubgroup n F N) fs.action (naturalAction N fs) W :
      Set (Ambient fs.action)) ∩
      (baseFieldGroup (SpinSubgroup n F N) fs.action : Set (Ambient fs.action)))
  rw [rawNormalizer_set_eq, ← spinField_range]
  exact source.factorization W

end ModularRep.PaperProofs.TypeBSourceStabilizerBindings


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
