import ModularRep.PaperProofs.TypeBWeightStabilizerSource
import ModularRep.PaperProofs.TypeBFLZLabelSource
import ModularRep.PaperProofs.TypeBCriterionCarrierBindings
import ModularRep.PaperProofs.TypeBLocalOrdinaryGeometry
import Mathlib.Tactic.Group

/-!
# Literal raw Spin weight separation over a splitting ordinary field

The sole E2 field is FLZ Proposition 7.5, pp. 573--574, on every actual
raw Spin weight, with its ordinary normalizer-quotient character. The
finite odd-field, rank, nondefining-prime and sufficient ordinary-root
guards are explicit. No ordinary algebraic closure, Assumption 3.11,
Brauer replacement or criterion conclusion is an input.

The class-inertia consequence is a group-action deduction on the same
raw weight. It repeats the short orbit-quotient argument of the frozen
TypeBClassInertiaFactorization without that theorem's retained ordinary
algebraic-closure guard. It supplies no class factorization source.
-/

noncomputable section
set_option autoImplicit false

open scoped Pointwise

namespace ModularRep.PaperProofs.TypeBSpinRawWeightSeparationBinding

open ModularRep TypeBCliffordCarriers TypeBFLZLabelSource
open TypeBCriterionHypotheses TypeBCriterionCarrierBindings

section Source

variable {n p f ell : ℕ} {F K : Type} [Field F] [Field K]

/-- FLZ Proposition 7.5 on all literal ordinary raw Spin weights.
Enough roots for Spin also suffice for each actual normalizer quotient.
The pointwise inertia uses the existing inverse right-twist convention. -/
structure Theorem75Source
    [finiteField : Finite F] [definingCharacteristic : CharP F p]
    [positiveFieldDegree : NeZero f] [finiteClifford : Finite (Clifford n F)]
    (parameters : OddFieldParameters F p f) (scope : Applicability p ell n)
    (N : NormSource n F) (fs : FieldActionSource n F p f parameters N)
    [ordinaryCharacteristic : CharZero K]
    [ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card (Spin n F N))] : Prop where
  factorization : ∀ W : CharacterWeight ell K (Spin n F N),
    TypeBWeightStabilizerSource.normalizerInertia fs W =
      TypeBWeightStabilizerSource.specialCliffordInertia fs W *
        TypeBWeightStabilizerSource.spinFieldInertia fs W

variable [Finite F] [CharP F p] [NeZero f] [Finite (Clifford n F)] [CharZero K]
variable (parameters : OddFieldParameters F p f) (scope : Applicability p ell n)
variable (N : NormSource n F) (fs : FieldActionSource n F p f parameters N)
variable [HasEnoughRootsOfUnity K (Nat.card (Spin n F N))]

/-- Extract the actual special-Clifford and Spin-field factors from the
published set product, preserving their raw normalizer-inertia membership. -/
theorem exists_normalizer_inertia_factors
    (source : Theorem75Source parameters scope N fs (K := K))
    (W : CharacterWeight ell K (Spin n F N))
    (a : TypeBWeightStabilizerSource.Ambient fs)
    (ha : a ∈ TypeBWeightStabilizerSource.normalizerInertia fs W) :
    ∃ m : SpecialClifford n F, ∃ ge : TypeBWeightStabilizerSource.SpinField fs,
      SemidirectProduct.inl m ∈ TypeBWeightStabilizerSource.normalizerInertia fs W ∧
      TypeBWeightStabilizerSource.spinFieldEmbedding fs ge ∈
        TypeBWeightStabilizerSource.normalizerInertia fs W ∧
      (SemidirectProduct.inl m : TypeBWeightStabilizerSource.Ambient fs) *
        TypeBWeightStabilizerSource.spinFieldEmbedding fs ge = a := by
  rw [source.factorization W] at ha
  rcases Set.mem_mul.mp ha with ⟨x, hx, y, hy, hxy⟩
  rcases hx.2 with ⟨m, hm⟩
  rcases hy.2 with ⟨ge, hge⟩
  refine ⟨m, ge, ?_, ?_, ?_⟩
  · simpa only [hm] using hx.1
  · simpa only [hge] using hy.1
  · simpa only [hm, hge] using hxy

end Source

section ClassTransfer

open TypeBLocalOrdinaryGeometry

variable {ell : ℕ} {K M E : Type}
variable [Field K] [CharZero K]
variable [Group M] [Finite M] [Group E] [Finite E]
variable (G : Subgroup M) [G.Normal] (field : E →* MulAut M)
variable (action : NaturalAction G field)

abbrev Raw := CharacterWeight.IsoClass (p := ell) (K := K) (G := G)

abbrev WeightClass := CharacterWeight.ConjugacyClass (p := ell) (K := K) (G := G)

def rawAmbientAction : MulAction (Ambient field) (Raw (ell := ell) (K := K) G) :=
  CyclicOuterLemma37Concrete.rightAutomorphismAction action.hom

def classAmbientAction :
    MulAction (Ambient field) (WeightClass (ell := ell) (K := K) G) :=
  CyclicOuterLemma37Concrete.rightAutomorphismAction action.hom

/-- The actual embedded base action is the usual raw conjugation action. -/
theorem base_smul_raw (g : G) (r : Raw (ell := ell) (K := K) G) :
    letI := rawAmbientAction (ell := ell) (K := K) G field action
    baseEmbedding G field g • r = g • r := by
  letI := rawAmbientAction (ell := ell) (K := K) G field action
  change CharacterWeight.rightTwistIsoClass
    (action.hom (baseEmbedding G field g)⁻¹) r =
      CharacterWeight.rightTwistIsoClass (MulAut.conj g⁻¹) r
  rw [← map_inv, naturalAction_base]

def classOf (W : CharacterWeight ell K G) : WeightClass (ell := ell) (K := K) G :=
  Quotient.mk'' (Quotient.mk'' W : Raw (ell := ell) (K := K) G)

/-- Raw fixedness normalizes the very same embedded radical. -/
theorem rawInertia_le_radicalNormalizer (W : CharacterWeight ell K G) :
    rawInertia G field action W ≤
      Subgroup.normalizer (embeddedRadical G field W : Set (Ambient field)) := by
  intro a ha
  change CharacterWeight.rightTwistIsoClass (action.hom a⁻¹)
    (Quotient.mk'' W) = Quotient.mk'' W at ha
  obtain ⟨hR, _⟩ := Quotient.exact ha
  change W.subgroup.comap (action.hom a⁻¹).toMonoidHom = W.subgroup at hR
  have hmap : W.subgroup.map (action.hom a).toMonoidHom = W.subgroup := by
    rw [Subgroup.map_equiv_eq_comap_symm']
    rw [map_inv] at hR
    exact hR
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change (W.subgroup.map (baseEmbedding G field)).map
    (MulAut.conj a).toMonoidHom = W.subgroup.map (baseEmbedding G field)
  rw [Subgroup.map_map]
  have hsquare : (MulAut.conj a).toMonoidHom.comp (baseEmbedding G field) =
      (baseEmbedding G field).comp (action.hom a).toMonoidHom := by
    apply MonoidHom.ext
    intro g
    exact (baseEmbedding_natural G field action a g).symm
  rw [hsquare, ← Subgroup.map_map, hmap]

theorem rawNormalizerInertia_eq_rawInertia (W : CharacterWeight ell K G) :
    rawNormalizerInertia G field action W = rawInertia G field action W :=
  inf_eq_left.mpr (rawInertia_le_radicalNormalizer G field action W)

theorem rawInertia_le_classInertia (W : CharacterWeight ell K G) :
    rawInertia G field action W ≤ weightClassInertia G field action (classOf G W) := by
  letI := rawAmbientAction (ell := ell) (K := K) G field action
  letI := classAmbientAction (ell := ell) (K := K) G field action
  intro a ha
  change a • (Quotient.mk'' W : Raw (ell := ell) (K := K) G) = Quotient.mk'' W at ha
  change (Quotient.mk'' (a • (Quotient.mk'' W : Raw (ell := ell) (K := K) G)) :
    WeightClass (ell := ell) (K := K) G) = Quotient.mk'' (Quotient.mk'' W)
  exact congrArg (fun r : Raw (ell := ell) (K := K) G =>
    (Quotient.mk'' r : WeightClass (ell := ell) (K := K) G)) ha

/-- Base conjugation fixes the literal base-conjugacy class. -/
theorem embeddedG_le_classInertia (W : CharacterWeight ell K G) :
    embeddedG G field ≤ weightClassInertia G field action (classOf G W) := by
  letI := rawAmbientAction (ell := ell) (K := K) G field action
  letI := classAmbientAction (ell := ell) (K := K) G field action
  rintro _ ⟨g, rfl⟩
  change (Quotient.mk'' (baseEmbedding G field g •
    (Quotient.mk'' W : Raw (ell := ell) (K := K) G)) :
      WeightClass (ell := ell) (K := K) G) = Quotient.mk'' (Quotient.mk'' W)
  rw [base_smul_raw]
  exact MulAction.orbitRel.Quotient.quotient_smul_eq

/-- Correct a class-fixed actor by an actual embedded base element. -/
theorem classInertia_has_base_raw_factors (W : CharacterWeight ell K G)
    (a : Ambient field) (ha : a ∈ weightClassInertia G field action (classOf G W)) :
    ∃ (g : G) (r : Ambient field), r ∈ rawInertia G field action W ∧
      baseEmbedding G field g * r = a := by
  letI := rawAmbientAction (ell := ell) (K := K) G field action
  letI := classAmbientAction (ell := ell) (K := K) G field action
  change (Quotient.mk'' (a • (Quotient.mk'' W : Raw (ell := ell) (K := K) G)) :
    WeightClass (ell := ell) (K := K) G) = Quotient.mk'' (Quotient.mk'' W) at ha
  obtain ⟨g, hg⟩ := Quotient.exact ha
  refine ⟨g, (baseEmbedding G field g)⁻¹ * a, ?_, by simp [mul_assoc]⟩
  change ((baseEmbedding G field g)⁻¹ * a) •
    (Quotient.mk'' W : Raw (ell := ell) (K := K) G) = Quotient.mk'' W
  rw [mul_smul, ← hg]
  dsimp only
  rw [← base_smul_raw G field action g]
  exact inv_smul_smul _ _

include action in
/-- The actual G E subgroup has the two canonical factors. -/
theorem baseFieldGroup_has_factors (a : Ambient field)
    (ha : a ∈ baseFieldGroup G field) :
    ∃ (g : G) (e : E), baseEmbedding G field g * SemidirectProduct.inr e = a := by
  letI := embeddedG_normal G field action
  change a ∈ (↑(embeddedG G field ⊔ embeddedE field) : Set (Ambient field)) at ha
  rw [Subgroup.normal_mul] at ha
  obtain ⟨x, hx, y, hy, hxy⟩ := ha
  obtain ⟨g, rfl⟩ := hx
  obtain ⟨e, rfl⟩ := hy
  exact ⟨g, e, hxy⟩

/-- The raw M-times-GE product implies the class M-times-E product.
This is entirely a quotient-action argument, with no ordinary closure. -/
theorem weightClassFactorization_of_rawNormalizerFactorization
    (W : CharacterWeight ell K G)
    (raw : RawNormalizerFactorization G field action W) :
    WeightClassFactorization G field action W := by
  let I := weightClassInertia G field action (classOf G W)
  have hbase : embeddedG G field ≤ I := embeddedG_le_classInertia G field action W
  have hraw : rawNormalizerInertia G field action W ≤ I :=
    inf_le_left.trans (rawInertia_le_classInertia G field action W)
  change (I : Set (Ambient field)) =
    (factorInertia field I (embeddedM field) : Set (Ambient field)) *
      (factorInertia field I (embeddedE field) : Set (Ambient field))
  apply Set.Subset.antisymm
  · intro a ha
    obtain ⟨g, r, hr, hgr⟩ := classInertia_has_base_raw_factors G field action W a ha
    have hrN : r ∈ rawNormalizerInertia G field action W := by
      rw [rawNormalizerInertia_eq_rawInertia]
      exact hr
    change r ∈ (rawNormalizerInertia G field action W : Set (Ambient field)) at hrN
    rw [show (rawNormalizerInertia G field action W : Set (Ambient field)) = _ from raw]
      at hrN
    obtain ⟨m, hm, t, ht, hmtr⟩ := hrN
    obtain ⟨h, e, hhet⟩ := baseFieldGroup_has_factors G field action t ht.2
    have hbG : baseEmbedding G field g ∈ I := hbase ⟨g, rfl⟩
    have hbH : baseEmbedding G field h ∈ I := hbase ⟨h, rfl⟩
    have hmI : m ∈ I := hraw hm.1
    have htI : t ∈ I := hraw ht.1
    have heI : SemidirectProduct.inr e ∈ I := by
      have hc := I.mul_mem (I.inv_mem hbH) htI
      rw [← hhet] at hc
      simpa [mul_assoc] using hc
    refine ⟨baseEmbedding G field g * m * baseEmbedding G field h,
      ⟨I.mul_mem (I.mul_mem hbG hmI) hbH,
        (embeddedM field).mul_mem
          ((embeddedM field).mul_mem ⟨g.1, rfl⟩ hm.2) ⟨h.1, rfl⟩⟩,
      SemidirectProduct.inr e, ⟨heI, ⟨e, rfl⟩⟩, ?_⟩
    rw [← hgr, ← hmtr, ← hhet]
    group
  · rintro _ ⟨x, hx, y, hy, rfl⟩
    exact I.mul_mem hx.1 hy.1

end ClassTransfer

section LiteralBinding

variable {n p f ell : ℕ} {F K : Type}
variable [Field F] [Finite F] [CharP F p] [NeZero f] [Finite (Clifford n F)]
variable [Field K] [CharZero K]
variable (parameters : OddFieldParameters F p f) (scope : Applicability p ell n)
variable (N : NormSource n F) (fs : FieldActionSource n F p f parameters N)

/-- The two actual embeddings have the same Spin-field range. -/
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

/-- Bind raw fixedness, its radical normalizer and inverse action exactly. -/
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

variable [HasEnoughRootsOfUnity K (Nat.card (Spin n F N))]
variable (source : Theorem75Source parameters scope N fs (K := K))

include source in
/-- The source supplies the criterion's literal raw product. -/
theorem rawFactorization (W : CharacterWeight ell K (Spin n F N)) :
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

include source in
/-- The class product is derived for the very same raw weight. -/
theorem classFactorization (W : CharacterWeight ell K (Spin n F N)) :
    WeightClassFactorization (SpinSubgroup n F N) fs.action (naturalAction N fs) W :=
  weightClassFactorization_of_rawNormalizerFactorization
    (SpinSubgroup n F N) fs.action (naturalAction N fs) W
    (rawFactorization parameters scope N fs source W)

include source in
/-- Identity is a valid actual normalizer conjugator because the raw
source holds for every weight. Both products are on that same representative. -/
theorem rawNormalizerClause :
    RawNormalizerClause (ell := ell) (K := K)
      (SpinSubgroup n F N) fs.action (naturalAction N fs) := by
  intro W
  refine ⟨1, (Subgroup.normalizer _).one_mem, ?_, ?_⟩
  · exact rawFactorization parameters scope N fs source _
  · exact classFactorization parameters scope N fs source _

end LiteralBinding

end ModularRep.PaperProofs.TypeBSpinRawWeightSeparationBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
