import ModularRep.PaperProofs.TypeBLocalOrdinaryGeometry
import Mathlib.Tactic.Group

/-!
# From the raw normalizer product to the weight-class product

FLZ Theorem 2.1(4) uses the raw pair normalizer and the factors M and G E.
Brough--Spaeth Theorem 4.5(iv) uses the weight conjugacy class and the
factors M and E. This module proves the implication for the SAME raw
weight. It opens the actual conjugacy quotient to correct a class-fixed
element by an embedded base element. Raw fixedness normalizes the actual
radical by the natural conjugation square. No orbit or factorization
transport is an external input.
-/

noncomputable section

open scoped Pointwise

namespace ModularRep.PaperProofs.TypeBClassInertiaFactorization

open ModularRep TypeBCriterionHypotheses TypeBLocalOrdinaryGeometry

variable {ell : ℕ} {K M E : Type}
variable [Field K] [CharZero K] [IsAlgClosed K]
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

/-- The actual ambient base inclusion induces precisely the usual raw
weight conjugation action of G. -/
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

/-- The characteristic radical of the raw weight is fixed under a raw
inertia element; its actual embedded subgroup is therefore normalized. -/
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

/-- The explicit normalizer condition in the criterion introduces no
extra raw stabilizer elements and removes none. -/
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

/-- Every base element fixes the actual base-conjugacy class. -/
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

/-- Open the literal orbit quotient: a class-fixed ambient element is a
base element times a raw-fixed element. -/
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
/-- The actual G E subgroup is the product of its actual base and field
inclusions, using normality from the natural action. -/
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

/-- Kernel deduction closing the raw/class mismatch between FLZ 2.1(4)
and Brough--Spaeth 4.5(iv), on exactly the same weight. -/
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

end ModularRep.PaperProofs.TypeBClassInertiaFactorization


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
