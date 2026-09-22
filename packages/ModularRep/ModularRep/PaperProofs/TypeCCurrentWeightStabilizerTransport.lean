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

namespace ModularRep.PaperProofs.TypeCCurrentRawWeightClass

open ModularRep TypeBCriterionHypotheses TypeBLocalOrdinaryGeometry

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

end ModularRep.PaperProofs.TypeCCurrentRawWeightClass


/-!
# The actual Type C raw-weight stabilizer conjugation join

Li (2021), Section 2.C, gives G-conjugation coverage by the standard
product radical subgroups. Lemma 5.5(1), printed p.607, gives the raw
M times G E stabilizer product for every own defect-zero character over
each such standard subgroup. The next sentence replaces E by E^x for a
conjugated radical. This module proves the needed fixed-G-E consequence:
conjugation by an element of G preserves both M and G E.

All results here are K deductions on the criterion's actual natural action.
No source theorem is asserted, no family of standard subgroups is invented,
and no class-level coverage substitutes for transport of the own ordinary
character. The final consumer takes group-only coverage and the standard
subgroup statement; it derives the formula for every actual raw weight,
then uses the existing raw-to-class theorem on that same weight.
-/

noncomputable section

open scoped Pointwise

namespace ModularRep.PaperProofs.TypeCCurrentWeightStabilizerTransport

open ModularRep TypeBCriterionHypotheses TypeBLocalOrdinaryGeometry
open TypeCCurrentRawWeightClass

section GroupProduct

variable {A : Type} [Group A]

/-- Conjugation by an element in both fixed factors preserves the actual
intersection-product formula. No normality or independent image equality
is required. -/
theorem intersection_product_map_conj
    (I L R : Subgroup A) (h : A) (hL : h ∈ L) (hR : h ∈ R)
    (product : (I : Set A) = (↑(I ⊓ L) : Set A) * (↑(I ⊓ R) : Set A)) :
    let J := I.map (MulAut.conj h).toMonoidHom
    (J : Set A) = (↑(J ⊓ L) : Set A) * (↑(J ⊓ R) : Set A) := by
  dsimp only
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := hz
    change y ∈ (I : Set A) at hy
    rw [product] at hy
    obtain ⟨l, hl, r, hr, rfl⟩ := hy
    refine ⟨MulAut.conj h l, ⟨⟨l, hl.1, rfl⟩, ?_⟩,
      MulAut.conj h r, ⟨⟨r, hr.1, rfl⟩, ?_⟩, (map_mul _ _ _).symm⟩
    · exact L.mul_mem (L.mul_mem hL hl.2) (L.inv_mem hL)
    · exact R.mul_mem (R.mul_mem hR hr.2) (R.inv_mem hR)
  · rintro z ⟨l, hl, r, hr, rfl⟩
    exact (I.map (MulAut.conj h).toMonoidHom).mul_mem hl.1 hr.1

end GroupProduct

section ActualWeights

variable {ell : ℕ} {K M E : Type}
variable [Field K] [CharZero K]
variable [Group M] [Finite M] [Group E] [Finite E]
variable (G : Subgroup M) [G.Normal] (field : E →* MulAut M)
variable (action : NaturalAction G field)

/-- Positive base conjugation of the whole raw pair. The manuscript right
twist therefore has the inverse conjugation automorphism. -/
def conjugateWeight (W : CharacterWeight ell K G) (g : G) :
    CharacterWeight ell K G :=
  W.rightTwist (MulAut.conj g⁻¹)

@[simp]
theorem conjugateWeight_subgroup (W : CharacterWeight ell K G) (g : G) :
    (conjugateWeight G W g).subgroup =
      W.subgroup.comap (MulAut.conj g⁻¹).toMonoidHom := rfl

/-- The transported pair retains precisely the original own character
pulled through its canonical normalizer-quotient equivalence. -/
theorem conjugateWeight_localCharacter (W : CharacterWeight ell K G) (g : G)
    (x : NormalizerQuotient (conjugateWeight G W g).subgroup) :
    (conjugateWeight G W g).localCharacter x =
      W.localCharacter (rightNormalizerQuotientEquiv
        (MulAut.conj g⁻¹) W.subgroup x) := rfl

/-- Cancellation is equality of the whole pair, including its own local
ordinary character, by the checked right-twist composition law. -/
theorem conjugateWeight_inverse (W : CharacterWeight ell K G) (g : G) :
    conjugateWeight G (conjugateWeight G W g) g⁻¹ = W := by
  simp only [conjugateWeight, inv_inv]
  have h := CharacterWeight.eq_of_isomorphic
    (CharacterWeight.rightTwist_mul_isomorphic W
      (MulAut.conj g⁻¹) (MulAut.conj g))
  have hproduct : MulAut.conj g⁻¹ * MulAut.conj g = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  rw [hproduct] at h
  exact h.trans (CharacterWeight.eq_of_isomorphic
    (CharacterWeight.rightTwist_one_isomorphic W))

/-- The actual ambient raw stabilizer of the conjugated pair is the image
under conjugation by the same embedded base element. -/
theorem rawInertia_conjugateWeight (W : CharacterWeight ell K G) (g : G) :
    rawInertia G field action (conjugateWeight G W g) =
      (rawInertia G field action W).map
        (MulAut.conj (baseEmbedding G field g)).toMonoidHom := by
  letI := rawAmbientAction (ell := ell) (K := K) G field action
  change MulAction.stabilizer (Ambient field)
      (g • (Quotient.mk'' W : Raw (ell := ell) (K := K) G)) =
    (MulAction.stabilizer (Ambient field)
      (Quotient.mk'' W : Raw (ell := ell) (K := K) G)).map
        (MulAut.conj (baseEmbedding G field g)).toMonoidHom
  rw [← base_smul_raw G field action g]
  exact MulAction.stabilizer_smul_eq_stabilizer_map_conj _ _

/-- The explicit radical normalizer introduces no change to the same
raw-pair stabilizer, so the identical image formula applies to it. -/
theorem rawNormalizerInertia_conjugateWeight
    (W : CharacterWeight ell K G) (g : G) :
    rawNormalizerInertia G field action (conjugateWeight G W g) =
      (rawNormalizerInertia G field action W).map
        (MulAut.conj (baseEmbedding G field g)).toMonoidHom := by
  simp only [rawNormalizerInertia_eq_rawInertia, rawInertia_conjugateWeight]

/-- Unlike the field subgroup alone, both factors M and G E contain the
conjugating base element. The fixed-factor raw formula therefore passes
to every actual G-conjugate pair. -/
theorem rawFactorization_conjugateWeight
    (W : CharacterWeight ell K G) (g : G)
    (raw : RawNormalizerFactorization G field action W) :
    RawNormalizerFactorization G field action (conjugateWeight G W g) := by
  have hM : baseEmbedding G field g ∈ embeddedM field := ⟨g.1, rfl⟩
  have hGE : baseEmbedding G field g ∈ baseFieldGroup G field :=
    (embeddedG_le_baseFieldGroup G field) ⟨g, rfl⟩
  have h := intersection_product_map_conj
    (rawNormalizerInertia G field action W)
    (embeddedM field) (baseFieldGroup G field)
    (baseEmbedding G field g) hM hGE raw
  change (rawNormalizerInertia G field action (conjugateWeight G W g) :
      Set (Ambient field)) =
    (↑(rawNormalizerInertia G field action (conjugateWeight G W g) ⊓
      embeddedM field) : Set (Ambient field)) *
    (↑(rawNormalizerInertia G field action (conjugateWeight G W g) ⊓
      baseFieldGroup G field) : Set (Ambient field))
  rw [rawNormalizerInertia_conjugateWeight]
  exact h

theorem rawFactorization_conjugateWeight_iff
    (W : CharacterWeight ell K G) (g : G) :
    RawNormalizerFactorization G field action (conjugateWeight G W g) ↔
      RawNormalizerFactorization G field action W := by
  constructor
  · intro h
    have hback := rawFactorization_conjugateWeight G field action
      (conjugateWeight G W g) g⁻¹ h
    simpa only [conjugateWeight_inverse] using hback
  · exact rawFactorization_conjugateWeight G field action W g

/-- The source domain is only group-level conjugation coverage and the
standard-subgroup formula for each actual own local character. Twisting W
itself chooses the matching standard pair; no weight/character coverage
or class-level factorization is a source premise.

For Li's application, R must be the actual product-basic subgroup family
of Section 2.C, and `standard` is Lemma 5.5(1). This generic K theorem does
not assert either external input or identify an arbitrary family with it. -/
theorem rawFactorization_of_standard_subgroups
    {Index : Type} (R : Index → Subgroup G)
    (coverage : ∀ Q : Subgroup G, IsRadicalSubgroup ell Q →
      ∃ (i : Index) (g : G),
        Q.comap (MulAut.conj g⁻¹).toMonoidHom = R i)
    (standard : ∀ (i : Index) (W : CharacterWeight ell K G),
      W.subgroup = R i → RawNormalizerFactorization G field action W)
    (W : CharacterWeight ell K G) :
    RawNormalizerFactorization G field action W := by
  obtain ⟨i, g, hsubgroup⟩ := coverage W.subgroup W.radical
  have hstandard := standard i (conjugateWeight G W g) hsubgroup
  exact (rawFactorization_conjugateWeight_iff G field action W g).mp hstandard

/-- The class formula concerns the SAME pair and is obtained from the
accepted generic raw-to-class K bridge, not from a selected representative
or an independently supplied class stabilizer. -/
theorem weightClassFactorization_of_standard_subgroups
    {Index : Type} (R : Index → Subgroup G)
    (coverage : ∀ Q : Subgroup G, IsRadicalSubgroup ell Q →
      ∃ (i : Index) (g : G),
        Q.comap (MulAut.conj g⁻¹).toMonoidHom = R i)
    (standard : ∀ (i : Index) (W : CharacterWeight ell K G),
      W.subgroup = R i → RawNormalizerFactorization G field action W)
    (W : CharacterWeight ell K G) :
    WeightClassFactorization G field action W :=
  weightClassFactorization_of_rawNormalizerFactorization G field action W
    (rawFactorization_of_standard_subgroups G field action R coverage standard W)

/-- Identity is now a valid normalizer conjugator because K has proved the
raw formula for every own pair. Both clauses use exactly the criterion's
computed identity-twisted pair. -/
theorem rawNormalizerClause_of_standard_subgroups
    {Index : Type} (R : Index → Subgroup G)
    (coverage : ∀ Q : Subgroup G, IsRadicalSubgroup ell Q →
      ∃ (i : Index) (g : G),
        Q.comap (MulAut.conj g⁻¹).toMonoidHom = R i)
    (standard : ∀ (i : Index) (W : CharacterWeight ell K G),
      W.subgroup = R i → RawNormalizerFactorization G field action W) :
    RawNormalizerClause (ell := ell) (K := K) G field action := by
  intro W
  refine ⟨1, (Subgroup.normalizer _).one_mem, ?_, ?_⟩
  · exact rawFactorization_of_standard_subgroups G field action R coverage standard _
  · exact weightClassFactorization_of_standard_subgroups
      G field action R coverage standard _

end ActualWeights

end ModularRep.PaperProofs.TypeCCurrentWeightStabilizerTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
