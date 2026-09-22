import ModularRep.PaperProofs.TypeBLocalOrdinaryGeometry

/-!
# Local ordinary character geometry over consistent splitting coefficients

These are the dependent inclusion and character-transport deductions needed
for the scoped local extension. The subgroup carriers, their normality,
the ambient embeddings and the quotient projections are the existing ones.
Only the proof chain whose compiled signatures retain an unnecessary
ordinary coefficient condition is reconstructed here.

Raw fixedness yields invariance of the same normalizer-quotient character.
No character action, geometric equality or extension is supplied as a source.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBLocalOrdinaryGeometrySplitting

open ModularRep OrdinaryIrreducibleCharacter
open TypeBCriterionHypotheses TypeBLocalOrdinaryGeometry CyclicOuterLemma37Concrete

variable {ell : ℕ} {K M E : Type}
variable [Field K] [CharZero K]
variable [Group M] [Finite M] [Group E] [Finite E]
variable (G : Subgroup M) [G.Normal] (field : E →* MulAut M)
variable (action : NaturalAction G field) (W : CharacterWeight ell K G)
variable (factor : Subgroup (Ambient field))
variable (base_le_factor : embeddedG G field ≤ factor)

/-- The actual downstairs normalizer fixes its raw quotient-character
weight, by the checked inner-conjugation calculation. -/
theorem normalizer_mem_rawInertia
    (x : Subgroup.normalizer (W.subgroup : Set G)) :
    baseEmbedding G field x.1 ∈ rawInertia G field action W := by
  change CharacterWeight.rightTwistIsoClass
    (action.hom (baseEmbedding G field x.1)⁻¹)
    (Quotient.mk'' W) = Quotient.mk'' W
  rw [← map_inv, naturalAction_base]
  exact normalizer_fixes_rawWeight
    (canonicalRawNormalizerQuotientInput (p := ell) (K := K) (H := G))
    x.1 (Quotient.mk'' W) x.2

/-- Mapping a normalizer element preserves normalization of the actual
embedded radical. -/
theorem normalizer_mem_embeddedRadical_normalizer
    (x : Subgroup.normalizer (W.subgroup : Set G)) :
    baseEmbedding G field x.1 ∈
      Subgroup.normalizer (embeddedRadical G field W : Set (Ambient field)) :=
  (Subgroup.le_normalizer_map (baseEmbedding G field))
    (Subgroup.mem_map_of_mem (baseEmbedding G field) x.2)

theorem normalizer_mem_rawNormalizerInertia
    (x : Subgroup.normalizer (W.subgroup : Set G)) :
    baseEmbedding G field x.1 ∈ rawNormalizerInertia G field action W :=
  ⟨normalizer_mem_rawInertia G field action W x,
    normalizer_mem_embeddedRadical_normalizer G field W x⟩

/-- The canonical inclusion of N_G(R) into the chosen actual factor
inertia. -/
def normalizerInclusion : Subgroup.normalizer (W.subgroup : Set G) →*
    Inertia G field action W factor where
  toFun x := ⟨baseEmbedding G field x.1,
    normalizer_mem_rawNormalizerInertia G field action W x,
    base_le_factor ⟨x.1, rfl⟩⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' x y := by apply Subtype.ext; exact map_mul _ _ _

@[simp]
theorem normalizerInclusion_value
    (x : Subgroup.normalizer (W.subgroup : Set G)) :
    (normalizerInclusion G field action W factor base_le_factor x : Ambient field) =
      baseEmbedding G field x.1 := rfl

include base_le_factor in
theorem radical_le_inertia : embeddedRadical G field W ≤
    Inertia G field action W factor := by
  rintro _ ⟨r, hr, rfl⟩
  exact (normalizerInclusion G field action W factor base_le_factor
    ⟨r, W.subgroup.le_normalizer hr⟩).property

/-- Stabilizer membership gives the actual dependent character equality,
with the positive conjugation automorphism obtained from the inverse
stabilizer element. -/
theorem inertia_supplies_isomorphic
    (a : Inertia G field action W factor) :
    CharacterWeight.Isomorphic (W.rightTwist (action.hom a.1)) W := by
  have h := (rawInertia G field action W).inv_mem a.property.1.1
  change CharacterWeight.rightTwistIsoClass (action.hom ((a.1)⁻¹)⁻¹)
    (Quotient.mk'' W) = Quotient.mk'' W at h
  simp only [inv_inv] at h
  exact Quotient.exact h

/-- A raw fixedness equality implies invariance of the inflated ordinary
character on actual normalizer elements. This opens the dependent cast
and quotient maps; it is not an additional action certificate. -/
theorem inflated_localCharacter_fixed_of_isomorphic
    (alpha : MulAut G)
    (hfixed : CharacterWeight.Isomorphic (W.rightTwist alpha) W)
    (x y : Subgroup.normalizer (W.subgroup : Set G))
    (hxy : (y : G) = alpha (x : G)) :
    W.localCharacter (QuotientGroup.mk y) =
      W.localCharacter (QuotientGroup.mk x) := by
  change ∃ hR : W.subgroup.comap alpha.toMonoidHom = W.subgroup,
    CharacterWeight.castLocalCharacter hR
      (OrdinaryIrreducibleCharacter.mapEquiv W.localCharacter
        (rightNormalizerQuotientEquiv alpha W.subgroup).symm) = W.localCharacter at hfixed
  obtain ⟨hR, htheta⟩ := hfixed
  have hevaluation := congrArg
    (fun chi : Irr K (NormalizerQuotient W.subgroup) ↦
      chi (QuotientGroup.mk x)) htheta
  have hcast := castLocalCharacter_apply hR
    (OrdinaryIrreducibleCharacter.mapEquiv W.localCharacter
      (rightNormalizerQuotientEquiv alpha W.subgroup).symm) (QuotientGroup.mk x)
  have hvalue : W.localCharacter
      (rightNormalizerQuotientEquiv alpha W.subgroup
        ((MulEquiv.cast (M := fun R : Subgroup G ↦ NormalizerQuotient R) hR).symm
          (QuotientGroup.mk x))) = W.localCharacter (QuotientGroup.mk x) :=
    hcast.symm.trans hevaluation
  have hmk := normalizerQuotientCast_symm_mk hR x
  have hvalue' : W.localCharacter
      (rightNormalizerQuotientEquiv alpha W.subgroup
        (QuotientGroup.mk
          (MulEquiv.cast
            (M := fun R : Subgroup G ↦ Subgroup.normalizer (R : Set G))
            hR.symm x))) = W.localCharacter (QuotientGroup.mk x) :=
    (congrArg (fun q ↦ W.localCharacter
      (rightNormalizerQuotientEquiv alpha W.subgroup q)) hmk).symm.trans hvalue
  change W.localCharacter
      (QuotientGroup.mk (rightNormalizerEquiv alpha W.subgroup
        (MulEquiv.cast
          (M := fun R : Subgroup G ↦ Subgroup.normalizer (R : Set G))
          hR.symm x))) = W.localCharacter (QuotientGroup.mk x) at hvalue'
  have heq : rightNormalizerEquiv alpha W.subgroup
      (MulEquiv.cast
        (M := fun R : Subgroup G ↦ Subgroup.normalizer (R : Set G))
        hR.symm x) = y := by
    apply Subtype.ext
    change alpha ((MulEquiv.cast
      (M := fun R : Subgroup G ↦ Subgroup.normalizer (R : Set G))
      hR.symm x : Subgroup.normalizer
        (W.subgroup.comap alpha.toMonoidHom : Set G)) : G) = (y : G)
    exact (congrArg alpha (normalizerCast_coe hR.symm x)).trans hxy.symm
  simpa only [heq] using hvalue'

/-- Literal conjugation in the factor inertia preserves the inflated
local character. The normalizer elements are identified by their actual
ambient inclusions. -/
theorem inflated_localCharacter_invariant
    (a : Inertia G field action W factor)
    (x y : Subgroup.normalizer (W.subgroup : Set G))
    (hxy : baseEmbedding G field y.1 =
      a.1 * baseEmbedding G field x.1 * a.1⁻¹) :
    W.localCharacter (QuotientGroup.mk y) =
      W.localCharacter (QuotientGroup.mk x) := by
  apply inflated_localCharacter_fixed_of_isomorphic G W (action.hom a.1)
    (inertia_supplies_isomorphic G field action W factor a) x y
  apply baseEmbedding_injective G field
  exact hxy.trans (baseEmbedding_natural G field action a.1 x.1).symm

/-- The injective base inclusion reflects the radical-normalizer condition. -/
theorem base_mem_normalizer_iff (g : G) :
    baseEmbedding G field g ∈
      Subgroup.normalizer (embeddedRadical G field W : Set (Ambient field)) ↔
        g ∈ Subgroup.normalizer (W.subgroup : Set G) := by
  change g ∈ (Subgroup.normalizer
    (W.subgroup.map (baseEmbedding G field))).comap (baseEmbedding G field) ↔ _
  rw [Subgroup.comap_normalizer_eq_of_le_range
    (W.subgroup.map_le_range (baseEmbedding G field)),
    Subgroup.comap_map_eq_self_of_injective (baseEmbedding_injective G field)]

def normalizerToBase : Subgroup.normalizer (W.subgroup : Set G) →*
    BaseInInertia G field action W factor where
  toFun x := ⟨normalizerInclusion G field action W factor base_le_factor x,
    ⟨x.1, rfl⟩⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' x y := by apply Subtype.ext; exact map_mul _ _ _

theorem normalizerToBase_surjective : Function.Surjective
    (normalizerToBase G field action W factor base_le_factor) := by
  intro b
  obtain ⟨g, hg⟩ := b.property
  have hgn : g ∈ Subgroup.normalizer (W.subgroup : Set G) :=
    (base_mem_normalizer_iff G field W g).mp (hg.symm ▸ b.1.property.1.2)
  refine ⟨⟨g, hgn⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hg

def normalizerToLocal : Subgroup.normalizer (W.subgroup : Set G) →*
    LocalBase G field action W factor where
  toFun x :=
    ⟨QuotientGroup.mk' (RadicalInInertia G field action W factor)
      (normalizerInclusion G field action W factor base_le_factor x),
      ⟨normalizerInclusion G field action W factor base_le_factor x,
        ⟨x.1, rfl⟩, rfl⟩⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by apply Subtype.ext; simp

theorem normalizerToLocal_surjective : Function.Surjective
    (normalizerToLocal G field action W factor base_le_factor) := by
  intro z
  obtain ⟨b, hb, hbz⟩ := z.property
  obtain ⟨x, hx⟩ := normalizerToBase_surjective G field action W factor
    base_le_factor ⟨b, hb⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  change QuotientGroup.mk' (RadicalInInertia G field action W factor)
    (normalizerInclusion G field action W factor base_le_factor x) = z.1
  rw [show normalizerInclusion G field action W factor base_le_factor x = b from
    congrArg Subtype.val hx]
  exact hbz

theorem normalizerToLocal_ker :
    W.subgroup.subgroupOf (Subgroup.normalizer (W.subgroup : Set G)) =
      (normalizerToLocal G field action W factor base_le_factor).ker := by
  ext x
  constructor
  · intro hx
    change normalizerToLocal G field action W factor base_le_factor x = 1
    apply Subtype.ext
    apply (QuotientGroup.eq_one_iff
      (normalizerInclusion G field action W factor base_le_factor x)).mpr
    exact ⟨x.1, hx, rfl⟩
  · intro hx
    change normalizerToLocal G field action W factor base_le_factor x = 1 at hx
    have hq := congrArg Subtype.val hx
    have hm := (QuotientGroup.eq_one_iff
      (normalizerInclusion G field action W factor base_le_factor x)).mp hq
    obtain ⟨r, hr, hrx⟩ := hm
    have heq : r = (x : G) := baseEmbedding_injective G field hrx
    change (x : G) ∈ W.subgroup
    exact heq ▸ hr

/-- The canonical normalizer-quotient comparison comes from the actual
surjection just constructed, with its exact radical kernel. -/
def localEquiv : NormalizerQuotient W.subgroup ≃*
    LocalBase G field action W factor :=
  (QuotientGroup.quotientMulEquivOfEq
    (normalizerToLocal_ker G field action W factor base_le_factor)).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (normalizerToLocal G field action W factor base_le_factor)
      (normalizerToLocal_surjective G field action W factor base_le_factor))

@[simp]
theorem localEquiv_mk (x : Subgroup.normalizer (W.subgroup : Set G)) :
    localEquiv G field action W factor base_le_factor (QuotientGroup.mk x) =
      normalizerToLocal G field action W factor base_le_factor x := rfl

def localCharacter : Irr K (LocalBase G field action W factor) :=
  OrdinaryIrreducibleCharacter.mapEquiv W.localCharacter
    (localEquiv G field action W factor base_le_factor)

@[simp]
theorem localCharacter_on_normalizer
    (x : Subgroup.normalizer (W.subgroup : Set G)) :
    localCharacter G field action W factor base_le_factor
        (normalizerToLocal G field action W factor base_le_factor x) =
      W.localCharacter (QuotientGroup.mk x) := by
  change W.localCharacter ((localEquiv G field action W factor base_le_factor).symm
    (normalizerToLocal G field action W factor base_le_factor x)) = _
  rw [← localEquiv_mk, MulEquiv.symm_apply_apply]

/-- Invariance of the actual character in I/R is derived from raw
fixedness, exact normalizer inclusions and the literal quotient map. -/
theorem localCharacter_fixed
    (d : Inertia G field action W factor ⧸ RadicalInInertia G field action W factor)
    (z : LocalBase G field action W factor) :
    localCharacter G field action W factor base_le_factor (MulAut.conjNormal d z) =
      localCharacter G field action W factor base_le_factor z := by
  refine QuotientGroup.induction_on d ?_
  intro a
  obtain ⟨x, rfl⟩ := normalizerToLocal_surjective G field action W factor
    base_le_factor z
  let y : BaseInInertia G field action W factor := MulAut.conjNormal a
    (normalizerToBase G field action W factor base_le_factor x)
  obtain ⟨t, ht⟩ := normalizerToBase_surjective G field action W factor
    base_le_factor y
  have htI : normalizerInclusion G field action W factor base_le_factor t =
      a * normalizerInclusion G field action W factor base_le_factor x * a⁻¹ :=
    congrArg Subtype.val ht
  have htQ : normalizerToLocal G field action W factor base_le_factor t =
      MulAut.conjNormal (QuotientGroup.mk a)
        (normalizerToLocal G field action W factor base_le_factor x) := by
    apply Subtype.ext
    change QuotientGroup.mk' (RadicalInInertia G field action W factor)
      (normalizerInclusion G field action W factor base_le_factor t) = _
    rw [htI, map_mul, map_mul, map_inv]
    rfl
  rw [← htQ, localCharacter_on_normalizer, localCharacter_on_normalizer]
  apply inflated_localCharacter_invariant G field action W factor a x t
  exact congrArg Subtype.val htI

end ModularRep.PaperProofs.TypeBLocalOrdinaryGeometrySplitting


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
