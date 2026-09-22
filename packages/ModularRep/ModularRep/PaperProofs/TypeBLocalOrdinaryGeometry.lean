import ModularRep.PaperProofs.TypeBCriterionHypotheses
import ModularRep.PaperProofs.TypeBCyclicExtensionSource
import ModularRep.PaperProofs.TypeBAutomorphismSource

/-!
# Actual local geometry for the Type B ordinary extensions

The subgroups are the criterion's actual raw normalizer inertias inside
`M semidirect E`.  The natural action fixes the inclusion of `G`, and the
local ordinary character is the quotient character of the supplied raw
weight. All geometric statements here are kernel deductions; no local
extension or factorization is a premise.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBLocalOrdinaryGeometry

open ModularRep OrdinaryIrreducibleCharacter
open TypeBCriterionHypotheses CyclicOuterLemma37Concrete

variable {ell : ℕ} {K M E : Type}
variable [Field K] [CharZero K] [IsAlgClosed K]
variable [Group M] [Finite M] [Group E] [Finite E]
variable (G : Subgroup M) [G.Normal] (field : E →* MulAut M)
variable (action : NaturalAction G field)

local instance : Fintype G := Fintype.ofFinite _

theorem baseEmbedding_injective : Function.Injective (baseEmbedding G field) :=
  SemidirectProduct.inl_injective.comp Subtype.val_injective

/-- The given natural action agrees with inner conjugation on the fixed
embedded base group. -/
theorem naturalAction_base (g : G) :
    action.hom (baseEmbedding G field g) = MulAut.conj g := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  rw [action.value]
  simp [baseEmbedding, MulAut.conj_apply]

/-- The complete conjugation square for the actual inclusion. -/
theorem baseEmbedding_natural (a : Ambient field) (g : G) :
    baseEmbedding G field (action.hom a g) =
      a * baseEmbedding G field g * a⁻¹ := by
  apply SemidirectProduct.ext
  · change (action.hom a g : M) = _
    rw [action.value]
    simp [baseEmbedding, mul_assoc]
  · simp [baseEmbedding]

include action in
/-- Its image is therefore a normal subgroup of the actual ambient group. -/
theorem embeddedG_normal : (embeddedG G field).Normal where
  conj_mem _ hx a := by
    obtain ⟨g, rfl⟩ := hx
    exact ⟨action.hom a g, baseEmbedding_natural G field action a g⟩

theorem embeddedG_le_embeddedM : embeddedG G field ≤ embeddedM field := by
  rintro _ ⟨g, rfl⟩
  exact ⟨g.1, rfl⟩

theorem embeddedG_le_baseFieldGroup : embeddedG G field ≤ baseFieldGroup G field :=
  le_sup_left

variable (W : CharacterWeight ell K G)

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

-- One fixed ambient factor; the applications are exactly embedded M and
-- embedded G E. The containment is proved for both above.
variable (factor : Subgroup (Ambient field))
variable (base_le_factor : embeddedG G field ≤ factor)

abbrev Inertia := rawNormalizerInertia G field action W ⊓ factor

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

instance radicalInInertia_normal :
    ((embeddedRadical G field W).subgroupOf
      (Inertia G field action W factor)).Normal := by
  apply Subgroup.normal_subgroupOf_of_le_normalizer
  exact inf_le_left.trans inf_le_right

abbrev BaseInInertia : Subgroup (Inertia G field action W factor) :=
  (embeddedG G field).subgroupOf (Inertia G field action W factor)

instance baseInInertia_normal : (BaseInInertia G field action W factor).Normal := by
  letI := embeddedG_normal G field action
  change ((embeddedG G field).subgroupOf _).Normal
  infer_instance

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

/-- Normalizing the embedded radical is equivalent to normalizing the
original radical for an element of the fixed base group. -/
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

abbrev RadicalInInertia : Subgroup (Inertia G field action W factor) :=
  (embeddedRadical G field W).subgroupOf (Inertia G field action W factor)

theorem radical_le_base : RadicalInInertia G field action W factor ≤
    BaseInInertia G field action W factor := by
  intro x hx
  obtain ⟨r, _hr, hrx⟩ := hx
  exact ⟨r, hrx⟩

/-- The actual local normal subgroup after quotienting the chosen factor
inertia by R. -/
abbrev LocalBase := (BaseInInertia G field action W factor).map
  (QuotientGroup.mk' (RadicalInInertia G field action W factor))

instance localBase_normal : (LocalBase G field action W factor).Normal :=
  (baseInInertia_normal G field action W factor).map _
    (QuotientGroup.mk'_surjective _)

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

include base_le_factor in
/-- Once an actual cyclic quotient embedding is supplied, the checked
quotient-tower theorem constructs the ordinary character required by the
criterion. All radical, normalizer and character-action data are computed
above; there is no extension premise. -/
theorem localOrdinaryExtension_of_cyclic_embedding
    {C : Type} [Group C] [IsCyclic C]
    (principle : Representation.CyclicExtensionPrinciple.{0, 0, 0} K)
    (embedding : (Inertia G field action W factor ⧸
      BaseInInertia G field action W factor) →* C)
    (injective : Function.Injective embedding) :
    Nonempty (LocalOrdinaryExtension G field W
      (Inertia G field action W factor)) := by
  obtain ⟨thetaHat, hthetaHat⟩ :=
    TypeBCyclicExtensionSource.ordinary_extension_over_quotient_tower principle
      (RadicalInInertia G field action W factor)
      (BaseInInertia G field action W factor)
      (radical_le_base G field action W factor) embedding injective
      (localCharacter G field action W factor base_le_factor)
      (localCharacter_fixed G field action W factor base_le_factor)
  refine ⟨{
    radical_le := radical_le_inertia G field action W factor base_le_factor
    radical_normal := radicalInInertia_normal G field action W factor
    normalizerInclusion := normalizerInclusion G field action W factor base_le_factor
    normalizerInclusion_value := normalizerInclusion_value G field action W factor base_le_factor
    character := thetaHat
    restriction := ?_ }⟩
  intro x
  exact (hthetaHat (normalizerToLocal G field action W factor base_le_factor x)).trans
    (localCharacter_on_normalizer G field action W factor base_le_factor x)

/-! The following projections are independent of weights. -/

theorem embeddedM_right_eq_one (x : embeddedM field) : x.1.right = 1 := by
  obtain ⟨m, hm⟩ := x.property
  rw [← hm]
  rfl

/-- Left coordinate is a homomorphism on the literal embedded M factor. -/
def embeddedMProjection : embeddedM field →* M where
  toFun x := x.1.left
  map_one' := rfl
  map_mul' x y := by
    change x.1.left * field x.1.right y.1.left = x.1.left * y.1.left
    rw [embeddedM_right_eq_one field x, map_one, MulAut.one_apply]

def mFactorProjection : embeddedM field →* M ⧸ G :=
  (QuotientGroup.mk' G).comp (embeddedMProjection field)

theorem mFactorProjection_ker : (mFactorProjection G field).ker =
    (embeddedG G field).subgroupOf (embeddedM field) := by
  ext x
  change ((x.1.left : M ⧸ G) = 1) ↔ x.1 ∈ embeddedG G field
  rw [QuotientGroup.eq_one_iff]
  constructor
  · intro hx
    refine ⟨⟨x.1.left, hx⟩, ?_⟩
    apply SemidirectProduct.ext
    · rfl
    · exact (embeddedM_right_eq_one field x).symm
  · rintro ⟨g, hg⟩
    have hleft : g.1 = x.1.left := congrArg SemidirectProduct.left hg
    exact hleft ▸ g.property

include action in
theorem field_preserves_base (e : E) (g : G) : field e g.1 ∈ G := by
  have hvalue : (action.hom (SemidirectProduct.inr e) g : M) = field e g.1 := by
    simpa using action.value (SemidirectProduct.inr e) g
  exact hvalue ▸ (action.hom (SemidirectProduct.inr e) g).property

def leftBaseSubgroup : Subgroup (Ambient field) where
  carrier := {a | a.left ∈ G}
  one_mem' := G.one_mem
  mul_mem' {a b} ha hb := G.mul_mem ha (field_preserves_base G field action a.right ⟨b.left, hb⟩)
  inv_mem' {a} ha :=
    field_preserves_base G field action a.right⁻¹ ⟨a.left⁻¹, G.inv_mem ha⟩

/-- Membership of the actual subgroup G E is exactly the condition that
the left coordinate belongs to G. -/
theorem baseFieldGroup_eq_leftBase : baseFieldGroup G field =
    leftBaseSubgroup G field action := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rintro _ ⟨g, rfl⟩
      exact g.property
    · rintro _ ⟨e, rfl⟩
      exact G.one_mem
  · intro a ha
    have hinl : SemidirectProduct.inl a.left ∈ embeddedG G field :=
      ⟨⟨a.left, ha⟩, rfl⟩
    have hinr : SemidirectProduct.inr a.right ∈ embeddedE field := ⟨a.right, rfl⟩
    rw [← SemidirectProduct.inl_left_mul_inr_right a]
    exact (baseFieldGroup G field).mul_mem
      ((show embeddedG G field ≤ baseFieldGroup G field from le_sup_left) hinl)
      ((show embeddedE field ≤ baseFieldGroup G field from le_sup_right) hinr)

def fieldFactorProjection : baseFieldGroup G field →* E :=
  SemidirectProduct.rightHom.comp (baseFieldGroup G field).subtype

include action in
theorem fieldFactorProjection_ker : (fieldFactorProjection G field).ker =
    (embeddedG G field).subgroupOf (baseFieldGroup G field) := by
  ext x
  change x.1.right = 1 ↔ x.1 ∈ embeddedG G field
  constructor
  · intro hx
    have hleft : x.1.left ∈ G := by
      have hm := (baseFieldGroup_eq_leftBase G field action).le x.property
      exact hm
    refine ⟨⟨x.1.left, hleft⟩, ?_⟩
    apply SemidirectProduct.ext
    · rfl
    · exact hx.symm
  · rintro ⟨g, hg⟩
    exact (congrArg SemidirectProduct.right hg).symm

section GeneralQuotientEmbeddings

variable [hBaseNormal : (embeddedG G field).Normal]
variable {C : Type} [Group C]
variable (projection : factor →* C)
variable (projection_kernel : projection.ker = (embeddedG G field).subgroupOf factor)
variable (I : Subgroup (Ambient field)) (le_factor : I ≤ factor)

def restrictedFactorProjection : I →* C :=
  projection.comp (Subgroup.inclusion le_factor)

include projection_kernel in
theorem restrictedFactorProjection_ker :
    (restrictedFactorProjection field factor projection I le_factor).ker =
      (embeddedG G field).subgroupOf I := by
  ext x
  change (Subgroup.inclusion le_factor x) ∈ projection.ker ↔
    x.1 ∈ embeddedG G field
  rw [projection_kernel]
  rfl

/-- The quotient embedding is the actual quotient lift of the fixed factor
projection. It applies to arbitrary subgroups I of that factor. -/
def factorQuotientEmbedding : (I ⧸ (embeddedG G field).subgroupOf I) →* C :=
  QuotientGroup.lift ((embeddedG G field).subgroupOf I)
    (restrictedFactorProjection field factor projection I le_factor)
    (restrictedFactorProjection_ker G field factor projection projection_kernel I le_factor).symm.le

theorem factorQuotientEmbedding_injective : Function.Injective
    (factorQuotientEmbedding G field factor projection projection_kernel I le_factor) :=
  (QuotientGroup.injective_lift_iff ((embeddedG G field).subgroupOf I)
    (restrictedFactorProjection field factor projection I le_factor)
    (restrictedFactorProjection_ker G field factor projection projection_kernel I le_factor).symm.le).mpr
    (restrictedFactorProjection_ker G field factor projection projection_kernel I le_factor).symm

end GeneralQuotientEmbeddings

section ConcreteQuotientEmbeddings

variable [hBaseNormal : (embeddedG G field).Normal]

/-- Any actual subgroup of embedded M has its quotient by the embedded
base intersection embedded in the literal quotient M/G. -/
def mInertiaQuotientEmbedding (I : Subgroup (Ambient field)) (hI : I ≤ embeddedM field) :
    (I ⧸ (embeddedG G field).subgroupOf I) →* M ⧸ G :=
  factorQuotientEmbedding G field (embeddedM field) (mFactorProjection G field)
    (mFactorProjection_ker G field) I hI

theorem mInertiaQuotientEmbedding_injective
    (I : Subgroup (Ambient field)) (hI : I ≤ embeddedM field) :
    Function.Injective (mInertiaQuotientEmbedding G field I hI) :=
  factorQuotientEmbedding_injective G field (embeddedM field) (mFactorProjection G field)
    (mFactorProjection_ker G field) I hI

/-- Any actual subgroup of G E has its quotient by the embedded base
intersection embedded in the actual acting field group E. -/
def fieldInertiaQuotientEmbedding (I : Subgroup (Ambient field))
    (hI : I ≤ baseFieldGroup G field) :
    (I ⧸ (embeddedG G field).subgroupOf I) →* E :=
  factorQuotientEmbedding G field (baseFieldGroup G field) (fieldFactorProjection G field)
    (fieldFactorProjection_ker G field action) I hI

theorem fieldInertiaQuotientEmbedding_injective
    (I : Subgroup (Ambient field)) (hI : I ≤ baseFieldGroup G field) :
    Function.Injective (fieldInertiaQuotientEmbedding G field action I hI) :=
  factorQuotientEmbedding_injective G field (baseFieldGroup G field)
    (fieldFactorProjection G field) (fieldFactorProjection_ker G field action) I hI

end ConcreteQuotientEmbeddings

/-- The ordinary extension clause on the actual embedded M inertia is
deduced from cyclicity of the literal M/G quotient. -/
theorem ordinary_M
    (principle : Representation.CyclicExtensionPrinciple.{0, 0, 0} K)
    (quotient_cyclic : IsCyclic (M ⧸ G)) :
    Nonempty (LocalOrdinaryExtension G field W
      (rawNormalizerInertia G field action W ⊓ embeddedM field)) := by
  letI := embeddedG_normal G field action
  letI := quotient_cyclic
  exact localOrdinaryExtension_of_cyclic_embedding G field action W
    (embeddedM field) (embeddedG_le_embeddedM G field) principle
    (mInertiaQuotientEmbedding G field _ inf_le_right)
    (mInertiaQuotientEmbedding_injective G field _ inf_le_right)

/-- The ordinary extension clause on the actual G E inertia is deduced
from cyclicity of the actual field group. -/
theorem ordinary_GE [IsCyclic E]
    (principle : Representation.CyclicExtensionPrinciple.{0, 0, 0} K) :
    Nonempty (LocalOrdinaryExtension G field W
      (rawNormalizerInertia G field action W ⊓ baseFieldGroup G field)) := by
  letI := embeddedG_normal G field action
  exact localOrdinaryExtension_of_cyclic_embedding G field action W
    (baseFieldGroup G field) (embeddedG_le_baseFieldGroup G field) principle
    (fieldInertiaQuotientEmbedding G field action _ inf_le_right)
    (fieldInertiaQuotientEmbedding_injective G field action _ inf_le_right)

end ModularRep.PaperProofs.TypeBLocalOrdinaryGeometry


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
