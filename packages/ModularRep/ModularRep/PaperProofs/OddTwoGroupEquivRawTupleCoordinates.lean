import ModularRep.PaperProofs.OddTwoGroupEquivHolomorphCoordinates
import ModularRep.PaperProofs.OddTwoWeightGroupEquiv
import ModularRep.PaperProofs.OddTwoStandardBlockTripleTransport

/-!
# Actual raw-weight and local tuple coordinates along a group equivalence

The whole holomorph map is the already computed pair (e, MulAut.congr e).
The raw weight is the actual image pair mapGroupEquiv W e, including its
OWN ordinary character. Its action equation proves the exact raw-stabilizer
image, hence the actual local subgroup and intersection images. The latter
restriction is the same canonical normalizer map used to transport W.

All declarations are K. No raw/local image, containment, tuple relation,
character-value compatibility, root square or FLZ interpretation is a
premise. The own reductions only select the actual tuples. The target raw
weight is the literal image pair, not an independently selected member
of its ambient class; the later selected-representative correction remains
a separate join.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoGroupEquivRawTupleCoordinates

open Formalisation
open ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.OddTwoActualStabilizerTriple
open ModularRep.PaperProofs.OddTwoGroupEquivHolomorphCoordinates
open ModularRep.PaperProofs.OddTwoStandardBlockTripleTransport

universe u

private theorem image_of_membership {G H : Type u} [Group G] [Group H]
    (e : G ≃* H) (A : Subgroup G) (B : Subgroup H)
    (hmem : ∀ x : G, e x ∈ B ↔ x ∈ A) :
    A.map e.toMonoidHom = B := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hmem x).mpr hx
  · intro hy
    obtain ⟨x, rfl⟩ := e.surjective y
    exact ⟨x, (hmem x).mp hy, rfl⟩

section RawAction

variable {p : ℕ} {K G H : Type u}
variable [Field K] [CharZero K]
variable [Group G] [Fintype G] [Group H] [Fintype H]

variable (e : G ≃* H)

/-- Both inverse twists are the existing actual raw action, in their
literal inner-then-outer coordinate order. -/
theorem raw_smul_coordinates (d : Holomorph G)
    (r : RawWeightClass (p := p) (K := K) (H := G)) :
    letI := canonicalRawSemidirectAction (p := p) (K := K) (MonoidHom.id (MulAut G))
    d • r = rightTwistIsoClass (MulAut.conj d.left⁻¹)
      (rightTwistIsoClass d.right⁻¹ r) := rfl

/-- The SAME image pair intertwines the whole actual holomorph actions. -/
theorem raw_equivariant (d : Holomorph G)
    (r : RawWeightClass (p := p) (K := K) (H := G)) :
    letI := canonicalRawSemidirectAction (p := p) (K := K) (MonoidHom.id (MulAut G))
    letI := canonicalRawSemidirectAction (p := p) (K := K) (MonoidHom.id (MulAut H))
    mapIsoClassGroupEquiv e (d • r) =
      holomorphEquiv e d • mapIsoClassGroupEquiv e r := by
  letI := canonicalRawSemidirectAction (p := p) (K := K) (MonoidHom.id (MulAut G))
  letI := canonicalRawSemidirectAction (p := p) (K := K) (MonoidHom.id (MulAut H))
  rw [raw_smul_coordinates, raw_smul_coordinates]
  rw [mapIsoClassGroupEquiv_rightTwist, mapIsoClassGroupEquiv_rightTwist,
    automorphismEquiv_inner]
  simp only [holomorphEquiv_left, holomorphEquiv_right, map_inv]

variable (W : CharacterWeight p K G)

/-- Literal raw-pair naturality, before taking ambient conjugacy classes. -/
theorem raw_equivariant_mk (d : Holomorph G) :
    letI := canonicalRawSemidirectAction (p := p) (K := K) (MonoidHom.id (MulAut G))
    letI := canonicalRawSemidirectAction (p := p) (K := K) (MonoidHom.id (MulAut H))
    mapIsoClassGroupEquiv e
        (d • (Quotient.mk'' W : RawWeightClass (p := p) (K := K) (H := G))) =
      holomorphEquiv e d •
        (Quotient.mk'' (W.mapGroupEquiv e) :
          RawWeightClass (p := p) (K := K) (H := H)) :=
  raw_equivariant e d (Quotient.mk'' W)

/-- Exact raw-stabilizer membership follows from the actual quotient
equivalence, retaining the whole own-character pair. -/
theorem raw_membership_iff (d : Holomorph G) :
    holomorphEquiv e d ∈
        rawStabilizer (MonoidHom.id (MulAut H)) (W.mapGroupEquiv e) ↔
      d ∈ rawStabilizer (MonoidHom.id (MulAut G)) W := by
  letI := canonicalRawSemidirectAction (p := p) (K := K) (MonoidHom.id (MulAut G))
  letI := canonicalRawSemidirectAction (p := p) (K := K) (MonoidHom.id (MulAut H))
  change holomorphEquiv e d • mapIsoClassGroupEquiv e (Quotient.mk'' W) =
      mapIsoClassGroupEquiv e (Quotient.mk'' W) ↔
    d • (Quotient.mk'' W : RawWeightClass (p := p) (K := K) (H := G)) = Quotient.mk'' W
  rw [← raw_equivariant e d (Quotient.mk'' W)]
  change (isoClassGroupEquiv (p := p) (K := K) e)
      (d • (Quotient.mk'' W : RawWeightClass (p := p) (K := K) (H := G))) =
    (isoClassGroupEquiv (p := p) (K := K) e) (Quotient.mk'' W) ↔ _
  exact (isoClassGroupEquiv (p := p) (K := K) e).injective.eq_iff

/-- The exact image of the full own raw-pair stabilizer is proved in K. -/
theorem rawStabilizer_image :
    (rawStabilizer (MonoidHom.id (MulAut G)) W).map
        (holomorphEquiv e).toMonoidHom =
      rawStabilizer (MonoidHom.id (MulAut H)) (W.mapGroupEquiv e) :=
  image_of_membership _ _ _ (raw_membership_iff e W)

/-- The raw-group restriction is the same computed ambient equivalence. -/
def rawStabilizerEquiv :
    rawStabilizer (MonoidHom.id (MulAut G)) W ≃*
      rawStabilizer (MonoidHom.id (MulAut H)) (W.mapGroupEquiv e) :=
  ((holomorphEquiv e).subgroupMap
    (rawStabilizer (MonoidHom.id (MulAut G)) W)).trans
      (MulEquiv.subgroupCongr (rawStabilizer_image e W))

@[simp] theorem rawStabilizerEquiv_ambient
    (d : rawStabilizer (MonoidHom.id (MulAut G)) W) :
    (rawStabilizerEquiv e W d : Holomorph H) = holomorphEquiv e (d : Holomorph G) := rfl

end RawAction

section ActualTuples

variable {p : ℕ} {k K G H : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Group H] [Fintype H]

local instance finiteTupleAut (J : Type u) [Group J] [Finite J] : Finite (MulAut J) :=
  Finite.of_injective (fun a : MulAut J => (a : J → J)) DFunLike.coe_injective

variable (iota : PrimeRegularRootEmbedding p k K G) (e : G ≃* H)
variable (psi : IBr iota) (W : CharacterWeight p K G)

local notation "iotaH" => iota.alongMulEquiv e
local notation "psiH" => IrreducibleBrauerCharacter.equivAlongMulEquiv iota e psi
local notation "WH" => W.mapGroupEquiv e

/-- The local subgroup always means the raw stabilizer's actual
intersection with the displayed global character stabilizer. -/
theorem globalEquiv_mem_local_iff
    (d : globalStabilizer iota (MonoidHom.id (MulAut G)) psi) :
    globalEquiv iota e psi d ∈ localSubgroup iotaH (MonoidHom.id (MulAut H)) psiH WH ↔
      d ∈ localSubgroup iota (MonoidHom.id (MulAut G)) psi W :=
  raw_membership_iff e W d.1

/-- No local-image equality is imported as a hypothesis. -/
theorem globalEquiv_map_local :
    (localSubgroup iota (MonoidHom.id (MulAut G)) psi W).map
        (globalEquiv iota e psi).toMonoidHom =
      localSubgroup iotaH (MonoidHom.id (MulAut H)) psiH WH :=
  image_of_membership _ _ _ (globalEquiv_mem_local_iff iota e psi W)

/-- Actual full containment is equivalent in the two carriers. Neither
containment is a premise, and no class-stabilizer surrogate is used. -/
theorem fullRawContainment_iff :
    (rawStabilizer (MonoidHom.id (MulAut G)) W ≤
      globalStabilizer iota (MonoidHom.id (MulAut G)) psi) ↔
    (rawStabilizer (MonoidHom.id (MulAut H)) WH ≤
      globalStabilizer iotaH (MonoidHom.id (MulAut H)) psiH) := by
  constructor
  · intro contained y hy
    obtain ⟨d, rfl⟩ := (holomorphEquiv e).surjective y
    exact (global_membership_iff iota e psi d).mpr
      (contained ((raw_membership_iff e W d).mp hy))
  · intro contained d hd
    exact (global_membership_iff iota e psi d).mp
      (contained ((raw_membership_iff e W d).mpr hd))

/-- Canonical restriction to the actual local subgroup. -/
def localEquiv :
    localSubgroup iota (MonoidHom.id (MulAut G)) psi W ≃*
      localSubgroup iotaH (MonoidHom.id (MulAut H)) psiH WH :=
  ((globalEquiv iota e psi).subgroupMap
    (localSubgroup iota (MonoidHom.id (MulAut G)) psi W)).trans
      (MulEquiv.subgroupCongr (globalEquiv_map_local iota e psi W))

@[simp] theorem localEquiv_ambient
    (d : localSubgroup iota (MonoidHom.id (MulAut G)) psi W) :
    (localEquiv iota e psi W d : globalStabilizer iotaH (MonoidHom.id (MulAut H)) psiH) =
      globalEquiv iota e psi (d : globalStabilizer iota (MonoidHom.id (MulAut G)) psi) := rfl

/-- The exact base/local intersection image follows from those two
already proved images and injectivity of the whole tuple map. -/
theorem globalEquiv_map_intersection :
    (baseSubgroup iota (MonoidHom.id (MulAut G)) psi ⊓
      localSubgroup iota (MonoidHom.id (MulAut G)) psi W).map
        (globalEquiv iota e psi).toMonoidHom =
      baseSubgroup iotaH (MonoidHom.id (MulAut H)) psiH ⊓
        localSubgroup iotaH (MonoidHom.id (MulAut H)) psiH WH := by
  rw [Subgroup.map_inf _ _ _ (globalEquiv iota e psi).injective,
    globalEquiv_map_base, globalEquiv_map_local]

/-- Display the intersection map through the SAME own normalizer
equivalence which defines mapGroupEquiv W e. -/
def displayedIntersectionEquiv :
    ↥(baseSubgroup iota (MonoidHom.id (MulAut G)) psi ⊓
      localSubgroup iota (MonoidHom.id (MulAut G)) psi W) ≃*
    ↥(baseSubgroup iotaH (MonoidHom.id (MulAut H)) psiH ⊓
      localSubgroup iotaH (MonoidHom.id (MulAut H)) psiH WH) :=
  ((normalizerEquivIntersection iota (MonoidHom.id (MulAut G)) psi W).symm.trans
    (ModularRep.normalizerEquiv e W.subgroup)).trans
      (normalizerEquivIntersection iotaH (MonoidHom.id (MulAut H)) psiH WH)

/-- The displayed intersection map is precisely the original normalizer
map in the two checked normalizer-to-intersection coordinates. -/
theorem displayedIntersectionEquiv_normalizer_square
    (x : Subgroup.normalizer (W.subgroup : Set G)) :
    displayedIntersectionEquiv iota e psi W
        (normalizerEquivIntersection iota (MonoidHom.id (MulAut G)) psi W x) =
      normalizerEquivIntersection iotaH (MonoidHom.id (MulAut H)) psiH WH
        (ModularRep.normalizerEquiv e W.subgroup x) := by
  change normalizerEquivIntersection iotaH (MonoidHom.id (MulAut H)) psiH WH
      (ModularRep.normalizerEquiv e W.subgroup
        ((normalizerEquivIntersection iota (MonoidHom.id (MulAut G)) psi W).symm
          (normalizerEquivIntersection iota (MonoidHom.id (MulAut G)) psi W x))) = _
  exact congrArg
    (fun y => normalizerEquivIntersection iotaH (MonoidHom.id (MulAut H)) psiH WH
      (ModularRep.normalizerEquiv e W.subgroup y))
    ((normalizerEquivIntersection iota (MonoidHom.id (MulAut G)) psi W).symm_apply_apply x)

/-- Its ambient square identifies that own-normalizer map with the
restriction of the SAME global holomorph equivalence. -/
theorem displayedIntersectionEquiv_square
    (x : ↥(baseSubgroup iota (MonoidHom.id (MulAut G)) psi ⊓
      localSubgroup iota (MonoidHom.id (MulAut G)) psi W)) :
    (displayedIntersectionEquiv iota e psi W x :
      globalStabilizer iotaH (MonoidHom.id (MulAut H)) psiH) =
      globalEquiv iota e psi (x : globalStabilizer iota (MonoidHom.id (MulAut G)) psi) := by
  obtain ⟨h, rfl⟩ :=
    (normalizerEquivIntersection iota (MonoidHom.id (MulAut G)) psi W).surjective x
  rw [displayedIntersectionEquiv_normalizer_square]
  apply Subtype.ext
  change (normalizerEquivIntersection iotaH (MonoidHom.id (MulAut H)) psiH WH
      (ModularRep.normalizerEquiv e W.subgroup h)).1.1 =
    holomorphEquiv e
      (normalizerEquivIntersection iota (MonoidHom.id (MulAut G)) psi W h).1.1
  calc
    _ = (SemidirectProduct.inl (e (h : G)) : Holomorph H) :=
      normalizerEquivIntersection_ambient iotaH (MonoidHom.id (MulAut H)) psiH WH
        (ModularRep.normalizerEquiv e W.subgroup h)
    _ = holomorphEquiv e (SemidirectProduct.inl (h : G)) :=
      (holomorphEquiv_inl e (h : G)).symm
    _ = _ := congrArg (holomorphEquiv e)
      (normalizerEquivIntersection_ambient iota (MonoidHom.id (MulAut G)) psi W h).symm

/-- Group coordinates on the ACTUAL two tuples. The arbitrary own roots
select their character domains; no compatibility is asserted from groups. -/
def groupCoordinates
    (iota : PrimeRegularRootEmbedding p k K G) (e : G ≃* H)
    (psi : IBr iota) (W : CharacterWeight p K G)
    (R : OwnNormalizerReduction (k := k) W)
    (R' : OwnNormalizerReduction (k := k) (W.mapGroupEquiv e)) :
    GroupCoordinates
      (arguments iota (MonoidHom.id (MulAut G)) psi W R)
      (arguments (iota.alongMulEquiv e) (MonoidHom.id (MulAut H))
        (IrreducibleBrauerCharacter.equivAlongMulEquiv iota e psi)
        (W.mapGroupEquiv e) R') := by
  exact {
    ambient := globalEquiv iota e psi
    map_base := globalEquiv_map_base iota e psi
    map_local := globalEquiv_map_local iota e psi W }

/-- The canonical base restriction is the already computed exact kernel map. -/
theorem groupCoordinates_baseEquiv
    (iota : PrimeRegularRootEmbedding p k K G) (e : G ≃* H)
    (psi : IBr iota) (W : CharacterWeight p K G)
    (R : OwnNormalizerReduction (k := k) W)
    (R' : OwnNormalizerReduction (k := k) (W.mapGroupEquiv e)) :
    (groupCoordinates iota e psi W R R').baseEquiv = baseKernelEquiv iota e psi :=
  GroupCoordinates.baseEquiv_eq_of_ambient (groupCoordinates iota e psi W R R')
    (baseKernelEquiv iota e psi) (baseKernelEquiv_ambient iota e psi)

/-- The canonical local restriction is the displayed local group map. -/
theorem groupCoordinates_localEquiv
    (iota : PrimeRegularRootEmbedding p k K G) (e : G ≃* H)
    (psi : IBr iota) (W : CharacterWeight p K G)
    (R : OwnNormalizerReduction (k := k) W)
    (R' : OwnNormalizerReduction (k := k) (W.mapGroupEquiv e)) :
    (groupCoordinates iota e psi W R R').localEquiv = localEquiv iota e psi W :=
  GroupCoordinates.localEquiv_eq_of_ambient (groupCoordinates iota e psi W R R')
    (localEquiv iota e psi W) (localEquiv_ambient iota e psi W)

/-- The own-character-domain restriction is the exact normalizer map.
Transport of roots and character values is a later, separate K join. -/
theorem groupCoordinates_intersectionEquiv
    (iota : PrimeRegularRootEmbedding p k K G) (e : G ≃* H)
    (psi : IBr iota) (W : CharacterWeight p K G)
    (R : OwnNormalizerReduction (k := k) W)
    (R' : OwnNormalizerReduction (k := k) (W.mapGroupEquiv e)) :
    (groupCoordinates iota e psi W R R').intersectionEquiv =
      displayedIntersectionEquiv iota e psi W :=
  GroupCoordinates.intersectionEquiv_eq_of_ambient (groupCoordinates iota e psi W R R')
    (displayedIntersectionEquiv iota e psi W)
    (displayedIntersectionEquiv_square iota e psi W)

end ActualTuples

end ModularRep.PaperProofs.OddTwoGroupEquivRawTupleCoordinates


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
