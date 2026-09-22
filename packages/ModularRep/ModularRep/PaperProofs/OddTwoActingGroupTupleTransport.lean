import ModularRep.PaperProofs.OddTwoGroupEquivHolomorphCoordinates
import ModularRep.PaperProofs.OddTwoStandardBlockTripleTransport
import ModularRep.PaperProofs.OddTwoActualCentralInflationPacket

/-!
# Actual tuples under a change of acting-group presentation

The equivalence A from Gamma to the full automorphism group has value
exactly gamma. The ambient map is the literal pair (id, A). Its actual
inverse/op actions give the global and OWN raw-pair stabilizer images.
The base and own-normalizer coordinates are identities. The two tuples
therefore use the SAME iota, psi, W and R, and their root/value squares
are K consequences of the displayed identity maps.

No image, containment, root square, value equation, relation or covariance
is a source premise. A and its value equation are ordinary parameters of
this K adapter; the principal family supplies the already computed
familyAutEquiv. Only the last iff uses the existing universal authentic
standard-definition transport source, after constructing the actual packet.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoActingGroupTupleTransport

open Formalisation
open ModularRep
open ModularRep.CharacterWeight
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.OddTwoActualStabilizerTriple
open ModularRep.PaperProofs.OddTwoGroupEquivHolomorphCoordinates
open ModularRep.PaperProofs.OddTwoStandardBlockTripleTransport
open ModularRep.PaperProofs.OddTwoActualCentralInflationPacket
open ModularRep.PaperProofs.OddTwoCentralTwoRelationInflation

universe u

private theorem image_of_membership {G H : Type u} [Group G] [Group H]
    (e : G ≃* H) (B : Subgroup G) (C : Subgroup H)
    (hmem : ∀ x : G, e x ∈ C ↔ x ∈ B) :
    B.map e.toMonoidHom = C := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hmem x).mpr hx
  · intro hy
    obtain ⟨x, rfl⟩ := e.surjective y
    exact ⟨x, (hmem x).mp hy, rfl⟩

section Groups

variable {G Gamma : Type u} [Group G] [Group Gamma]
variable (gamma : Gamma →* MulAut G) (A : Gamma ≃* MulAut G)
variable (A_eq : ∀ a, A a = gamma a)

/-- The actual ambient map keeps the base coordinate and changes only
the presentation of the SAME automorphism. -/
def ambientEquiv : G ⋊[gamma] Gamma ≃* Holomorph G :=
  SemidirectProduct.congr (MulEquiv.refl G) A (fun a => by
    ext x
    exact congrArg (fun b : MulAut G => b x) (A_eq a).symm)

@[simp] theorem ambientEquiv_left (d : G ⋊[gamma] Gamma) :
    (ambientEquiv gamma A A_eq d).left = d.left := rfl

@[simp] theorem ambientEquiv_right (d : G ⋊[gamma] Gamma) :
    (ambientEquiv gamma A A_eq d).right = A d.right := rfl

@[simp] theorem ambientEquiv_inl (g : G) :
    ambientEquiv gamma A A_eq (SemidirectProduct.inl g) =
      SemidirectProduct.inl g := by
  apply SemidirectProduct.ext
  · rfl
  · exact map_one A

@[simp] theorem ambientEquiv_inr (a : Gamma) :
    ambientEquiv gamma A A_eq (SemidirectProduct.inr a) =
      SemidirectProduct.inr (A a) := by
  apply SemidirectProduct.ext <;> rfl

include A_eq in
/-- The exact inverse/op homomorphisms agree in the two presentations. -/
theorem inverseOpHom_square (a : Gamma) :
    inverseOpHom gamma a = inverseOpHom (MonoidHom.id (MulAut G)) (A a) := by
  change MulOpposite.op (gamma a⁻¹) = MulOpposite.op (A a)⁻¹
  rw [← A_eq a⁻¹, map_inv]

/-- Natural conjugation on the actual base is unchanged. -/
theorem ambient_automorphism_square (d : G ⋊[gamma] Gamma) :
    semidirectToMulAut (MonoidHom.id (MulAut G)) (ambientEquiv gamma A A_eq d) =
      semidirectToMulAut gamma d := by
  ext x
  change d.left * A d.right x * d.left⁻¹ =
    d.left * gamma d.right x * d.left⁻¹
  rw [A_eq]

end Groups

section ActualActions

variable {p : ℕ} {k K G Gamma : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Group Gamma] [Finite Gamma]

local instance finitePresentationAut : Finite (MulAut G) :=
  Finite.of_injective (fun a : MulAut G => (a : G → G)) DFunLike.coe_injective

variable (iota : PrimeRegularRootEmbedding p k K G)
variable (gamma : Gamma →* MulAut G) (A : Gamma ≃* MulAut G)
variable (A_eq : ∀ a, A a = gamma a)

/-- The actual Brauer actions agree, retaining both inverse/op factors. -/
theorem brauer_action_agrees (d : G ⋊[gamma] Gamma) (psi : IBr iota) :
    letI := actualBrauerAction iota gamma
    letI := actualBrauerAction iota (MonoidHom.id (MulAut G))
    d • psi = ambientEquiv gamma A A_eq d • psi := by
  letI := actualBrauerAction iota gamma
  letI := actualBrauerAction iota (MonoidHom.id (MulAut G))
  change MulOpposite.op (MulAut.conj d.left⁻¹) •
      (inverseOpHom gamma d.right • psi) =
    MulOpposite.op (MulAut.conj d.left⁻¹) •
      (inverseOpHom (MonoidHom.id (MulAut G)) (A d.right) • psi)
  rw [inverseOpHom_square gamma A A_eq]

/-- The SAME own raw class has the same action in both presentations. -/
theorem raw_action_agrees (d : G ⋊[gamma] Gamma)
    (r : RawWeightClass (p := p) (K := K) (H := G)) :
    letI := canonicalRawSemidirectAction (p := p) (K := K) gamma
    letI := canonicalRawSemidirectAction (p := p) (K := K) (MonoidHom.id (MulAut G))
    d • r = ambientEquiv gamma A A_eq d • r := by
  letI := canonicalRawSemidirectAction (p := p) (K := K) gamma
  letI := canonicalRawSemidirectAction (p := p) (K := K) (MonoidHom.id (MulAut G))
  change MulOpposite.op (MulAut.conj d.left⁻¹) •
      (inverseOpHom gamma d.right • r) =
    MulOpposite.op (MulAut.conj d.left⁻¹) •
      (inverseOpHom (MonoidHom.id (MulAut G)) (A d.right) • r)
  rw [inverseOpHom_square gamma A A_eq]

variable (psi : IBr iota) (W : CharacterWeight p K G)

theorem global_membership_iff (d : G ⋊[gamma] Gamma) :
    ambientEquiv gamma A A_eq d ∈
        globalStabilizer iota (MonoidHom.id (MulAut G)) psi ↔
      d ∈ globalStabilizer iota gamma psi := by
  letI := actualBrauerAction iota gamma
  letI := actualBrauerAction iota (MonoidHom.id (MulAut G))
  change ambientEquiv gamma A A_eq d • psi = psi ↔ d • psi = psi
  rw [← brauer_action_agrees iota gamma A A_eq d psi]

theorem raw_membership_iff (d : G ⋊[gamma] Gamma) :
    ambientEquiv gamma A A_eq d ∈ rawStabilizer (MonoidHom.id (MulAut G)) W ↔
      d ∈ rawStabilizer gamma W := by
  letI := canonicalRawSemidirectAction (p := p) (K := K) gamma
  letI := canonicalRawSemidirectAction (p := p) (K := K) (MonoidHom.id (MulAut G))
  change ambientEquiv gamma A A_eq d •
      (Quotient.mk'' W : RawWeightClass (p := p) (K := K) (H := G)) = Quotient.mk'' W ↔
    d • (Quotient.mk'' W : RawWeightClass (p := p) (K := K) (H := G)) = Quotient.mk'' W
  rw [← raw_action_agrees gamma A A_eq d (Quotient.mk'' W)]

theorem globalStabilizer_image :
    (globalStabilizer iota gamma psi).map (ambientEquiv gamma A A_eq).toMonoidHom =
      globalStabilizer iota (MonoidHom.id (MulAut G)) psi :=
  image_of_membership _ _ _ (global_membership_iff iota gamma A A_eq psi)

theorem rawStabilizer_image :
    (rawStabilizer gamma W).map (ambientEquiv gamma A A_eq).toMonoidHom =
      rawStabilizer (MonoidHom.id (MulAut G)) W :=
  image_of_membership _ _ _ (raw_membership_iff gamma A A_eq W)

/-- Restrict the computed whole map to the actual global stabilizer. -/
def globalEquiv : globalStabilizer iota gamma psi ≃*
    globalStabilizer iota (MonoidHom.id (MulAut G)) psi :=
  ((ambientEquiv gamma A A_eq).subgroupMap (globalStabilizer iota gamma psi)).trans
    (MulEquiv.subgroupCongr (globalStabilizer_image iota gamma A A_eq psi))

@[simp] theorem globalEquiv_ambient (d : globalStabilizer iota gamma psi) :
    (globalEquiv iota gamma A A_eq psi d : Holomorph G) =
      ambientEquiv gamma A A_eq (d : G ⋊[gamma] Gamma) := rfl

include A A_eq in
/-- Neither of the two full raw-containment statements is assumed. -/
theorem fullRawContainment_iff :
    (rawStabilizer gamma W ≤ globalStabilizer iota gamma psi) ↔
      (rawStabilizer (MonoidHom.id (MulAut G)) W ≤
        globalStabilizer iota (MonoidHom.id (MulAut G)) psi) := by
  constructor
  · intro contained y hy
    obtain ⟨d, rfl⟩ := (ambientEquiv gamma A A_eq).surjective y
    exact (global_membership_iff iota gamma A A_eq psi d).mpr
      (contained ((raw_membership_iff gamma A A_eq W d).mp hy))
  · intro contained d hd
    exact (global_membership_iff iota gamma A A_eq psi d).mp
      (contained ((raw_membership_iff gamma A A_eq W d).mpr hd))

theorem globalEquiv_mem_base_iff (d : globalStabilizer iota gamma psi) :
    globalEquiv iota gamma A A_eq psi d ∈
        baseSubgroup iota (MonoidHom.id (MulAut G)) psi ↔
      d ∈ baseSubgroup iota gamma psi := by
  change A d.1.right = 1 ↔ d.1.right = 1
  constructor
  · intro h
    exact A.injective (h.trans (map_one A).symm)
  · intro h
    rw [h, map_one]

theorem globalEquiv_map_base :
    (baseSubgroup iota gamma psi).map (globalEquiv iota gamma A A_eq psi).toMonoidHom =
      baseSubgroup iota (MonoidHom.id (MulAut G)) psi :=
  image_of_membership _ _ _ (globalEquiv_mem_base_iff iota gamma A A_eq psi)

theorem globalEquiv_mem_local_iff (d : globalStabilizer iota gamma psi) :
    globalEquiv iota gamma A A_eq psi d ∈
        localSubgroup iota (MonoidHom.id (MulAut G)) psi W ↔
      d ∈ localSubgroup iota gamma psi W :=
  raw_membership_iff gamma A A_eq W d.1

theorem globalEquiv_map_local :
    (localSubgroup iota gamma psi W).map
        (globalEquiv iota gamma A A_eq psi).toMonoidHom =
      localSubgroup iota (MonoidHom.id (MulAut G)) psi W :=
  image_of_membership _ _ _ (globalEquiv_mem_local_iff iota gamma A A_eq psi W)

/-- The canonical base restriction is still the right-projection kernel. -/
def baseKernelEquiv : baseSubgroup iota gamma psi ≃*
    baseSubgroup iota (MonoidHom.id (MulAut G)) psi :=
  ((globalEquiv iota gamma A A_eq psi).subgroupMap (baseSubgroup iota gamma psi)).trans
    (MulEquiv.subgroupCongr (globalEquiv_map_base iota gamma A A_eq psi))

@[simp] theorem baseKernelEquiv_ambient (x : baseSubgroup iota gamma psi) :
    (baseKernelEquiv iota gamma A A_eq psi x :
      globalStabilizer iota (MonoidHom.id (MulAut G)) psi) =
    globalEquiv iota gamma A A_eq psi (x : globalStabilizer iota gamma psi) := rfl

/-- In the original base coordinates this map is literally the identity. -/
theorem baseKernelEquiv_base_square (x : G) :
    baseKernelEquiv iota gamma A A_eq psi
        (OddTwoActualStabilizerTriple.baseEquiv iota gamma psi x) =
      OddTwoActualStabilizerTriple.baseEquiv iota (MonoidHom.id (MulAut G)) psi x := by
  apply Subtype.ext
  apply Subtype.ext
  change ambientEquiv gamma A A_eq
      (OddTwoActualStabilizerTriple.baseEquiv iota gamma psi x).1.1 =
    (OddTwoActualStabilizerTriple.baseEquiv iota (MonoidHom.id (MulAut G)) psi x).1.1
  rw [OddTwoActualStabilizerTriple.baseEquiv_ambient,
    OddTwoActualStabilizerTriple.baseEquiv_ambient, ambientEquiv_inl]

/-- The own local subgroup is the actual raw/global intersection. -/
def localEquiv : localSubgroup iota gamma psi W ≃*
    localSubgroup iota (MonoidHom.id (MulAut G)) psi W :=
  ((globalEquiv iota gamma A A_eq psi).subgroupMap
    (localSubgroup iota gamma psi W)).trans
      (MulEquiv.subgroupCongr (globalEquiv_map_local iota gamma A A_eq psi W))

@[simp] theorem localEquiv_ambient (x : localSubgroup iota gamma psi W) :
    (localEquiv iota gamma A A_eq psi W x :
      globalStabilizer iota (MonoidHom.id (MulAut G)) psi) =
    globalEquiv iota gamma A A_eq psi (x : globalStabilizer iota gamma psi) := rfl

/-- The displayed intersection map keeps the SAME own normalizer element. -/
def displayedIntersectionEquiv :
    ↥(baseSubgroup iota gamma psi ⊓ localSubgroup iota gamma psi W) ≃*
      ↥(baseSubgroup iota (MonoidHom.id (MulAut G)) psi ⊓
        localSubgroup iota (MonoidHom.id (MulAut G)) psi W) :=
  (normalizerEquivIntersection iota gamma psi W).symm.trans
    (normalizerEquivIntersection iota (MonoidHom.id (MulAut G)) psi W)

theorem displayedIntersectionEquiv_normalizer_square
    (x : Subgroup.normalizer (W.subgroup : Set G)) :
    displayedIntersectionEquiv iota gamma psi W
        (normalizerEquivIntersection iota gamma psi W x) =
      normalizerEquivIntersection iota (MonoidHom.id (MulAut G)) psi W x := by
  change normalizerEquivIntersection iota (MonoidHom.id (MulAut G)) psi W
      ((normalizerEquivIntersection iota gamma psi W).symm
        (normalizerEquivIntersection iota gamma psi W x)) = _
  exact congrArg (normalizerEquivIntersection iota (MonoidHom.id (MulAut G)) psi W)
    ((normalizerEquivIntersection iota gamma psi W).symm_apply_apply x)

theorem displayedIntersectionEquiv_ambient
    (x : ↥(baseSubgroup iota gamma psi ⊓ localSubgroup iota gamma psi W)) :
    (displayedIntersectionEquiv iota gamma psi W x :
      globalStabilizer iota (MonoidHom.id (MulAut G)) psi) =
    globalEquiv iota gamma A A_eq psi (x : globalStabilizer iota gamma psi) := by
  obtain ⟨h, rfl⟩ := (normalizerEquivIntersection iota gamma psi W).surjective x
  rw [displayedIntersectionEquiv_normalizer_square]
  apply Subtype.ext
  change (normalizerEquivIntersection iota (MonoidHom.id (MulAut G)) psi W h).1.1 =
    ambientEquiv gamma A A_eq (normalizerEquivIntersection iota gamma psi W h).1.1
  rw [normalizerEquivIntersection_ambient, normalizerEquivIntersection_ambient,
    ambientEquiv_inl]

/-- Exact group coordinates on the same own-character tuples. Explicit
binders keep the actual tuple parameters even when a group projection
definitionally forgets the roots or character. -/
def groupCoordinates
    (iota : PrimeRegularRootEmbedding p k K G)
    (gamma : Gamma →* MulAut G) (A : Gamma ≃* MulAut G)
    (A_eq : ∀ a, A a = gamma a) (psi : IBr iota) (W : CharacterWeight p K G)
    (R : OwnNormalizerReduction (k := k) W) :
    GroupCoordinates (arguments iota gamma psi W R)
      (arguments iota (MonoidHom.id (MulAut G)) psi W R) := by
  exact {
    ambient := globalEquiv iota gamma A A_eq psi
    map_base := globalEquiv_map_base iota gamma A A_eq psi
    map_local := globalEquiv_map_local iota gamma A A_eq psi W }

/-- The actual same roots and characters supply all four tuple fields.
There is no horizontal root or character-value premise. -/
def tupleIsomorphism
    (iota : PrimeRegularRootEmbedding p k K G)
    (gamma : Gamma →* MulAut G) (A : Gamma ≃* MulAut G)
    (A_eq : ∀ a, A a = gamma a) (psi : IBr iota) (W : CharacterWeight p K G)
    (R : OwnNormalizerReduction (k := k) W) :
    TupleIsomorphism (arguments iota gamma psi W R)
      (arguments iota (MonoidHom.id (MulAut G)) psi W R) :=
  TupleIsomorphism.ofDisplayed
    (groupCoordinates iota gamma A A_eq psi W R)
    (baseKernelEquiv iota gamma A A_eq psi)
    (displayedIntersectionEquiv iota gamma psi W)
    (baseKernelEquiv_ambient iota gamma A A_eq psi)
    (displayedIntersectionEquiv_ambient iota gamma A A_eq psi W)
    (rootCompatibleAlong_transport iota iota (MonoidHom.id G)
      (OddTwoActualStabilizerTriple.baseEquiv iota gamma psi)
      (OddTwoActualStabilizerTriple.baseEquiv iota (MonoidHom.id (MulAut G)) psi)
      (baseKernelEquiv iota gamma A A_eq psi).toMonoidHom
      (baseKernelEquiv_base_square iota gamma A A_eq psi) (by intro V x z; rfl))
    (rootCompatibleAlong_transport (ownReductionRoot (k := k) W R)
      (ownReductionRoot (k := k) W R)
      (MonoidHom.id (Subgroup.normalizer (W.subgroup : Set G)))
      (normalizerEquivIntersection iota gamma psi W)
      (normalizerEquivIntersection iota (MonoidHom.id (MulAut G)) psi W)
      (displayedIntersectionEquiv iota gamma psi W).toMonoidHom
      (displayedIntersectionEquiv_normalizer_square iota gamma psi W)
      (by intro V x z; rfl))
    (values_transport iota iota (MonoidHom.id G)
      (OddTwoActualStabilizerTriple.baseEquiv iota gamma psi)
      (OddTwoActualStabilizerTriple.baseEquiv iota (MonoidHom.id (MulAut G)) psi)
      (baseKernelEquiv iota gamma A A_eq psi).toMonoidHom
      (baseKernelEquiv_base_square iota gamma A A_eq psi) psi psi (by intro x; rfl))
    (values_transport (ownReductionRoot (k := k) W R) (ownReductionRoot (k := k) W R)
      (MonoidHom.id (Subgroup.normalizer (W.subgroup : Set G)))
      (normalizerEquivIntersection iota gamma psi W)
      (normalizerEquivIntersection iota (MonoidHom.id (MulAut G)) psi W)
      (displayedIntersectionEquiv iota gamma psi W).toMonoidHom
      (displayedIntersectionEquiv_normalizer_square iota gamma psi W)
      (ownReductionBrauer (k := k) W R) (ownReductionBrauer (k := k) W R)
      (by intro x; rfl))

/-- Only the existing universal standard interpretation is used, after
computing the tuple packet. This iff asserts neither relation. -/
theorem blockIsomorphic_iff
    (iota : PrimeRegularRootEmbedding p k K G)
    (gamma : Gamma →* MulAut G) (A : Gamma ≃* MulAut G)
    (A_eq : ∀ a, A a = gamma a) (psi : IBr iota) (W : CharacterWeight p K G)
    (R : OwnNormalizerReduction (k := k) W)
    (standard : BlockTripleSourceSemantics p k K)
    (source : StandardTransportSource standard) :
    standard.blockIsomorphic (arguments iota gamma psi W R) ↔
      standard.blockIsomorphic (arguments iota (MonoidHom.id (MulAut G)) psi W R) :=
  source.relation_iff _ _ (tupleIsomorphism iota gamma A A_eq psi W R)

end ActualActions

end ModularRep.PaperProofs.OddTwoActingGroupTupleTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
