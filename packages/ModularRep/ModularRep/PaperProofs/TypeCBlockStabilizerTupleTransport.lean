import ModularRep.PaperProofs.OddTwoActingGroupTupleTransport
import ModularRep.PaperProofs.EvenFieldFLZSourceConditions
import ModularRep.PaperProofs.OddTwoSelectedWeightAutomorphismCoordinates

/-!
# Actual tuples for a block stabilizer and the full holomorph

The faithful map (id, P.gamma) need not cover the whole holomorph. It does
cover the actual stabilizer of a character in P.block: fixing that
character preserves its specified block, and the actual block-stabilizer
adapter supplies precisely the missing outer coordinate.

The local subgroup stays the raw/global intersection. Full raw containment
is compared only for an corresponding weight in the same specified block, whose block
covariance supplies the analogous restricted raw surjectivity. The tuple
then keeps exactly the same root, character and own-normalizer reduction.
No new source law or relation is assumed.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeCBlockStabilizerTupleTransport

open Formalisation ModularRep CharacterWeight
open FDRepSimpleClassKZero
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open CyclicOuterLemma37Concrete CyclicOuterLemma37LiteralLocalExtension
open CyclicOuterRawPairNormalizer
open EvenFieldFLZSourceConditions
open OddTwoActualStabilizerTriple OddTwoGroupEquivHolomorphCoordinates
open OddTwoSelectedWeightAutomorphismCoordinates
open OddTwoStandardBlockTripleTransport OddTwoActualCentralInflationPacket
open OddTwoCentralTwoRelationInflation

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

variable (P : Definition35Problem.{u})

local instance fullAutFinite : Finite (MulAut P.H) :=
  Finite.of_injective (fun a : MulAut P.H => (a : P.H → P.H)) DFunLike.coe_injective

variable (adapter : Definition35AutomorphismStabilizerAdapter P)

include adapter in
/-- Faithfulness follows from the actual adapter, not a new source fact. -/
theorem gamma_injective : Function.Injective P.gamma := by
  intro a c hac
  apply adapter.equiv.injective
  apply Subtype.ext
  rw [adapter.equiv_coe, adapter.equiv_coe]
  change MulOpposite.op (P.gamma a⁻¹) = MulOpposite.op (P.gamma c⁻¹)
  simp only [map_inv, hac]

include adapter in
/-- Surjectivity is used only for automorphisms preserving this block. -/
theorem exists_gamma_of_block_fixed (alpha : MulAut P.H)
    (hblock : MulOpposite.op alpha⁻¹ • P.block = P.block) :
    ∃ a : P.Gamma, P.gamma a = alpha := by
  let b : MulAction.stabilizer (MulAut P.H)ᵐᵒᵖ P.block :=
    ⟨MulOpposite.op alpha⁻¹, hblock⟩
  obtain ⟨a, ha⟩ := adapter.equiv.surjective b
  refine ⟨a, ?_⟩
  have hop : inverseOpHom P.gamma a = MulOpposite.op alpha⁻¹ :=
    (adapter.equiv_coe a).symm.trans (congrArg Subtype.val ha)
  have hinv := congrArg MulOpposite.unop hop
  change P.gamma a⁻¹ = alpha⁻¹ at hinv
  rw [map_inv] at hinv
  exact inv_injective hinv

/-- The actual ambient homomorphism; it is not asserted surjective. -/
def ambientMap : P.H ⋊[P.gamma] P.Gamma →* Holomorph P.H :=
  SemidirectProduct.map (MonoidHom.id P.H) P.gamma (fun _ => by ext x; rfl)

@[simp] theorem ambientMap_left (d : P.H ⋊[P.gamma] P.Gamma) :
    (ambientMap P d).left = d.left := rfl

@[simp] theorem ambientMap_right (d : P.H ⋊[P.gamma] P.Gamma) :
    (ambientMap P d).right = P.gamma d.right := rfl

@[simp] theorem ambientMap_inl (x : P.H) :
    ambientMap P (SemidirectProduct.inl x) = SemidirectProduct.inl x := by
  apply SemidirectProduct.ext
  · rfl
  · exact map_one P.gamma

@[simp] theorem ambientMap_inr (a : P.Gamma) :
    ambientMap P (SemidirectProduct.inr a) = SemidirectProduct.inr (P.gamma a) := by
  apply SemidirectProduct.ext <;> rfl

include adapter in
theorem ambientMap_injective : Function.Injective (ambientMap P) := by
  intro d c h
  apply SemidirectProduct.ext
  · exact congrArg (fun d : Holomorph P.H => d.left) h
  · exact gamma_injective P adapter (congrArg (fun d : Holomorph P.H => d.right) h)

include adapter in
/-- Every element whose right coordinate preserves the block has an actual
preimage; the left coordinate is unchanged. -/
theorem exists_ambient_preimage_of_block_fixed (d : Holomorph P.H)
    (hblock : MulOpposite.op d.right⁻¹ • P.block = P.block) :
    ∃ c : P.H ⋊[P.gamma] P.Gamma, ambientMap P c = d := by
  obtain ⟨a, ha⟩ := exists_gamma_of_block_fixed P adapter d.right hblock
  refine ⟨⟨d.left, a⟩, ?_⟩
  apply SemidirectProduct.ext
  · rfl
  · exact ha

/-- Both actual inverse/op actions agree under the faithful ambient map. -/
theorem brauer_action_agrees (d : P.H ⋊[P.gamma] P.Gamma) (psi : IBr P.iota) :
    letI := actualBrauerAction P.iota P.gamma
    letI := actualBrauerAction P.iota (MonoidHom.id (MulAut P.H))
    d • psi = ambientMap P d • psi := by
  letI := actualBrauerAction P.iota P.gamma
  letI := actualBrauerAction P.iota (MonoidHom.id (MulAut P.H))
  change MulOpposite.op (MulAut.conj d.left⁻¹) •
      (MulOpposite.op (P.gamma d.right⁻¹) • psi) =
    MulOpposite.op (MulAut.conj d.left⁻¹) •
      (MulOpposite.op (P.gamma d.right)⁻¹ • psi)
  rw [map_inv P.gamma d.right]

theorem raw_action_agrees (d : P.H ⋊[P.gamma] P.Gamma)
    (w : RawWeightClass (p := P.p) (K := P.K) (H := P.H)) :
    letI := canonicalRawSemidirectAction (p := P.p) (K := P.K) P.gamma
    letI := canonicalRawSemidirectAction (p := P.p) (K := P.K)
      (MonoidHom.id (MulAut P.H))
    d • w = ambientMap P d • w := by
  letI := canonicalRawSemidirectAction (p := P.p) (K := P.K) P.gamma
  letI := canonicalRawSemidirectAction (p := P.p) (K := P.K)
    (MonoidHom.id (MulAut P.H))
  change MulOpposite.op (MulAut.conj d.left⁻¹) •
      (MulOpposite.op (P.gamma d.right⁻¹) • w) =
    MulOpposite.op (MulAut.conj d.left⁻¹) •
      (MulOpposite.op (P.gamma d.right)⁻¹ • w)
  rw [map_inv P.gamma d.right]

variable (psi : Definition35Brauer P)

theorem global_membership_iff (d : P.H ⋊[P.gamma] P.Gamma) :
    ambientMap P d ∈ globalStabilizer P.iota (MonoidHom.id (MulAut P.H)) psi.1 ↔
      d ∈ globalStabilizer P.iota P.gamma psi.1 := by
  letI := actualBrauerAction P.iota P.gamma
  letI := actualBrauerAction P.iota (MonoidHom.id (MulAut P.H))
  change ambientMap P d • psi.1 = psi.1 ↔ d • psi.1 = psi.1
  rw [← brauer_action_agrees P d psi.1]

/-- Actual character support forces the relevant right coordinate to
preserve the specified block. This is the restricted-surjectivity join. -/
theorem global_right_block_fixed (d : Holomorph P.H)
    (hd : d ∈ globalStabilizer P.iota (MonoidHom.id (MulAut P.H)) psi.1) :
    MulOpposite.op d.right⁻¹ • P.block = P.block := by
  letI := actualBrauerAction P.iota (MonoidHom.id (MulAut P.H))
  change d • psi.1 = psi.1 at hd
  rw [brauer_smul_right P.iota d psi.1] at hd
  calc
    _ = MulOpposite.op d.right⁻¹ •
        irreducibleBrauerCharacterBlock P.iota P.irreducibleBrauerInjective P.blocks psi.1 :=
      congrArg (fun c : P.Block => MulOpposite.op d.right⁻¹ • c) psi.2.symm
    _ = irreducibleBrauerCharacterBlock P.iota P.irreducibleBrauerInjective P.blocks
        (MulOpposite.op d.right⁻¹ • psi.1) :=
      (P.brauerBlock_transport _ _).symm
    _ = _ := (congrArg
      (irreducibleBrauerCharacterBlock P.iota P.irreducibleBrauerInjective P.blocks) hd).trans psi.2

/-- Restrict the actual ambient map to the actual character stabilizer. -/
def globalMap : globalStabilizer P.iota P.gamma psi.1 →*
    globalStabilizer P.iota (MonoidHom.id (MulAut P.H)) psi.1 where
  toFun d := ⟨ambientMap P d.1, (global_membership_iff P psi d.1).mpr d.2⟩
  map_one' := Subtype.ext (map_one (ambientMap P))
  map_mul' d c := Subtype.ext (map_mul (ambientMap P) d.1 c.1)

include adapter in
theorem globalMap_bijective : Function.Bijective (globalMap P psi) := by
  constructor
  · intro d c h
    exact Subtype.ext (ambientMap_injective P adapter (congrArg Subtype.val h))
  · intro d
    obtain ⟨c, hc⟩ := exists_ambient_preimage_of_block_fixed P adapter d.1
      (global_right_block_fixed P psi d.1 d.2)
    have hglobal : c ∈ globalStabilizer P.iota P.gamma psi.1 :=
      (global_membership_iff P psi c).mp (hc.symm ▸ d.2)
    exact ⟨⟨c, hglobal⟩, Subtype.ext hc⟩

def globalEquiv : globalStabilizer P.iota P.gamma psi.1 ≃*
    globalStabilizer P.iota (MonoidHom.id (MulAut P.H)) psi.1 :=
  MulEquiv.ofBijective (globalMap P psi) (globalMap_bijective P adapter psi)

@[simp] theorem globalEquiv_ambient (d : globalStabilizer P.iota P.gamma psi.1) :
    (globalEquiv P adapter psi d : Holomorph P.H) = ambientMap P d.1 := rfl

variable (W : CharacterWeight P.p P.K P.H)

theorem raw_membership_iff (d : P.H ⋊[P.gamma] P.Gamma) :
    ambientMap P d ∈ rawStabilizer (MonoidHom.id (MulAut P.H)) W ↔
      d ∈ rawStabilizer P.gamma W := by
  letI := canonicalRawSemidirectAction (p := P.p) (K := P.K) P.gamma
  letI := canonicalRawSemidirectAction (p := P.p) (K := P.K)
    (MonoidHom.id (MulAut P.H))
  change ambientMap P d •
      (Quotient.mk'' W : RawWeightClass (p := P.p) (K := P.K) (H := P.H)) = Quotient.mk'' W ↔
    d • (Quotient.mk'' W : RawWeightClass (p := P.p) (K := P.K) (H := P.H)) = Quotient.mk'' W
  rw [← raw_action_agrees P d (Quotient.mk'' W)]

private theorem rawOrbit_op_smul (alpha : (MulAut P.H)ᵐᵒᵖ)
    (w : RawWeightClass (p := P.p) (K := P.K) (H := P.H)) :
    rawWeightOrbit (alpha • w) = alpha • rawWeightOrbit w := by
  refine Quotient.inductionOn w ?_
  intro V
  rfl

/-- Fixing the OWN raw pair fixes its ambient class, hence its specified
weight block. The hypothesis is actual block membership, not containment. -/
theorem raw_right_block_fixed
    (hW : P.blockSource.weightBlock (weightClass W) = P.block)
    (d : Holomorph P.H) (hd : d ∈ rawStabilizer (MonoidHom.id (MulAut P.H)) W) :
    MulOpposite.op d.right⁻¹ • P.block = P.block := by
  letI := canonicalRawSemidirectAction (p := P.p) (K := P.K)
    (MonoidHom.id (MulAut P.H))
  change d • (Quotient.mk'' W : RawWeightClass (p := P.p) (K := P.K) (H := P.H)) =
    Quotient.mk'' W at hd
  have hclass := congrArg
    (rawWeightOrbit (p := P.p) (K := P.K) (H := P.H)) hd
  change rawWeightOrbit (MulOpposite.op (MulAut.conj d.left⁻¹) •
      (MulOpposite.op d.right⁻¹ •
        (Quotient.mk'' W : RawWeightClass (p := P.p) (K := P.K) (H := P.H)))) =
    weightClass W at hclass
  rw [rawOrbit_op_smul P, rawOrbit_op_smul P] at hclass
  have hinner := inner_fixes_weightClass d.left (MulOpposite.op d.right⁻¹ • weightClass W)
  change MulOpposite.op (MulAut.conj d.left⁻¹) •
      (MulOpposite.op d.right⁻¹ • weightClass W) =
    MulOpposite.op d.right⁻¹ • weightClass W at hinner
  change MulOpposite.op (MulAut.conj d.left⁻¹) •
      (MulOpposite.op d.right⁻¹ • weightClass W) = weightClass W at hclass
  have hfixed := hinner.symm.trans hclass
  calc
    _ = MulOpposite.op d.right⁻¹ • P.blockSource.weightBlock (weightClass W) :=
      congrArg (fun c : P.Block => MulOpposite.op d.right⁻¹ • c) hW.symm
    _ = P.blockSource.weightBlock (MulOpposite.op d.right⁻¹ • weightClass W) :=
      (P.blockSource.weightBlock_transport _ _).symm
    _ = _ := (congrArg P.blockSource.weightBlock hfixed).trans hW

include adapter in
/-- The two full raw containments are equivalent for a weight in THIS
specified block; neither containment is a premise. -/
theorem fullRawContainment_iff
    (hW : P.blockSource.weightBlock (weightClass W) = P.block) :
    (rawStabilizer P.gamma W ≤ globalStabilizer P.iota P.gamma psi.1) ↔
      (rawStabilizer (MonoidHom.id (MulAut P.H)) W ≤
        globalStabilizer P.iota (MonoidHom.id (MulAut P.H)) psi.1) := by
  constructor
  · intro contained d hd
    obtain ⟨c, hc⟩ := exists_ambient_preimage_of_block_fixed P adapter d
      (raw_right_block_fixed P W hW d hd)
    have hraw : c ∈ rawStabilizer P.gamma W :=
      (raw_membership_iff P W c).mp (hc.symm ▸ hd)
    exact hc ▸ (global_membership_iff P psi c).mpr (contained hraw)
  · intro contained d hd
    exact (global_membership_iff P psi d).mp
      (contained ((raw_membership_iff P W d).mpr hd))

include adapter in
/-- The selected fibre supplies the preceding membership in K. -/
theorem selected_fullRawContainment_iff (w : Definition35Weight P) :
    (rawStabilizer P.gamma (selectedCharacterWeight P.blockSource P.block w) ≤
        globalStabilizer P.iota P.gamma psi.1) ↔
      (rawStabilizer (MonoidHom.id (MulAut P.H))
          (selectedCharacterWeight P.blockSource P.block w) ≤
        globalStabilizer P.iota (MonoidHom.id (MulAut P.H)) psi.1) := by
  apply fullRawContainment_iff P adapter psi
    (selectedCharacterWeight P.blockSource P.block w)
  exact (congrArg P.blockSource.weightBlock
    (selectedCharacterWeight_spec P.blockSource P.block w)).trans w.2

theorem globalEquiv_mem_base_iff (d : globalStabilizer P.iota P.gamma psi.1) :
    globalEquiv P adapter psi d ∈
        baseSubgroup P.iota (MonoidHom.id (MulAut P.H)) psi.1 ↔
      d ∈ baseSubgroup P.iota P.gamma psi.1 := by
  change P.gamma d.1.right = 1 ↔ d.1.right = 1
  constructor
  · intro h
    exact gamma_injective P adapter (h.trans (map_one P.gamma).symm)
  · intro h
    rw [h, map_one]

theorem globalEquiv_map_base :
    (baseSubgroup P.iota P.gamma psi.1).map (globalEquiv P adapter psi).toMonoidHom =
      baseSubgroup P.iota (MonoidHom.id (MulAut P.H)) psi.1 :=
  image_of_membership _ _ _ (globalEquiv_mem_base_iff P adapter psi)

theorem globalEquiv_mem_local_iff (d : globalStabilizer P.iota P.gamma psi.1) :
    globalEquiv P adapter psi d ∈
        localSubgroup P.iota (MonoidHom.id (MulAut P.H)) psi.1 W ↔
      d ∈ localSubgroup P.iota P.gamma psi.1 W :=
  raw_membership_iff P W d.1

theorem globalEquiv_map_local :
    (localSubgroup P.iota P.gamma psi.1 W).map (globalEquiv P adapter psi).toMonoidHom =
      localSubgroup P.iota (MonoidHom.id (MulAut P.H)) psi.1 W :=
  image_of_membership _ _ _ (globalEquiv_mem_local_iff P adapter psi W)

def baseKernelEquiv : baseSubgroup P.iota P.gamma psi.1 ≃*
    baseSubgroup P.iota (MonoidHom.id (MulAut P.H)) psi.1 :=
  ((globalEquiv P adapter psi).subgroupMap (baseSubgroup P.iota P.gamma psi.1)).trans
    (MulEquiv.subgroupCongr (globalEquiv_map_base P adapter psi))

@[simp] theorem baseKernelEquiv_ambient (x : baseSubgroup P.iota P.gamma psi.1) :
    (baseKernelEquiv P adapter psi x :
      globalStabilizer P.iota (MonoidHom.id (MulAut P.H)) psi.1) =
    globalEquiv P adapter psi x.1 := rfl

theorem baseKernelEquiv_base_square (x : P.H) :
    baseKernelEquiv P adapter psi
        (OddTwoActualStabilizerTriple.baseEquiv P.iota P.gamma psi.1 x) =
      OddTwoActualStabilizerTriple.baseEquiv P.iota (MonoidHom.id (MulAut P.H)) psi.1 x := by
  apply Subtype.ext
  apply Subtype.ext
  change ambientMap P
      (OddTwoActualStabilizerTriple.baseEquiv P.iota P.gamma psi.1 x).1.1 =
    (OddTwoActualStabilizerTriple.baseEquiv P.iota (MonoidHom.id (MulAut P.H)) psi.1 x).1.1
  rw [OddTwoActualStabilizerTriple.baseEquiv_ambient,
    OddTwoActualStabilizerTriple.baseEquiv_ambient, ambientMap_inl]

def localEquiv : localSubgroup P.iota P.gamma psi.1 W ≃*
    localSubgroup P.iota (MonoidHom.id (MulAut P.H)) psi.1 W :=
  ((globalEquiv P adapter psi).subgroupMap (localSubgroup P.iota P.gamma psi.1 W)).trans
    (MulEquiv.subgroupCongr (globalEquiv_map_local P adapter psi W))

@[simp] theorem localEquiv_ambient (x : localSubgroup P.iota P.gamma psi.1 W) :
    (localEquiv P adapter psi W x :
      globalStabilizer P.iota (MonoidHom.id (MulAut P.H)) psi.1) =
    globalEquiv P adapter psi x.1 := rfl

/-- Reuse the accepted identity on the actual own normalizer. This
definition does not require an equivalence Gamma to full Aut. -/
abbrev displayedIntersectionEquiv :=
  OddTwoActingGroupTupleTransport.displayedIntersectionEquiv P.iota P.gamma psi.1 W

theorem displayedIntersectionEquiv_normalizer_square
    (x : Subgroup.normalizer (W.subgroup : Set P.H)) :
    displayedIntersectionEquiv P psi W (normalizerEquivIntersection P.iota P.gamma psi.1 W x) =
      normalizerEquivIntersection P.iota (MonoidHom.id (MulAut P.H)) psi.1 W x :=
  OddTwoActingGroupTupleTransport.displayedIntersectionEquiv_normalizer_square
    P.iota P.gamma psi.1 W x

theorem displayedIntersectionEquiv_ambient
    (x : ↥(baseSubgroup P.iota P.gamma psi.1 ⊓ localSubgroup P.iota P.gamma psi.1 W)) :
    (displayedIntersectionEquiv P psi W x :
      globalStabilizer P.iota (MonoidHom.id (MulAut P.H)) psi.1) =
    globalEquiv P adapter psi x.1 := by
  obtain ⟨h, rfl⟩ := (normalizerEquivIntersection P.iota P.gamma psi.1 W).surjective x
  rw [displayedIntersectionEquiv_normalizer_square]
  apply Subtype.ext
  change (normalizerEquivIntersection P.iota (MonoidHom.id (MulAut P.H)) psi.1 W h).1.1 =
    ambientMap P (normalizerEquivIntersection P.iota P.gamma psi.1 W h).1.1
  rw [normalizerEquivIntersection_ambient, normalizerEquivIntersection_ambient,
    ambientMap_inl]

/-- Actual restricted global coordinates; roots are retained in the
explicit tuple parameters even though the groups do not depend on them. -/
def groupCoordinates (P : Definition35Problem.{u})
    (adapter : Definition35AutomorphismStabilizerAdapter P) (psi : Definition35Brauer P)
    (W : CharacterWeight P.p P.K P.H) (R : OwnNormalizerReduction (k := P.k) W) :
    GroupCoordinates (arguments P.iota P.gamma psi.1 W R)
      (arguments P.iota (MonoidHom.id (MulAut P.H)) psi.1 W R) := by
  exact {
    ambient := globalEquiv P adapter psi
    map_base := globalEquiv_map_base P adapter psi
    map_local := globalEquiv_map_local P adapter psi W }

/-- The SAME ambient/normalizer roots and characters give reflexive
horizontal squares, transported through the computed identity coordinates. -/
def tupleIsomorphism (P : Definition35Problem.{u})
    (adapter : Definition35AutomorphismStabilizerAdapter P) (psi : Definition35Brauer P)
    (W : CharacterWeight P.p P.K P.H) (R : OwnNormalizerReduction (k := P.k) W) :
    TupleIsomorphism (arguments P.iota P.gamma psi.1 W R)
      (arguments P.iota (MonoidHom.id (MulAut P.H)) psi.1 W R) :=
  TupleIsomorphism.ofDisplayed
    (groupCoordinates P adapter psi W R)
    (baseKernelEquiv P adapter psi) (displayedIntersectionEquiv P psi W)
    (baseKernelEquiv_ambient P adapter psi) (displayedIntersectionEquiv_ambient P adapter psi W)
    (rootCompatibleAlong_transport P.iota P.iota (MonoidHom.id P.H)
      (OddTwoActualStabilizerTriple.baseEquiv P.iota P.gamma psi.1)
      (OddTwoActualStabilizerTriple.baseEquiv P.iota (MonoidHom.id (MulAut P.H)) psi.1)
      (baseKernelEquiv P adapter psi).toMonoidHom
      (baseKernelEquiv_base_square P adapter psi) (by intro V x z; rfl))
    (rootCompatibleAlong_transport (ownReductionRoot (k := P.k) W R)
      (ownReductionRoot (k := P.k) W R)
      (MonoidHom.id (Subgroup.normalizer (W.subgroup : Set P.H)))
      (normalizerEquivIntersection P.iota P.gamma psi.1 W)
      (normalizerEquivIntersection P.iota (MonoidHom.id (MulAut P.H)) psi.1 W)
      (displayedIntersectionEquiv P psi W).toMonoidHom
      (displayedIntersectionEquiv_normalizer_square P psi W) (by intro V x z; rfl))
    (values_transport P.iota P.iota (MonoidHom.id P.H)
      (OddTwoActualStabilizerTriple.baseEquiv P.iota P.gamma psi.1)
      (OddTwoActualStabilizerTriple.baseEquiv P.iota (MonoidHom.id (MulAut P.H)) psi.1)
      (baseKernelEquiv P adapter psi).toMonoidHom
      (baseKernelEquiv_base_square P adapter psi) psi.1 psi.1 (by intro x; rfl))
    (values_transport (ownReductionRoot (k := P.k) W R) (ownReductionRoot (k := P.k) W R)
      (MonoidHom.id (Subgroup.normalizer (W.subgroup : Set P.H)))
      (normalizerEquivIntersection P.iota P.gamma psi.1 W)
      (normalizerEquivIntersection P.iota (MonoidHom.id (MulAut P.H)) psi.1 W)
      (displayedIntersectionEquiv P psi W).toMonoidHom
      (displayedIntersectionEquiv_normalizer_square P psi W)
      (ownReductionBrauer (k := P.k) W R) (ownReductionBrauer (k := P.k) W R)
      (by intro x; rfl))

/-- Only the existing universal authentic standard-definition transport
source is used, after the actual tuple packet has been constructed. -/
theorem blockIsomorphic_iff (P : Definition35Problem.{u})
    (adapter : Definition35AutomorphismStabilizerAdapter P) (psi : Definition35Brauer P)
    (W : CharacterWeight P.p P.K P.H) (R : OwnNormalizerReduction (k := P.k) W)
    (standard : BlockTripleSourceSemantics P.p P.k P.K)
    (source : StandardTransportSource standard) :
    standard.blockIsomorphic (arguments P.iota P.gamma psi.1 W R) ↔
      standard.blockIsomorphic (arguments P.iota (MonoidHom.id (MulAut P.H)) psi.1 W R) :=
  source.relation_iff _ _ (tupleIsomorphism P adapter psi W R)

end ModularRep.PaperProofs.TypeCBlockStabilizerTupleTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
