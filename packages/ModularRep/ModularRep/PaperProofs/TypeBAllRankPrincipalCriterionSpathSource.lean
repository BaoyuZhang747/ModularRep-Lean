import ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionFixedBlockSource
import ModularRep.PaperProofs.TypeBCentralKernelPairSplittingBinding
import ModularRep.PaperProofs.TypeBCentralKernelPrincipalStability
import ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionCarriers
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCoverAutomorphismEquiv

/-!
# The forward Spath passage on one fixed pair

The full cover is a specified homomorphism, distinct from the identity
prime-to-two cover. Its hatted weight is the full preimage; its global and
local modular characters are literal pullbacks over the same modular
system. The canonical target is the existing complete PairWitness on the
actual character and raw-weight inertias inside the full automorphism
semidirect product.

The source boundary below is the forward implication of Spath Theorem 4.4.
It has no inhabitant here. Its specified hatted block induction and exact
normalizer-stabilizer interpretation remain subordinate E1/E2/U joins.
One normalized Clause III packet supplies the same two honest extensions
and all its intermediate block equations. No arbitrary relation, BAW
predicate, all-block family or reverse Proposition 3.6(b) is used.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionSpathSource

open ModularRep CharacterWeight
open TypeBLocalReductionInstantiation TypeBModularGroupRootBinding
open TypeBCentralKernelTripleCertificate TypeBCentralKernelTripleRootFamily
open TypeBCentralKernelTripleCarriers TypeBCentralKernelWeightTransport
open TypeBAllRankPrincipalCriterionFixedBlockSource TypeBQ3PrincipalCriterionData
open IrreducibleBrauerCharacterSurjectiveDescent
open EvenFieldFLZ318FixedTheoremGate

local instance finiteFintype (X : Type) [Finite X] : Fintype X := Fintype.ofFinite X
local instance twoPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

section CanonicalAmbient

variable (Y : Type) [Group Y]

/-- The full natural automorphism ambient has fixed coordinates. -/
abbrev AutAmbient := Y ⋊[MonoidHom.id (MulAut Y)] MulAut Y

instance autAmbientFinite [Finite Y] : Finite (AutAmbient Y) := by
  letI : Finite (MulAut Y) :=
    Finite.of_injective (fun a : MulAut Y => (a : Y → Y)) DFunLike.coe_injective
  exact Finite.of_equiv (Y × MulAut Y) SemidirectProduct.equivProd.symm

/-- The base is the range of the literal left inclusion. -/
def canonicalBase : Subgroup (AutAmbient Y) :=
  (SemidirectProduct.inl : Y →* AutAmbient Y).range

instance canonicalBaseNormal : (canonicalBase Y).Normal := by
  change (SemidirectProduct.inl : Y →* AutAmbient Y).range.Normal
  rw [SemidirectProduct.range_inl_eq_ker_rightHom]
  infer_instance

def baseEquiv : Y ≃* canonicalBase Y :=
  MonoidHom.ofInjective SemidirectProduct.inl_injective

@[simp] theorem baseEquiv_val (y : Y) :
    (baseEquiv Y y).val = SemidirectProduct.inl y := rfl

/-- Both factors act by their actual automorphisms of the original group. -/
def naturalAction : AutAmbient Y →* MulAut Y :=
  ModularRep.ManuscriptVerification.CyclicOuterBAW.semidirectToMulAut
    (MonoidHom.id (MulAut Y))

theorem naturalAction_value (a : AutAmbient Y) (y : Y) :
    naturalAction Y a y = a.left * a.right y * a.left⁻¹ := by
  change ModularRep.ManuscriptVerification.CyclicOuterBAW.semidirectToMulAut
    (MonoidHom.id (MulAut Y)) a y = _
  rw [← SemidirectProduct.inl_left_mul_inr_right a, map_mul]
  rw [ModularRep.ManuscriptVerification.CyclicOuterBAW.semidirectToMulAut_inl,
    ModularRep.ManuscriptVerification.CyclicOuterBAW.semidirectToMulAut_inr]
  simp only [SemidirectProduct.inl_left_mul_inr_right,
    MulAut.mul_apply, MonoidHom.id_apply, MulAut.conj_apply]

/-- This square ties the canonical target inertias to natural automorphisms. -/
theorem baseEquiv_action (a : AutAmbient Y) (y : Y) :
    baseEquiv Y (naturalAction Y a y) =
      MulAut.conjNormal (H := canonicalBase Y) a (baseEquiv Y y) := by
  apply Subtype.ext
  change SemidirectProduct.inl (naturalAction Y a y) =
    a * SemidirectProduct.inl y * a⁻¹
  apply SemidirectProduct.ext
  · rw [naturalAction_value]
    simp [mul_assoc]
  · simp

theorem baseEquiv_congr (a : AutAmbient Y) :
    MulAut.congr (baseEquiv Y) (naturalAction Y a) =
      MulAut.conjNormal (H := canonicalBase Y) a := by
  apply MulEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ := (baseEquiv Y).surjective x
  change baseEquiv Y (naturalAction Y a ((baseEquiv Y).symm (baseEquiv Y y))) = _
  rw [MulEquiv.symm_apply_apply]
  exact baseEquiv_action Y a y

end CanonicalAmbient

section CanonicalPair

variable {k K O Y : Type} [Field k] [Field K] [CommRing O] [IsDomain O]
  [Algebra O K] [CharP k 2] [IsAlgClosed k] [CharZero K] [Group Y] [Finite Y]
  (Msys : ModularSystem 2 K O k)
  (root : PrimeRegularRootEmbedding 2 k K Y)
  (calibration : RootResidueCompatible Msys root)

def embeddedRoot : PrimeRegularRootEmbedding 2 k K (canonicalBase Y) :=
  root.alongMulEquiv (baseEquiv Y)

include calibration in
theorem embeddedRoot_residue : RootResidueCompatible Msys (embeddedRoot root) :=
  TypeBCentralKernelPairSplittingBinding.alongMulEquiv_residue
    Msys root calibration (baseEquiv Y)

def embeddedCharacter (phi : IBr root) : IBr (embeddedRoot root) :=
  IrreducibleBrauerCharacter.equivAlongMulEquiv root (baseEquiv Y) phi

def embeddedWeight (W : CharacterWeight 2 K Y) :
    CharacterWeight 2 K (canonicalBase Y) :=
  TypeBCentralKernelSpinFibreIdentification.rawWeightEquiv (baseEquiv Y) W

abbrev characterInertia (phi : IBr root) : Subgroup (AutAmbient Y) :=
  TypeBCentralKernelInertia.T (canonicalBase Y) (embeddedRoot root)
    (embeddedCharacter root phi)

abbrev weightInertia (W : CharacterWeight 2 K Y) : Subgroup (AutAmbient Y) :=
  TypeBCentralKernelInertia.U (canonicalBase Y) (embeddedWeight W)

theorem embeddedCharacter_twist (phi : IBr root) (a : AutAmbient Y) :
    embeddedCharacter root (IrreducibleBrauerCharacter.twist root phi (naturalAction Y a)) =
      IrreducibleBrauerCharacter.twist (embeddedRoot root) (embeddedCharacter root phi)
        (MulAut.conjNormal (H := canonicalBase Y) a) := by
  change IrreducibleBrauerCharacter.equivAlongMulEquiv root (baseEquiv Y)
      (IrreducibleBrauerCharacter.twist root phi (naturalAction Y a)) = _
  rw [IrreducibleBrauerCharacter.equivAlongMulEquiv_twist, baseEquiv_congr]
  rfl

theorem characterInertia_iff (phi : IBr root) (a : AutAmbient Y) :
    a ∈ characterInertia root phi ↔
      IrreducibleBrauerCharacter.twist root phi (naturalAction Y a⁻¹) = phi := by
  change IrreducibleBrauerCharacter.twist (embeddedRoot root) (embeddedCharacter root phi)
    (MulAut.conjNormal (H := canonicalBase Y) a⁻¹) = embeddedCharacter root phi ↔ _
  rw [← embeddedCharacter_twist]
  exact (IrreducibleBrauerCharacter.equivAlongMulEquiv root (baseEquiv Y)).injective.eq_iff

theorem embeddedWeight_twist (W : CharacterWeight 2 K Y) (a : AutAmbient Y) :
    embeddedWeight (W.rightTwist (naturalAction Y a)) =
      (embeddedWeight W).rightTwist (MulAut.conjNormal (H := canonicalBase Y) a) :=
  TypeBCentralKernelSpinFibreIdentification.rawWeightEquiv_rightTwist (baseEquiv Y)
    (naturalAction Y a) (MulAut.conjNormal (H := canonicalBase Y) a)
    (baseEquiv_action Y a) W

theorem weightInertia_iff (W : CharacterWeight 2 K Y) (a : AutAmbient Y) :
    a ∈ weightInertia W ↔ W.rightTwist (naturalAction Y a⁻¹) = W := by
  rw [TypeBCentralKernelInertia.mem_rawStabilizer]
  change (embeddedWeight W).rightTwist (MulAut.conjNormal (H := canonicalBase Y) a⁻¹) =
    embeddedWeight W ↔ _
  rw [← embeddedWeight_twist]
  exact (TypeBCentralKernelSpinFibreIdentification.rawWeightEquiv (baseEquiv Y)).injective.eq_iff

def embeddedOrdinaryRoots [HasEnoughRootsOfUnity K (Nat.card Y)] :
    HasEnoughRootsOfUnity K (Nat.card (canonicalBase Y)) := by
  rw [← Nat.card_congr (baseEquiv Y).toEquiv]
  infer_instance

variable (phi : IBr root) (W : CharacterWeight 2 K Y)
  (hUT : weightInertia W ≤ characterInertia root phi)

abbrev PairBlocks := PhysicalBlockFamily (k := k)
  (inside (canonicalBase Y) (characterInertia root phi))
  (inside (weightInertia W) (characterInertia root phi))

variable [HasEnoughRootsOfUnity K (Nat.card Y)]
  (navarro : ∀ (H : Type) [Group H] [Finite H]
    [HasEnoughRootsOfUnity K (Nat.card H)]
    (iota : PrimeRegularRootEmbedding 2 k K H)
    (compatible : RootResidueCompatible Msys iota),
      ScopedDefectZeroReductionSource Msys iota compatible)
  (blocks : PairBlocks root phi W)

/-- The target is the inherited full operator/tensor/block witness. -/
abbrev CanonicalPairWitness := by
  letI := embeddedOrdinaryRoots (K := K) (Y := Y)
  exact TypeBCentralKernelPairSplittingBinding.PairWitness
    Msys (canonicalBase Y) (embeddedRoot root)
    (embeddedRoot_residue Msys root calibration)
    (embeddedCharacter root phi) (embeddedWeight W) hUT navarro blocks

end CanonicalPair

section FullCoverPair

variable {k K O Y Hhat : Type} [Field k] [Field K] [CommRing O] [IsDomain O]
  [Algebra O K] [CharP k 2] [IsAlgClosed k] [CharZero K]
  [Group Y] [Finite Y] [Group Hhat] [Finite Hhat]
  (Msys : ModularSystem 2 K O k)
  (q : Hhat →* Y) (surjective : Function.Surjective q)
  (kernelTwo : IsPGroup 2 q.ker)
  (root : PrimeRegularRootEmbedding 2 k K Y)
  (calibration : RootResidueCompatible Msys root)

/-- The hatted root is constructed from the original modular system. -/
abbrev hattedRoot : PrimeRegularRootEmbedding 2 k K Hhat := groupRoot Msys Hhat

include calibration in
theorem hatted_root_compatible (V : FDRep k Y) :
    Representation.BrauerRootLiftCompatibleAlong V.ρ root (hattedRoot Msys) q := by
  rw [eq_groupRoot_of_residue Msys Y root calibration]
  exact groupRoot_compatible_along Msys V.ρ q

/-- Inflation retains the actual pullback representation and class function. -/
def hattedCharacter (phi : IBr root) : IBr (hattedRoot Msys (Hhat := Hhat)) :=
  (inflateToKernelTrivialIBrAlong q surjective (hattedRoot Msys) root
    (hatted_root_compatible Msys q root calibration) phi).val

@[simp] theorem hattedCharacter_value (phi : IBr root) :
    (hattedCharacter Msys q surjective root calibration phi).val =
      PrimeRegularClassFunction.pullback q phi.val := rfl

/-- Full preimage, with the original ordinary character transported canonically. -/
abbrev hattedWeight (W : CharacterWeight 2 K Y) : CharacterWeight 2 K Hhat :=
  TypeBCentralKernelWeightTransport.lift q surjective kernelTwo W

@[simp] theorem hattedWeight_subgroup (W : CharacterWeight 2 K Y) :
    (hattedWeight q surjective kernelTwo W).subgroup = W.subgroup.comap q := rfl

variable (W : CharacterWeight 2 K Y)

abbrev HattedNormalizer :=
  Subgroup.normalizer ((W.subgroup.comap q : Subgroup Hhat) : Set Hhat)

include surjective in
theorem hattedNormalizer_preimage :
    Subgroup.normalizer ((W.subgroup.comap q : Subgroup Hhat) : Set Hhat) =
      (Subgroup.normalizer (W.subgroup : Set Y)).comap q :=
  (Subgroup.comap_normalizer_eq_of_surjective W.subgroup surjective).symm

/-- This is the unchanged normalizer quotient in the manuscript passage. -/
abbrev hattedLocalEquiv : NormalizerQuotient (W.subgroup.comap q) ≃*
    NormalizerQuotient W.subgroup := preimageLocalEquiv q surjective W.subgroup

/-- The local ordinary inflation uses this exact quotient homomorphism. -/
def hattedLocalProjection : HattedNormalizer q W →* NormalizerQuotient W.subgroup :=
  (hattedLocalEquiv q surjective W).toMonoidHom.comp (localMk (W.subgroup.comap q))

theorem hattedLocalProjection_surjective :
    Function.Surjective (hattedLocalProjection q surjective W) :=
  (hattedLocalEquiv q surjective W).surjective.comp
    (QuotientGroup.mk'_surjective _)

def hattedOrdinaryValue (x : HattedNormalizer q W) : K :=
  W.localCharacter (hattedLocalProjection q surjective W x)

theorem hattedOrdinaryValue_eq (x : HattedNormalizer q W) :
    hattedOrdinaryValue q surjective W x =
      (hattedWeight q surjective kernelTwo W).localCharacter
        (localMk (W.subgroup.comap q) x) := rfl

variable [HasEnoughRootsOfUnity K (Nat.card Y)]
  (navarro : ∀ (H : Type) [Group H] [Finite H]
    [HasEnoughRootsOfUnity K (Nat.card H)]
    (iota : PrimeRegularRootEmbedding 2 k K H)
    (compatible : RootResidueCompatible Msys iota),
      ScopedDefectZeroReductionSource Msys iota compatible)

/-- The same downstairs defect-zero reduction is inflated on the hatted
normalizer; no ordinary splitting assumption on the full cover is added. -/
def hattedLocalCharacter : IBr (groupRoot Msys (HattedNormalizer q W)) :=
  (inflateToKernelTrivialIBrAlong (hattedLocalProjection q surjective W)
    (hattedLocalProjection_surjective q surjective W)
    (groupRoot Msys (HattedNormalizer q W))
    (TypeBCentralKernelPairSplittingBinding.quotientRoot Msys W)
    (fun V => groupRoot_compatible_along Msys V.ρ
      (hattedLocalProjection q surjective W))
    (TypeBCentralKernelPairSplittingBinding.quotientReduction Msys W navarro)).val

theorem hattedLocalCharacter_value
    (x : PrimeRegularElement (G := HattedNormalizer q W) 2) :
    (hattedLocalCharacter Msys q surjective W navarro).val x =
      hattedOrdinaryValue q surjective W x.val :=
  (TypeBCentralKernelPairSplittingBinding.quotientReduction_value Msys W navarro
    (PrimeRegularElement.map (hattedLocalProjection q surjective W) x)).symm

end FullCoverPair

section CentralQuotients

variable {k K O Y Hhat : Type} [Field k] [Field K] [CommRing O] [IsDomain O]
  [Algebra O K] [CharP k 2] [IsAlgClosed k] [CharZero K]
  [Group Y] [Finite Y] [Group Hhat] [Finite Hhat]
  (Msys : ModularSystem 2 K O k)
  (q : Hhat →* Y) (surjective : Function.Surjective q)
  (kernelTwo : IsPGroup 2 q.ker) (kernelCenter : q.ker = Subgroup.center Hhat)
  (root : PrimeRegularRootEmbedding 2 k K Y)
  (calibration : RootResidueCompatible Msys root) (phi : IBr root)

include kernelTwo kernelCenter in
/-- Navarro 2.32 is applied to the actual chosen affording representation.
Only its central kernel is identified; phi need not be faithful. -/
theorem hattedCentralKernel_eq
    (kernel : TypeBCentralKernelBrauerInflation.Navarro232Principle 2 k) :
    TypeBBSCentralCharacterQuotient.centralKernel (hattedRoot Msys)
      (hattedCharacter Msys q surjective root calibration phi) = q.ker := by
  let psi := hattedCharacter Msys q surjective root calibration phi
  change Subgroup.center Hhat ⊓
    (EvenFieldFLZBAWGoodFamily.chosenIBrRepresentation (hattedRoot Msys) psi).ρ.ker = q.ker
  rw [← kernelCenter]
  apply inf_eq_left.mpr
  exact kernel Hhat q.ker Nat.prime_two kernelTwo
    (EvenFieldFLZBAWGoodFamily.chosenIBrRepresentation (hattedRoot Msys) psi)
    (Classical.choose_spec psi.property).1

variable (centralKernelEq :
  TypeBBSCentralCharacterQuotient.centralKernel (hattedRoot Msys)
    (hattedCharacter Msys q surjective root calibration phi) = q.ker)

/-- The character-central quotient is identified by the actual q, not
by a separately supplied group equivalence. -/
def hattedCentralQuotientEquiv :
    Hhat ⧸ TypeBBSCentralCharacterQuotient.centralKernel (hattedRoot Msys)
      (hattedCharacter Msys q surjective root calibration phi) ≃* Y :=
  (QuotientGroup.quotientMulEquivOfEq centralKernelEq).trans
    (QuotientGroup.quotientKerEquivOfSurjective q surjective)

@[simp] theorem hattedCentralQuotientEquiv_mk (x : Hhat) :
    hattedCentralQuotientEquiv Msys q surjective root calibration phi centralKernelEq
      (QuotientGroup.mk' _ x) = q x := rfl

variable (W : CharacterWeight 2 K Y)

/-- Literal restriction of q to the full-preimage normalizer. -/
def hattedNormalizerProjection : HattedNormalizer q W →*
    Subgroup.normalizer (W.subgroup : Set Y) where
  toFun x := ⟨q x.val, by
    change x.val ∈ (Subgroup.normalizer (W.subgroup : Set Y)).comap q
    rw [← hattedNormalizer_preimage q surjective W]
    exact x.property⟩
  map_one' := Subtype.ext q.map_one
  map_mul' x y := Subtype.ext (q.map_mul x.val y.val)

@[simp] theorem hattedNormalizerProjection_val (x : HattedNormalizer q W) :
    (hattedNormalizerProjection q surjective W x).val = q x.val := rfl

theorem hattedNormalizerProjection_surjective :
    Function.Surjective (hattedNormalizerProjection q surjective W) := by
  intro y
  obtain ⟨x, hx⟩ := surjective y.val
  have hmem : x ∈ Subgroup.normalizer ((W.subgroup.comap q : Subgroup Hhat) : Set Hhat) := by
    rw [hattedNormalizer_preimage q surjective W]
    change q x ∈ Subgroup.normalizer (W.subgroup : Set Y)
    rw [hx]
    exact y.property
  exact ⟨⟨x, hmem⟩, Subtype.ext hx⟩

include centralKernelEq in
theorem hattedNormalizerProjection_kernel :
    (hattedNormalizerProjection q surjective W).ker =
      (TypeBBSCentralCharacterQuotient.centralKernel (hattedRoot Msys)
        (hattedCharacter Msys q surjective root calibration phi)).comap
          (HattedNormalizer q W).subtype := by
  rw [centralKernelEq]
  ext x
  change hattedNormalizerProjection q surjective W x = 1 ↔ q x.val = 1
  exact Subtype.ext_iff

/-- The local central quotient uses the very same character-central kernel. -/
def hattedLocalCentralQuotientEquiv :
    HattedNormalizer q W ⧸
      (TypeBBSCentralCharacterQuotient.centralKernel (hattedRoot Msys)
        (hattedCharacter Msys q surjective root calibration phi)).comap
          (HattedNormalizer q W).subtype ≃*
      Subgroup.normalizer (W.subgroup : Set Y) :=
  (QuotientGroup.quotientMulEquivOfEq
    (hattedNormalizerProjection_kernel Msys q surjective root calibration phi
      centralKernelEq W).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (hattedNormalizerProjection q surjective W)
      (hattedNormalizerProjection_surjective q surjective W))

@[simp] theorem hattedLocalCentralQuotientEquiv_mk (x : HattedNormalizer q W) :
    (hattedLocalCentralQuotientEquiv Msys q surjective root calibration phi
      centralKernelEq W (QuotientGroup.mk' _ x)).val = q x.val := rfl

theorem hattedLocalProjection_normalizer (x : HattedNormalizer q W) :
    hattedLocalProjection q surjective W x =
      localMk W.subgroup (hattedNormalizerProjection q surjective W x) :=
  preimageLocalEquiv_mk q surjective W.subgroup x
    (hattedNormalizerProjection q surjective W x) rfl

end CentralQuotients

section Source

variable {k K O Y Hhat : Type} [Field k] [Field K] [CommRing O] [IsDomain O]
  [Algebra O K] [CharP k 2] [IsAlgClosed k] [CharZero K]
  [Group Y] [Finite Y] [Group Hhat] [Finite Hhat]
  (Msys : ModularSystem 2 K O k)
  (q : Hhat →* Y) (fullCover : IsUniversalCentralExtension q)
  (kernelCenter : q.ker = Subgroup.center Hhat)

/-- The full universal property constructs the actual lift of each actor. -/
def hattedActor (a : AutAmbient Y) : MulAut Hhat :=
  (SporadicFi24P3Definition44NamedCarrierFullCoverAutomorphismEquiv.fullCoverAutEquiv
    q fullCover kernelCenter).symm (naturalAction Y a)

theorem hattedActor_projection (a : AutAmbient Y) (x : Hhat) :
    q (hattedActor q fullCover kernelCenter a x) = naturalAction Y a (q x) :=
  SporadicFi24P3Definition44NamedCarrierFullCoverAutomorphismEquiv.fullCoverAutEquiv_symm_apply_q
    q fullCover kernelCenter (naturalAction Y a) x

variable (root : PrimeRegularRootEmbedding 2 k K Y)
  (calibration : RootResidueCompatible Msys root) (phi : IBr root)
  (W : CharacterWeight 2 K Y)
  [HasEnoughRootsOfUnity K (Nat.card Y)]
  (navarro : ∀ (H : Type) [Group H] [Finite H]
    [HasEnoughRootsOfUnity K (Nat.card H)]
    (iota : PrimeRegularRootEmbedding 2 k K H)
    (compatible : RootResidueCompatible Msys iota),
      ScopedDefectZeroReductionSource Msys iota compatible)

/-- The precise remaining specified/source joins. None is a triple relation
or completed criterion. The local block is that of the computed reduction
of W's own ordinary inflation at the same modular-system root. -/
structure FullCoverPairJoins where
  ambientBlocks : PhysicalBlocks k Hhat
  localBlocks : PhysicalBlocks k (HattedNormalizer q W)
  induction :
    letI := ambientBlocks.blockFintype
    letI := localBlocks.blockFintype
    BlockInducesTo (HattedNormalizer q W) localBlocks.catalogue ambientBlocks.catalogue
      ((characterData (groupRoot Msys (HattedNormalizer q W)) localBlocks).block
        (hattedLocalCharacter Msys q fullCover.1.1 W navarro))
      ((characterData (hattedRoot Msys) ambientBlocks).block
        (hattedCharacter Msys q fullCover.1.1 root calibration phi))
  normalizerInertia : ∀ a : AutAmbient Y,
    a ∈ weightInertia W ↔
      ∃ localActor : MulAut (HattedNormalizer q W),
        (∀ x : HattedNormalizer q W,
          (localActor x).val = hattedActor q fullCover kernelCenter a⁻¹ x.val) ∧
        ∀ x : HattedNormalizer q W,
          hattedOrdinaryValue q fullCover.1.1 W (localActor x) =
            hattedOrdinaryValue q fullCover.1.1 W x

/-- Uniform forward Theorem 4.4, specialized only to prime two and the
centreless prime-to-two cover. All targets are independently defined actual
objects; source interpretation into the complete MRR witness remains E2/U.
The SAME normalized C retains both extensions and every intermediate J. -/
structure ForwardTheorem44 (k K : Type)
    [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K] : Prop where
  forward : ∀ (Y Hhat O : Type)
      [Group Y] [Finite Y] [Group Hhat] [Finite Hhat]
      [CommRing O] [IsDomain O] [Algebra O K]
      (Msys : ModularSystem 2 K O k)
      (q : Hhat →* Y) (fullCover : IsUniversalCentralExtension q)
      (simple : IsSimpleGroup Y) (nonabelian : ¬ IsMulCommutative Y)
      (kernelCenter : q.ker = Subgroup.center Hhat)
      (kernelTwo : IsPGroup 2 q.ker)
      (root : PrimeRegularRootEmbedding 2 k K Y)
      (calibration : RootResidueCompatible Msys root)
      (phi : IBr root) (W : CharacterWeight 2 K Y)
      [HasEnoughRootsOfUnity K (Nat.card Y)]
      (navarro : ∀ (H : Type) [Group H] [Finite H]
        [HasEnoughRootsOfUnity K (Nat.card H)]
        (iota : PrimeRegularRootEmbedding 2 k K H)
        (compatible : RootResidueCompatible Msys iota),
          ScopedDefectZeroReductionSource Msys iota compatible)
      (hUT : weightInertia W ≤ characterInertia root phi)
      (product :
        inside (canonicalBase Y) (characterInertia root phi) ⊔
          inside (weightInertia W) (characterInertia root phi) = ⊤)
      (blocks : PairBlocks root phi W)
      (centralKernel :
        TypeBBSCentralCharacterQuotient.centralKernel (hattedRoot Msys)
          (hattedCharacter Msys q fullCover.1.1 root calibration phi) = q.ker)
      (joins : FullCoverPairJoins Msys q fullCover kernelCenter
        root calibration phi W navarro)
      (packet : PrincipalClauseIII root phi W)
      (normalized : RootNormalized Msys packet)
      (fieldScope : SpathCoefficientField 2 k Nat.prime_two),
    Nonempty (CanonicalPairWitness Msys root calibration phi W hUT navarro blocks)

end Source

section SamePacket

variable {k K O Y Hhat : Type} [Field k] [Field K] [CommRing O] [IsDomain O]
  [Algebra O K] [CharP k 2] [IsAlgClosed k] [CharZero K]
  [Group Y] [Finite Y] [Group Hhat] [Finite Hhat]
  (Msys : ModularSystem 2 K O k)
  (q : Hhat →* Y) (fullCover : IsUniversalCentralExtension q)
  (simple : IsSimpleGroup Y) (nonabelian : ¬ IsMulCommutative Y)
  (kernelCenter : q.ker = Subgroup.center Hhat) (kernelTwo : IsPGroup 2 q.ker)
  (root : PrimeRegularRootEmbedding 2 k K Y)
  (calibration : RootResidueCompatible Msys root)
  [HasEnoughRootsOfUnity K (Nat.card Y)]
  (navarro : ∀ (H : Type) [Group H] [Finite H]
    [HasEnoughRootsOfUnity K (Nat.card H)]
    (iota : PrimeRegularRootEmbedding 2 k K H)
    (compatible : RootResidueCompatible Msys iota),
      ScopedDefectZeroReductionSource Msys iota compatible)
  (certificate : ForwardTheorem44 k K)
  (fieldScope : SpathCoefficientField 2 k Nat.prime_two)
  {R : TypeBQ3PrincipalWeightInflation.CoverWeightSource (k := k) (K := K) Y}
  {b : LiteralPrimitiveBlock k Y}
  (D : NormalizedBlockWitness Msys root R b)

/-- An element of the actual character inertia fixes the class of the
same raw match, now transported to the canonical embedded base. -/
theorem same_match_class_fixed
    (phi : TypeBCentralKernelInertia.BrauerFibre root b)
    (W : CharacterWeight 2 K Y)
    (same : TypeBWeightCoveringSource.rawClass W = (D.omega phi).val)
    {a : AutAmbient Y} (ha : a ∈ characterInertia root phi.val) :
    TypeBCentralKernelInertia.conjugationOp (canonicalBase Y) a •
        TypeBCentralKernelInertia.classOf (embeddedWeight W) =
      TypeBCentralKernelInertia.classOf (embeddedWeight W) := by
  let alpha : (MulAut Y)ᵐᵒᵖ := MulOpposite.op (naturalAction Y a⁻¹)
  have graph := D.equivariant alpha phi phi
    ((characterInertia_iff root phi.val a).mp ha).symm
  have original : CharacterWeight.rightTwistConjugacyClass (naturalAction Y a⁻¹)
      (TypeBCentralKernelInertia.classOf W) = TypeBCentralKernelInertia.classOf W := by
    change alpha • TypeBWeightCoveringSource.rawClass W = TypeBWeightCoveringSource.rawClass W
    rw [same]
    exact graph.symm
  have mapped := congrArg
    (TypeBCentralKernelSpinFibreIdentification.weightClassEquiv (baseEquiv Y)) original
  rw [TypeBCentralKernelSpinFibreIdentification.weightClassEquiv_rightTwist
      (baseEquiv Y) (naturalAction Y a⁻¹)
      (MulAut.conjNormal (H := canonicalBase Y) a⁻¹) (baseEquiv_action Y a⁻¹),
    TypeBCentralKernelSpinFibreIdentification.weightClassEquiv_classOf] at mapped
  exact mapped

/-- The class equation supplies an actual base element adjusting the
specified actor into the raw inertia; no new match is selected. -/
theorem same_match_representative_adjustment
    (phi : TypeBCentralKernelInertia.BrauerFibre root b)
    (W : CharacterWeight 2 K Y)
    (same : TypeBWeightCoveringSource.rawClass W = (D.omega phi).val)
    {a : AutAmbient Y} (ha : a ∈ characterInertia root phi.val) :
    ∃ g : canonicalBase Y, (g : AutAmbient Y)⁻¹ * a ∈ weightInertia W := by
  have fixed := same_match_class_fixed Msys root D phi W same ha
  have iso :
      (Quotient.mk'' (TypeBCentralKernelInertia.conjugationOp (canonicalBase Y) a •
        TypeBCentralKernelInertia.isoOf (embeddedWeight W)) :
          CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := canonicalBase Y)) =
        Quotient.mk'' (TypeBCentralKernelInertia.isoOf (embeddedWeight W)) := fixed
  obtain ⟨g, hg⟩ := Quotient.exact iso
  change g • TypeBCentralKernelInertia.isoOf (embeddedWeight W) =
    TypeBCentralKernelInertia.conjugationOp (canonicalBase Y) a •
      TypeBCentralKernelInertia.isoOf (embeddedWeight W) at hg
  refine ⟨g, ?_⟩
  change TypeBCentralKernelInertia.conjugationOp (canonicalBase Y)
    ((g : AutAmbient Y)⁻¹ * a) • TypeBCentralKernelInertia.isoOf (embeddedWeight W) =
      TypeBCentralKernelInertia.isoOf (embeddedWeight W)
  rw [map_mul, mul_smul, ← hg,
    ← TypeBCentralKernelInertia.iso_action_inner (canonicalBase Y) g]
  rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]

/-- The complete target's product condition follows from that same
equivariant graph; it is not supplied by the forward source. -/
theorem same_match_product
    (phi : TypeBCentralKernelInertia.BrauerFibre root b)
    (W : CharacterWeight 2 K Y)
    (same : TypeBWeightCoveringSource.rawClass W = (D.omega phi).val) :
    inside (canonicalBase Y) (characterInertia root phi.val) ⊔
      inside (weightInertia W) (characterInertia root phi.val) = ⊤ := by
  apply top_unique
  intro t _
  obtain ⟨g, hg⟩ := same_match_representative_adjustment Msys root D phi W same t.property
  have hgT : (g : AutAmbient Y) ∈ characterInertia root phi.val :=
    TypeBCentralKernelInertia.G_le_T (canonicalBase Y) (embeddedRoot root)
      (embeddedCharacter root phi.val) g.property
  let left : characterInertia root phi.val := ⟨g.val, hgT⟩
  let right : characterInertia root phi.val :=
    ⟨g.val⁻¹ * t.val,
      (characterInertia root phi.val).mul_mem
        ((characterInertia root phi.val).inv_mem hgT) t.property⟩
  have hl : left ∈ inside (canonicalBase Y) (characterInertia root phi.val) := g.property
  have hr : right ∈ inside (weightInertia W) (characterInertia root phi.val) := hg
  have factors : left * right = t := by
    apply Subtype.ext
    simp [left, right, mul_assoc]
  rw [← factors]
  exact (inside (canonicalBase Y) (characterInertia root phi.val) ⊔
    inside (weightInertia W) (characterInertia root phi.val)).mul_mem
      ((show inside (canonicalBase Y) (characterInertia root phi.val) ≤
          inside (canonicalBase Y) (characterInertia root phi.val) ⊔
            inside (weightInertia W) (characterInertia root phi.val) from le_sup_left) hl)
      ((show inside (weightInertia W) (characterInertia root phi.val) ≤
          inside (canonicalBase Y) (characterInertia root phi.val) ⊔
            inside (weightInertia W) (characterInertia root phi.val) from le_sup_right) hr)

/-- Principal support gives the required actor in the same fibre. The
already constructed graph and its injectivity then force the same phi. -/
theorem same_match_hUT
    (sourceBlocks : PhysicalBlocks k Y)
    (principal : TypeBCentralKernelBlockSource.IsPrincipal b)
    (phi : TypeBCentralKernelInertia.BrauerFibre root b)
    (W : CharacterWeight 2 K Y)
    (same : TypeBWeightCoveringSource.rawClass W = (D.omega phi).val) :
    weightInertia W ≤ characterInertia root phi.val := by
  letI := sourceBlocks.blockFintype
  intro a ha
  have rawFixed := (weightInertia_iff W a).mp ha
  let alpha : (MulAut Y)ᵐᵒᵖ := MulOpposite.op (naturalAction Y a⁻¹)
  let psi : TypeBCentralKernelInertia.BrauerFibre root b :=
    ⟨alpha • phi.val,
      TypeBCentralKernelPrincipalStability.supported_principal_op_smul
        sourceBlocks.decomposition root b principal alpha phi.val phi.property⟩
  have graph := D.equivariant alpha phi psi rfl
  have classFixed : alpha • TypeBWeightCoveringSource.rawClass W =
      TypeBWeightCoveringSource.rawClass W :=
    congrArg TypeBWeightCoveringSource.rawClass rawFixed
  have sameImage : D.omega psi = D.omega phi := by
    apply Subtype.ext
    exact graph.trans ((congrArg (fun w => alpha • w) same.symm).trans
      (classFixed.trans same))
  have sameCharacter := congrArg Subtype.val (D.omega.injective sameImage)
  exact (characterInertia_iff root phi.val a).mpr sameCharacter

include simple nonabelian kernelTwo certificate fieldScope in
/-- Destruct the normalized packet exactly once at this original raw match.
The application constructs D internally; the source never chooses omega. -/
theorem pairWitness_of_normalized_match
    (kernel : TypeBCentralKernelBrauerInflation.Navarro232Principle 2 k)
    (sourceBlocks : PhysicalBlocks k Y)
    (principal : TypeBCentralKernelBlockSource.IsPrincipal b)
    (phi : TypeBCentralKernelInertia.BrauerFibre root b)
    (W : CharacterWeight 2 K Y)
    (same : TypeBWeightCoveringSource.rawClass W = (D.omega phi).val)
    (blocks : PairBlocks root phi.val W)
    (joins : FullCoverPairJoins Msys q fullCover kernelCenter
      root calibration phi.val W navarro) :
    Nonempty (CanonicalPairWitness Msys root calibration phi.val W
      (same_match_hUT Msys root D sourceBlocks principal phi W same) navarro blocks) := by
  obtain ⟨packet⟩ := D.packets phi W same
  exact certificate.forward Y Hhat O Msys q fullCover simple nonabelian kernelCenter
    kernelTwo root calibration phi.val W navarro
    (same_match_hUT Msys root D sourceBlocks principal phi W same)
    (same_match_product Msys root D phi W same) blocks
    (hattedCentralKernel_eq Msys q fullCover.1.1 kernelTwo kernelCenter
      root calibration phi.val kernel)
    joins packet.val packet.property fieldScope

end SamePacket

section ActualSpin

open TypeBCliffordCarriers

variable {n r f : ℕ} {F : Type} [Field F] [Finite F] [CharP F r]
  (parameters : OddFieldParameters F r f) (rank : 4 ≤ n)
  (N : NormSource n F)
  (C : TypeBCliffordOrthogonalSourceBinding.Source n F r f parameters
    (TypeBAllRankPrincipalCriterionCarriers.rank3 rank) N)
  (centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n r f F N)
  [Finite (Spin n F N)]

/-- The actual norm-kernel Spin projection, on these exact all-rank data. -/
abbrev actualProjection : Spin n F N →* TypeBAllRankPrincipalCriterionCarriers.X n F :=
  TypeBAllRankPrincipalCriterionCarriers.spinProjection parameters rank N C

include centre in
theorem actualProjection_kernelCenter :
    (actualProjection parameters rank N C).ker = Subgroup.center (Spin n F N) :=
  TypeBCliffordOrthogonalSourceBinding.spin_kernel_eq_center n F N parameters
    (TypeBAllRankPrincipalCriterionCarriers.rank3 rank) C centre

include centre in
theorem actualProjection_kernelTwo : IsPGroup 2 (actualProjection parameters rank N C).ker :=
  TypeBMatrixOmegaPrimeToTwoCover.spinProjection_kernel_isTwoGroup n F parameters
    (TypeBAllRankPrincipalCriterionCarriers.rank3 rank) N C centre

variable {k K O : Type} [Field k] [Field K] [CommRing O] [IsDomain O]
  [Algebra O K] [CharP k 2] [IsAlgClosed k] [CharZero K]
  (Msys : ModularSystem 2 K O k)
  (fullCover : IsUniversalCentralExtension (actualProjection parameters rank N C))
  (simple : IsSimpleGroup (TypeBAllRankPrincipalCriterionCarriers.X n F))
  (nonabelian : ¬ IsMulCommutative (TypeBAllRankPrincipalCriterionCarriers.X n F))
  (root : PrimeRegularRootEmbedding 2 k K (TypeBAllRankPrincipalCriterionCarriers.X n F))
  (calibration : RootResidueCompatible Msys root)
  [HasEnoughRootsOfUnity K (Nat.card (TypeBAllRankPrincipalCriterionCarriers.X n F))]
  (navarro : ∀ (H : Type) [Group H] [Finite H]
    [HasEnoughRootsOfUnity K (Nat.card H)]
    (iota : PrimeRegularRootEmbedding 2 k K H)
    (compatible : RootResidueCompatible Msys iota),
      ScopedDefectZeroReductionSource Msys iota compatible)

/-- The hatted radical is the literal full preimage in actual Spin. -/
theorem actual_hattedWeight_subgroup
    (W : CharacterWeight 2 K (TypeBAllRankPrincipalCriterionCarriers.X n F)) :
    (hattedWeight (actualProjection parameters rank N C) fullCover.1.1
      (actualProjection_kernelTwo parameters rank N C centre) W).subgroup =
        W.subgroup.comap (actualProjection parameters rank N C) := rfl

/-- The remaining data are only hatted blocks and the precise stabilizer
dictionary for this actual projection; kernel and root joins are computed. -/
abbrev ActualPairJoins (phi : IBr root)
    (W : CharacterWeight 2 K (TypeBAllRankPrincipalCriterionCarriers.X n F)) :=
  FullCoverPairJoins Msys (actualProjection parameters rank N C) fullCover
    (actualProjection_kernelCenter parameters rank N C centre)
    root calibration phi W navarro

variable (certificate : ForwardTheorem44 k K)
  (fieldScope : SpathCoefficientField 2 k Nat.prime_two)
  {R : TypeBQ3PrincipalWeightInflation.CoverWeightSource (k := k) (K := K)
    (TypeBAllRankPrincipalCriterionCarriers.X n F)}
  {b : LiteralPrimitiveBlock k (TypeBAllRankPrincipalCriterionCarriers.X n F)}
  (D : NormalizedBlockWitness Msys root R b)

include simple nonabelian certificate fieldScope in
/-- The all-rank actual wrapper derives both structural kernel facts,
the character-central quotient, and hUT internally, at the SAME raw match. -/
theorem actual_pairWitness_of_normalized_match
    (kernel : TypeBCentralKernelBrauerInflation.Navarro232Principle 2 k)
    (sourceBlocks : PhysicalBlocks k (TypeBAllRankPrincipalCriterionCarriers.X n F))
    (principal : TypeBCentralKernelBlockSource.IsPrincipal b)
    (phi : TypeBCentralKernelInertia.BrauerFibre root b)
    (W : CharacterWeight 2 K (TypeBAllRankPrincipalCriterionCarriers.X n F))
    (same : TypeBWeightCoveringSource.rawClass W = (D.omega phi).val)
    (blocks : PairBlocks root phi.val W)
    (joins : ActualPairJoins parameters rank N C centre Msys fullCover
      root calibration navarro phi.val W) :
    Nonempty (CanonicalPairWitness Msys root calibration phi.val W
      (same_match_hUT Msys root D sourceBlocks principal phi W same) navarro blocks) :=
  pairWitness_of_normalized_match Msys (actualProjection parameters rank N C) fullCover
    simple nonabelian (actualProjection_kernelCenter parameters rank N C centre)
    (actualProjection_kernelTwo parameters rank N C centre)
    root calibration navarro certificate fieldScope D kernel sourceBlocks principal
    phi W same blocks joins

end ActualSpin

end ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionSpathSource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
