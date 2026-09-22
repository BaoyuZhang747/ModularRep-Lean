import ModularRep.PaperProofs.OddTwoActualStabilizerTriple
import ModularRep.PaperProofs.OddTwoActualSemidirectQuotient

/-!
# Actual quotient-image groups for the upward central-two triple passage

The global character downstairs is arbitrary and the raw weight upstairs
is retained unchanged. The global character upstairs and the raw weight
downstairs are the existing computed inflations/quotients. All maps and
subgroup equivalences below come from the same actual stabilizer projection.
There is no matching relation, replacement weight or freely supplied group
equivalence. The local groups are intersections; full raw containment is a
separate obligation of the later Definition 3.5 consumer.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoActualCentralInflationGroups

open ModularRep
open ModularRep.CharacterWeight
open ModularRep.PaperProofs.OddTwoActualStabilizerTriple
open ModularRep.PaperProofs.OddTwoActualSemidirectQuotient
open ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation
open ModularRep.PaperProofs.OddTwoProjectiveAutomorphismDiagonalJoin
open ModularRep.PaperProofs.OddTwoCentralTwoGlobalInflation
open ModularRep.PaperProofs.OddTwoCentralTwoWeightInflation
open ModularRep.PaperProofs.OddTwoCentralTwoRelationInflation
open ModularRep.PaperProofs.OddTwoUniversalPrimeToTwoSelfCover

universe u

section QuotientImages

variable {A B : Type u} [Group A] [Group B]

/-- Restrict the canonical first-isomorphism-theorem equivalence to the
actual image of a subgroup which is the full preimage of V. -/
def quotientImageEquiv (f : A →* B) (hf : Function.Surjective f)
    (U : Subgroup A) (V : Subgroup B) (hU : V.comap f = U) :
    U.map (QuotientGroup.mk' f.ker) ≃* V := by
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  have hmap : (U.map (QuotientGroup.mk' f.ker)).map e.toMonoidHom = V := by
    rw [Subgroup.map_map]
    have hcomp : e.toMonoidHom.comp (QuotientGroup.mk' f.ker) = f := by
      ext a
      rfl
    rw [hcomp, ← hU]
    exact Subgroup.map_comap_eq_self_of_surjective hf V
  exact (e.subgroupMap (U.map (QuotientGroup.mk' f.ker))).trans
    (MulEquiv.subgroupCongr hmap)

@[simp] theorem quotientImageEquiv_apply_coe
    (f : A →* B) (hf : Function.Surjective f)
    (U : Subgroup A) (V : Subgroup B) (hU : V.comap f = U)
    (x : U.map (QuotientGroup.mk' f.ker)) :
    (quotientImageEquiv f hf U V hU x : B) =
      QuotientGroup.quotientKerEquivOfSurjective f hf x := rfl

@[simp] theorem quotientImageEquiv_symm_apply_coe
    (f : A →* B) (hf : Function.Surjective f)
    (U : Subgroup A) (V : Subgroup B) (hU : V.comap f = U)
    (x : V) :
    ((quotientImageEquiv f hf U V hU).symm x : A ⧸ f.ker) =
      (QuotientGroup.quotientKerEquivOfSurjective f hf).symm x := rfl

end QuotientImages

section ActualStabilizers

variable {n : ℕ} {F k K : Type u}
variable [Field F] [Fintype F] [Field k] [Field K]
variable [CharP k 2] [IsAlgClosed k] [CharZero K]
variable {iotaUp : PrimeRegularRootEmbedding 2 k K (Sp n F)}
variable {iotaDown : PrimeRegularRootEmbedding 2 k K (PSp n F)}
variable (B : BrauerInflationSources iotaUp iotaDown)
variable (cover : OddSymplecticFullCoverSource n F)
variable (L : FullCoverAutomorphismLiftingSource (n := n) (F := F))
variable (T : ActualQuotientNaturality (K := K) (spProjection n F)
  cover.fullCover.1.1 cover.projection_twoKernel)
variable (psi : IBr iotaDown) (W : CharacterWeight 2 K (Sp n F))

local instance spFintype : Fintype (Sp n F) := Fintype.ofFinite _
local instance pspFintype : Fintype (PSp n F) := Fintype.ofFinite _

local notation "psiUp" => B.brauerEquiv cover psi
local notation "Wdown" => spQuotientPair cover W
local notation "upAction" => MonoidHom.id (MulAut (Sp n F))
local notation "downAction" => MonoidHom.id (MulAut (PSp n F))

/-- The existing stabilizer projection, with the actual triple's stabilizer
types exposed in its signature. Its underlying ambient map is unchanged. -/
def actualStabilizerProjection :
    globalStabilizer iotaUp upAction psiUp →*
      globalStabilizer iotaDown downAction psi where
  toFun d := ⟨projection d.1, (brauerStabilizerProjection B cover psi d).2⟩
  map_one' := Subtype.ext (map_one projection)
  map_mul' d e := Subtype.ext (map_mul projection d.1 e.1)

@[simp] theorem actualStabilizerProjection_coe
    (d : globalStabilizer iotaUp upAction psiUp) :
    (actualStabilizerProjection B cover psi d : Holomorph (PSp n F)) =
      projection d.1 := rfl

include L in
theorem actualStabilizerProjection_surjective :
    Function.Surjective (actualStabilizerProjection B cover psi) :=
  brauerStabilizerProjection_surjective B cover L psi

/-- The same projection with the constructed tuple's group instance
exposed. Its kernel therefore carries the exact instance required by
QuotientInflationData, without a new normality hypothesis. -/
def argumentsProjection (Rup : OwnNormalizerReduction (k := k) W) :
    (arguments iotaUp upAction psiUp W Rup).G →*
      globalStabilizer iotaDown downAction psi :=
  actualStabilizerProjection B cover psi

local notation "piStab" => actualStabilizerProjection B cover psi
local notation "Nu" => baseSubgroup iotaUp upAction psiUp
local notation "Nd" => baseSubgroup iotaDown downAction psi
local notation "Hu" => localSubgroup iotaUp upAction psiUp W
local notation "Hd" => localSubgroup iotaDown downAction psi Wdown
local notation "qStab" => QuotientGroup.mk'
  (MonoidHom.ker (actualStabilizerProjection B cover psi))

include L in
/-- Base membership is exactly the right coordinate being one, and the
actual projective automorphism map is injective on the full cover. -/
theorem base_preimage : (Nd).comap piStab = Nu := by
  ext d
  change projectiveAutHom d.1.right = 1 ↔ d.1.right = 1
  constructor
  · intro h
    exact (L.bijective_on_full_cover cover).1
      (h.trans projectiveAutHom.map_one.symm)
  · intro h
    rw [h, map_one]

include T in
/-- The local intersection retains the OWN quotient pair of W. -/
theorem local_preimage : (Hd).comap piStab = Hu :=
  localPairStabilizer_preimage B cover T psi W

include L T in
theorem intersection_preimage : (Nd ⊓ Hd).comap piStab = Nu ⊓ Hu := by
  rw [Subgroup.comap_inf, base_preimage B cover L psi,
    local_preimage B cover T psi W]

include L T in
/-- The actual normal kernel lies in the actual base/local intersection;
no assertion about the full raw stabilizer is required here. -/
theorem kernel_le_intersection : (piStab).ker ≤ Nu ⊓ Hu := by
  rw [← intersection_preimage B cover L T psi W]
  exact Subgroup.ker_le_comap piStab _

include L in
theorem kernel_eq_embeddedCenter :
    (piStab).ker = embeddedCenter.subgroupOf
      (globalStabilizer iotaUp upAction psiUp) :=
  brauerStabilizerProjection_kernel B cover L psi

include L T in
/-- The image of the actual intersection is the intersection of the
actual quotient images. -/
theorem quotient_intersection :
    (Nu ⊓ Hu).map qStab = (Nu).map qStab ⊓ (Hu).map qStab := by
  apply Subgroup.comap_injective (QuotientGroup.mk'_surjective (piStab).ker)
  have hker : (qStab).ker ≤ Nu ⊓ Hu := by
    simpa only [QuotientGroup.ker_mk'] using
      kernel_le_intersection B cover L T psi W
  rw [Subgroup.comap_map_eq_self hker, Subgroup.comap_inf,
    Subgroup.comap_map_eq_self (hker.trans inf_le_left),
    Subgroup.comap_map_eq_self (hker.trans inf_le_right)]

/-- The canonical equivalence on the whole actual stabilizer quotient. -/
def quotientStabilizerEquiv :
    globalStabilizer iotaUp upAction psiUp ⧸ (piStab).ker ≃*
      globalStabilizer iotaDown downAction psi :=
  QuotientGroup.quotientKerEquivOfSurjective piStab
    (actualStabilizerProjection_surjective B cover L psi)

@[simp] theorem quotientStabilizerEquiv_mk
    (d : globalStabilizer iotaUp upAction psiUp) :
    quotientStabilizerEquiv B cover L psi (qStab d) = piStab d := rfl

/-- PSp identified with the actual quotient image of the upstairs base. -/
def baseImageEquiv : PSp n F ≃* (Nu).map qStab :=
  (baseEquiv iotaDown downAction psi).trans
    (quotientImageEquiv piStab (actualStabilizerProjection_surjective B cover L psi)
      Nu Nd (base_preimage B cover L psi)).symm

@[simp] theorem baseImageEquiv_coe (g : PSp n F) :
    (baseImageEquiv B cover L psi g :
      globalStabilizer iotaUp upAction psiUp ⧸ (piStab).ker) =
      (quotientStabilizerEquiv B cover L psi).symm
        (baseEquiv iotaDown downAction psi g) := rfl

set_option maxHeartbeats 1000000 in
/-- The base square is the literal Sp projection on the left coordinate. -/
theorem baseImageEquiv_projection (g : Sp n F) :
    baseImageEquiv B cover L psi (spProjection n F g) =
      (qStab).subgroupMap Nu (baseEquiv iotaUp upAction psiUp g) := by
  apply Subtype.ext
  refine (baseImageEquiv_coe B cover L psi (spProjection n F g)).trans ?_
  apply (quotientStabilizerEquiv B cover L psi).injective
  change (quotientStabilizerEquiv B cover L psi)
      ((quotientStabilizerEquiv B cover L psi).symm
        (baseEquiv iotaDown downAction psi (spProjection n F g))) =
    (quotientStabilizerEquiv B cover L psi)
      (qStab (baseEquiv iotaUp upAction psiUp g))
  rw [MulEquiv.apply_symm_apply, quotientStabilizerEquiv_mk]
  apply Subtype.ext
  apply SemidirectProduct.ext
  · rfl
  · exact projectiveAutHom.map_one.symm

/-- The OWN downstairs normalizer identified with the actual quotient
image of the upstairs base/local intersection. -/
def normalizerImageEquiv :
    Subgroup.normalizer ((Wdown).subgroup : Set (PSp n F)) ≃*
      ↥((Nu).map qStab ⊓ (Hu).map qStab) :=
  ((normalizerEquivIntersection iotaDown downAction psi Wdown).trans
    (quotientImageEquiv piStab (actualStabilizerProjection_surjective B cover L psi)
      (Nu ⊓ Hu) (Nd ⊓ Hd) (intersection_preimage B cover L T psi W)).symm).trans
    (MulEquiv.subgroupCongr (quotient_intersection B cover L T psi W))

@[simp] theorem normalizerImageEquiv_coe
    (x : Subgroup.normalizer ((Wdown).subgroup : Set (PSp n F))) :
    (normalizerImageEquiv B cover L T psi W x :
      globalStabilizer iotaUp upAction psiUp ⧸ (piStab).ker) =
      (quotientStabilizerEquiv B cover L psi).symm
        (normalizerEquivIntersection iotaDown downAction psi Wdown x) := rfl

set_option maxHeartbeats 1000000 in
/-- The local square is the actual normalizer map of the fixed projection.
The target is the same subgroup used by QuotientInflationData. -/
theorem normalizerImageEquiv_projection
    (Rup : OwnNormalizerReduction (k := k) W)
    (x : Subgroup.normalizer (W.subgroup : Set (Sp n F))) :
    normalizerImageEquiv B cover L T psi W
      (normalizerMap (spProjection n F) W.subgroup x) =
      (arguments iotaUp upAction psiUp W Rup).localProjection
        (argumentsProjection B cover psi W Rup).ker
        (normalizerEquivIntersection iotaUp upAction psiUp W x) := by
  apply Subtype.ext
  refine (normalizerImageEquiv_coe B cover L T psi W
    (normalizerMap (spProjection n F) W.subgroup x)).trans ?_
  apply (quotientStabilizerEquiv B cover L psi).injective
  change (quotientStabilizerEquiv B cover L psi)
      ((quotientStabilizerEquiv B cover L psi).symm
        (normalizerEquivIntersection iotaDown downAction psi Wdown
          (normalizerMap (spProjection n F) W.subgroup x))) =
    (quotientStabilizerEquiv B cover L psi)
      (qStab (normalizerEquivIntersection iotaUp upAction psiUp W x))
  rw [MulEquiv.apply_symm_apply, quotientStabilizerEquiv_mk]
  apply Subtype.ext
  apply SemidirectProduct.ext
  · rfl
  · exact projectiveAutHom.map_one.symm

end ActualStabilizers

end ModularRep.PaperProofs.OddTwoActualCentralInflationGroups


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
