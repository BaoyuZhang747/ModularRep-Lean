import ModularRep.PaperProofs.OddTwoBroughActualTriple
import ModularRep.PaperProofs.OddTwoActualSemidirectQuotient
import ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate

/-!
# Actual ambient-group identifications for the Brough butterfly step

The map from the literal PSp holomorph to the literal PCSp/field ambient
group is computed from their fixed natural automorphism maps. Its
surjectivity, the base and conjugation squares, the actual Brauer/raw action
agreements, and both stabilizer preimages are K theorems.

The two global stabilizers induce exactly the same subgroup of Aut(PSp).
The inverse image of the Brough local subgroup's actual conjugation image
is precisely the holomorph's local subgroup for the SAME raw pair. Local
subgroups remain intersections with their actual global stabilizers; no
chosen-raw-pair fixation follows merely from conjugacy class fixation.

No image equality, alternate ambient group, relation-preservation field,
or block-triple conclusion is a source input. This module establishes the
group hypotheses used by MRR Lemma 3.11 / Spath Theorem 3.5(b), without
invoking either relation theorem. The characters and roots are those of
the two existing actual tuple constructors.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoBroughButterflyGroups

open Formalisation
open ModularRep.CharacterWeight
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation
open ModularRep.PaperProofs.OddTwoActualSemidirectQuotient (Holomorph brauerAutStabilizer)

universe u

variable {n : ℕ} {F k K : Type u}
variable [Field F] [Finite F] [Field k] [IsAlgClosed k] [CharP k 2]
variable [Field K] [CharZero K]

local instance fieldAutFinite : Finite (F ≃+* F) :=
  Finite.of_injective (fun a : F ≃+* F => (a : F → F)) DFunLike.coe_injective

local instance groupAutFinite (G : Type u) [Group G] [Finite G] : Finite (MulAut G) :=
  Finite.of_injective (fun a : MulAut G => (a : G → G)) DFunLike.coe_injective

local instance ambientFinite : Finite (Ambient (n := n) (F := F)) :=
  Finite.of_equiv (PCSp n F × (F ≃+* F)) SemidirectProduct.equivProd.symm

local instance groupFintype (G : Type u) [Group G] [Finite G] : Fintype G :=
  Fintype.ofFinite G

variable {C : CenterIntersectionSource n F} (S : BroughGroupSource C)

/-- The natural conjugation map of the literal PSp holomorph. -/
def holomorphAction : Holomorph (PSp n F) →* MulAut (PSp n F) :=
  semidirectToMulAut (MonoidHom.id (MulAut (PSp n F)))

@[simp] theorem holomorphAction_inl (x : PSp n F) :
    holomorphAction (SemidirectProduct.inl x) = MulAut.conj x :=
  semidirectToMulAut_inl _ x

@[simp] theorem holomorphAction_inr (a : MulAut (PSp n F)) :
    holomorphAction (SemidirectProduct.inr a) = a :=
  semidirectToMulAut_inr _ a

theorem holomorphAction_surjective :
    Function.Surjective (holomorphAction (n := n) (F := F)) := by
  intro a
  exact ⟨SemidirectProduct.inr a, holomorphAction_inr a⟩

/-- The fixed comparison map: the inverse of the actual Brough natural
automorphism identification, composed with actual holomorph conjugation. -/
def toBrough : Holomorph (PSp n F) →* Ambient (n := n) (F := F) :=
  S.fullAut.symm.toMonoidHom.comp holomorphAction

@[simp] theorem fullAut_toBrough (d : Holomorph (PSp n F)) :
    S.fullAut (toBrough S d) = holomorphAction d :=
  S.fullAut.apply_symm_apply _

theorem toBrough_surjective : Function.Surjective (toBrough S) :=
  S.fullAut.symm.surjective.comp holomorphAction_surjective

@[simp] theorem toBrough_inl (x : PSp n F) :
    toBrough S (SemidirectProduct.inl x) = baseEmbedding C x := by
  apply S.fullAut.injective
  rw [fullAut_toBrough, holomorphAction_inl, OddTwoBroughActualTriple.fullAut_base]

/-- The inverse/opposite action convention commutes with the actual map. -/
theorem inverseOp_toBrough (d : Holomorph (PSp n F)) :
    inverseOpHom S.fullAut.toMonoidHom (toBrough S d) =
      inverseOpHom holomorphAction d := by
  change MulOpposite.op (S.fullAut ((toBrough S d)⁻¹)) =
    MulOpposite.op (holomorphAction d⁻¹)
  rw [← (toBrough S).map_inv, fullAut_toBrough]

/-- This is the actual conjugation formula on the holomorph's base. -/
theorem holomorphAction_conjugate (d : Holomorph (PSp n F)) (x : PSp n F) :
    (SemidirectProduct.inl (holomorphAction d x) : Holomorph (PSp n F)) =
      d * SemidirectProduct.inl x * d⁻¹ := by
  have hd : holomorphAction d = MulAut.conj d.left * d.right := by
    calc
      holomorphAction d = holomorphAction
          (SemidirectProduct.inl d.left * SemidirectProduct.inr d.right) :=
        congrArg holomorphAction (SemidirectProduct.inl_left_mul_inr_right d).symm
      _ = MulAut.conj d.left * d.right := by
        rw [map_mul, holomorphAction_inl, holomorphAction_inr]
  apply SemidirectProduct.ext
  · rw [hd]
    simp [MulAut.conj_apply, mul_assoc]
  · simp

variable (iota : PrimeRegularRootEmbedding 2 k K (PSp n F))

/-- The actual holomorph and Brough Brauer actions agree on every character. -/
theorem brauer_action_agreement (d : Holomorph (PSp n F)) (psi : IBr iota) :
    let _ := OddTwoActualStabilizerTriple.actualBrauerAction iota
      (MonoidHom.id (MulAut (PSp n F)))
    let _ := OddTwoBroughActualTriple.actualBrauerAction S iota
    d • psi = toBrough S d • psi := by
  dsimp only
  letI := OddTwoActualStabilizerTriple.actualBrauerAction iota
    (MonoidHom.id (MulAut (PSp n F)))
  letI := OddTwoBroughActualTriple.actualBrauerAction S iota
  calc
    d • psi = inverseOpHom holomorphAction d • psi :=
      EvenFieldFLZ318FixedTheoremGate.semidirectRightAction_smul_eq
        (MonoidHom.id (MulAut (PSp n F))) d psi
    _ = toBrough S d • psi := by
      change _ = inverseOpHom S.fullAut.toMonoidHom (toBrough S d) • psi
      rw [inverseOp_toBrough]

/-- The same equality holds on the own raw-pair IsoClass carrier, before
passing to ambient conjugacy classes. -/
theorem raw_action_agreement (d : Holomorph (PSp n F))
    (r : RawWeightClass (p := 2) (K := K) (H := PSp n F)) :
    let _ := canonicalRawSemidirectAction (p := 2) (K := K)
      (MonoidHom.id (MulAut (PSp n F)))
    let _ := OddTwoBroughActualTriple.actualRawAction (K := K) S
    d • r = toBrough S d • r := by
  dsimp only
  letI := canonicalRawSemidirectAction (p := 2) (K := K)
    (MonoidHom.id (MulAut (PSp n F)))
  letI := OddTwoBroughActualTriple.actualRawAction (K := K) S
  calc
    d • r = inverseOpHom holomorphAction d • r :=
      EvenFieldFLZ318FixedTheoremGate.semidirectRightAction_smul_eq
        (MonoidHom.id (MulAut (PSp n F))) d r
    _ = toBrough S d • r := by
      change _ = inverseOpHom S.fullAut.toMonoidHom (toBrough S d) • r
      rw [inverseOp_toBrough]

variable (psi : IBr iota)

/-- An abbreviation for the already constructed actual holomorph tuple group. -/
abbrev holGlobal : Subgroup (Holomorph (PSp n F)) :=
  OddTwoActualStabilizerTriple.globalStabilizer iota
    (MonoidHom.id (MulAut (PSp n F))) psi

/-- The global stabilizer equality is proved from the literal actions. -/
theorem global_preimage :
    (OddTwoBroughActualTriple.globalStabilizer S iota psi).comap (toBrough S) =
      holGlobal iota psi := by
  ext d
  letI := OddTwoActualStabilizerTriple.actualBrauerAction iota
    (MonoidHom.id (MulAut (PSp n F)))
  letI := OddTwoBroughActualTriple.actualBrauerAction S iota
  change toBrough S d • psi = psi ↔ d • psi = psi
  rw [brauer_action_agreement S iota]

theorem raw_preimage (W : CharacterWeight 2 K (PSp n F)) :
    (OddTwoBroughActualTriple.rawStabilizer S W).comap (toBrough S) =
      OddTwoActualStabilizerTriple.rawStabilizer
        (MonoidHom.id (MulAut (PSp n F))) W := by
  ext d
  letI := canonicalRawSemidirectAction (p := 2) (K := K)
    (MonoidHom.id (MulAut (PSp n F)))
  letI := OddTwoBroughActualTriple.actualRawAction (K := K) S
  change toBrough S d • (Quotient.mk'' W : RawWeightClass (p := 2) (K := K)
    (H := PSp n F)) = _ ↔ d • (Quotient.mk'' W : RawWeightClass (p := 2) (K := K)
    (H := PSp n F)) = _
  rw [raw_action_agreement S]

/-- Restriction of the fixed ambient map to the actual global stabilizers. -/
def globalMap : holGlobal iota psi →*
    OddTwoBroughActualTriple.globalStabilizer S iota psi where
  toFun d := ⟨toBrough S d.1, by
    change d.1 ∈ (OddTwoBroughActualTriple.globalStabilizer S iota psi).comap
      (toBrough S)
    exact Eq.mp (congrArg (fun U : Subgroup (Holomorph (PSp n F)) => d.1 ∈ U)
      (global_preimage S iota psi).symm) d.2⟩
  map_one' := Subtype.ext (map_one (toBrough S))
  map_mul' d e := Subtype.ext (map_mul (toBrough S) d.1 e.1)

@[simp] theorem globalMap_ambient (d : holGlobal iota psi) :
    (globalMap S iota psi d).1 = toBrough S d.1 := rfl

theorem globalMap_surjective : Function.Surjective (globalMap S iota psi) := by
  intro a
  obtain ⟨d, hd⟩ := toBrough_surjective S a.1
  have hm : d ∈ holGlobal iota psi := by
    rw [← global_preimage S iota psi]
    change toBrough S d ∈ OddTwoBroughActualTriple.globalStabilizer S iota psi
    rw [hd]
    exact a.2
  exact ⟨⟨d, hm⟩, Subtype.ext hd⟩

/-- The restricted map retains the actual base embedding. -/
theorem globalMap_base (x : PSp n F) :
    globalMap S iota psi (OddTwoActualStabilizerTriple.baseInclusion iota
      (MonoidHom.id (MulAut (PSp n F))) psi x) =
        OddTwoBroughActualTriple.baseInclusion S iota psi x :=
  Subtype.ext (toBrough_inl S x)

/-- The two natural conjugation maps, written on the same literal PSp. -/
def holConjugation : holGlobal iota psi →* MulAut (PSp n F) :=
  holomorphAction.comp (holGlobal iota psi).subtype

def broughConjugation : OddTwoBroughActualTriple.globalStabilizer S iota psi →*
    MulAut (PSp n F) :=
  S.fullAut.toMonoidHom.comp (OddTwoBroughActualTriple.globalStabilizer S iota psi).subtype

theorem broughConjugation_injective : Function.Injective (broughConjugation S iota psi) :=
  S.fullAut.injective.comp Subtype.val_injective

@[simp] theorem conjugation_square (d : holGlobal iota psi) :
    broughConjugation S iota psi (globalMap S iota psi d) = holConjugation iota psi d :=
  fullAut_toBrough S d.1

/-- This value equation authenticates holConjugation as actual conjugation
on the computed normal base, not merely a named action map. -/
theorem holConjugation_base (d : holGlobal iota psi) (x : PSp n F) :
    OddTwoActualStabilizerTriple.baseInclusion iota
      (MonoidHom.id (MulAut (PSp n F))) psi (holConjugation iota psi d x) =
        d * OddTwoActualStabilizerTriple.baseInclusion iota
          (MonoidHom.id (MulAut (PSp n F))) psi x * d⁻¹ :=
  Subtype.ext (holomorphAction_conjugate d.1 x)

/-- The analogous value equation uses the actual proper PSp base in A. -/
theorem broughConjugation_base
    (a : OddTwoBroughActualTriple.globalStabilizer S iota psi) (x : PSp n F) :
    OddTwoBroughActualTriple.baseInclusion S iota psi
      (broughConjugation S iota psi a x) =
        a * OddTwoBroughActualTriple.baseInclusion S iota psi x * a⁻¹ :=
  Subtype.ext (OddTwoBroughActualTriple.baseEmbedding_conjugate S a.1 x)

theorem mem_broughGlobal_iff (a : Ambient (n := n) (F := F)) :
    a ∈ OddTwoBroughActualTriple.globalStabilizer S iota psi ↔
      S.fullAut a ∈ brauerAutStabilizer iota psi := by
  change MulOpposite.op (S.fullAut a⁻¹) • psi = psi ↔
    MulOpposite.op ((S.fullAut a)⁻¹) • psi = psi
  rw [map_inv]

/-- Both ranges are exactly the actual Brauer automorphism stabilizer. -/
theorem broughConjugation_range :
    (broughConjugation S iota psi).range = brauerAutStabilizer iota psi := by
  ext a
  constructor
  · rintro ⟨g, rfl⟩
    exact (mem_broughGlobal_iff S iota psi g.1).mp g.2
  · intro ha
    have hg : S.fullAut.symm a ∈ OddTwoBroughActualTriple.globalStabilizer S iota psi := by
      rw [mem_broughGlobal_iff, S.fullAut.apply_symm_apply]
      exact ha
    exact ⟨⟨S.fullAut.symm a, hg⟩, S.fullAut.apply_symm_apply a⟩

theorem conjugation_ranges :
    (holConjugation iota psi).range = (broughConjugation S iota psi).range := by
  ext a
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨globalMap S iota psi g, conjugation_square S iota psi g⟩
  · rintro ⟨g, rfl⟩
    obtain ⟨d, rfl⟩ := globalMap_surjective S iota psi g
    exact ⟨d, (conjugation_square S iota psi d).symm⟩

include S in
theorem holConjugation_range :
    (holConjugation iota psi).range = brauerAutStabilizer iota psi := by
  rw [conjugation_ranges S, broughConjugation_range]

variable (W : CharacterWeight 2 K (PSp n F))

/-- The concrete inverse-image equality for the SAME own raw weight.
Each side is its intersection with the appropriate global stabilizer. -/
theorem local_preimage :
    (OddTwoBroughActualTriple.localSubgroup S iota psi W).comap (globalMap S iota psi) =
      OddTwoActualStabilizerTriple.localSubgroup iota
        (MonoidHom.id (MulAut (PSp n F))) psi W := by
  ext d
  change toBrough S d.1 ∈ OddTwoBroughActualTriple.rawStabilizer S W ↔
    d.1 ∈ OddTwoActualStabilizerTriple.rawStabilizer
      (MonoidHom.id (MulAut (PSp n F))) W
  change d.1 ∈ (OddTwoBroughActualTriple.rawStabilizer S W).comap (toBrough S) ↔ _
  rw [raw_preimage S]

/-- Precisely the local inverse-image hypothesis of the butterfly theorem,
on the actual natural conjugation maps and the actual computed subgroups. -/
theorem local_conjugation_image_preimage :
    ((OddTwoBroughActualTriple.localSubgroup S iota psi W).map
      (broughConjugation S iota psi)).comap (holConjugation iota psi) =
        OddTwoActualStabilizerTriple.localSubgroup iota
          (MonoidHom.id (MulAut (PSp n F))) psi W := by
  ext d
  rw [← local_preimage S iota psi W]
  change holConjugation iota psi d ∈
      (OddTwoBroughActualTriple.localSubgroup S iota psi W).map
        (broughConjugation S iota psi) ↔
    globalMap S iota psi d ∈ OddTwoBroughActualTriple.localSubgroup S iota psi W
  constructor
  · rintro ⟨a, ha, heq⟩
    have hag : a = globalMap S iota psi d :=
      broughConjugation_injective S iota psi
        (heq.trans (conjugation_square S iota psi d).symm)
    exact hag ▸ ha
  · intro hd
    exact ⟨globalMap S iota psi d, hd, conjugation_square S iota psi d⟩

/-- The same inverse-image map agrees with both previously computed own
normalizer identifications, including their actual ambient inclusions. -/
theorem globalMap_normalizer
    (x : Subgroup.normalizer (W.subgroup : Set (PSp n F))) :
    globalMap S iota psi
      (OddTwoActualStabilizerTriple.normalizerEquivIntersection iota
        (MonoidHom.id (MulAut (PSp n F))) psi W x).1 =
      (OddTwoBroughActualTriple.normalizerEquivIntersection S iota psi W x).1 :=
  Subtype.ext (toBrough_inl S x.1)

end ModularRep.PaperProofs.OddTwoBroughButterflyGroups


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
