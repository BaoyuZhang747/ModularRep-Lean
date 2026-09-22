import ModularRep.PaperProofs.OddTwoPrincipalFieldFixedness
import ModularRep.PaperProofs.OddTwoBroughActualTriple

/-!
# Principal ambient actions and stabilizers of conformal translates

The PCSp commutator lies in the actual PSp image and hence acts trivially
on Brauer characters. Together with the checked field fixedness on the
principal fibre, K proves that all actual ambient actions commute there.
Thus every ambient translate has the same global stabilizer. This keeps
the ORIGINAL own raw weight when the Brough theorem changes the global
character; no new character-invariance or stabilizer source is supplied.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoPrincipalAmbientOrbitStabilizers

open scoped commutatorElement

open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
open ModularRep.PaperProofs.OddTwoUniversalPrimeToTwoSelfCover
open ModularRep.PaperProofs.OddTwoCentralTwoPrincipalWeightDescent
open ModularRep.PaperProofs.OddTwoDescendedFengMalleEquivariance
open ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation
open ModularRep.PaperProofs.OddTwoPrincipalFieldFixedness
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions

universe u

variable {n : ℕ} {F k K Block J : Type u}
variable [Field F] [Fintype F] [Field k] [IsAlgClosed k] [CharP k 2]
variable [Field K] [CharZero K]
variable [MulAction (MulAut (LiteralSp n F))ᵐᵒᵖ Block]
variable [MulAction (MulAut (LiteralPSp n F))ᵐᵒᵖ J]

local instance spFintype : Fintype (LiteralSp n F) := Fintype.ofFinite _
local instance pspFintype : Fintype (LiteralPSp n F) := Fintype.ofFinite _

variable {D : PrincipalCharacterData (n := n) (F := F) (k := k) (K := K) (Block := Block)}
variable {cover : OddSymplecticFullCoverSource n F}
variable (E : PrincipalDescentData (J := J) D cover)
variable (downSupport : OperationsBrauerSupport E.iotaDown E.downInjective
  E.downSource.operations)
variable {C : CenterIntersectionSource n F} (S : BroughGroupSource C)

/-- The principal fibre action is the restriction of the exact actual
Brauer action used in the Brough tuple. -/
theorem principal_stabilizer_eq (psi : E.DownPrincipalBrauer) :
    let _ := ambientBrauerAction E downSupport S
    MulAction.stabilizer (Ambient (n := n) (F := F)) psi =
      OddTwoBroughActualTriple.globalStabilizer S E.iotaDown psi.1 := by
  dsimp only
  letI := ambientBrauerAction E downSupport S
  ext g
  change g • psi = psi ↔ MulOpposite.op (S.fullAut g⁻¹) • psi.1 = psi.1
  have hcoe : (g • psi).1 = MulOpposite.op (S.fullAut g⁻¹) • psi.1 := by
    change MulOpposite.op ((S.fullAut g)⁻¹) • psi.1 = _
    rw [map_inv]
  constructor
  · intro h
    exact hcoe.symm.trans (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext (hcoe.trans h)

/-- Inner invariance applies to the actual embedded PSp element. -/
theorem base_fixes (x : PSp n F) (psi : E.DownPrincipalBrauer) :
    let _ := ambientBrauerAction E downSupport S
    baseEmbedding C x • psi = psi := by
  dsimp only
  letI := ambientBrauerAction E downSupport S
  change baseEmbedding C x ∈ MulAction.stabilizer (Ambient (n := n) (F := F)) psi
  rw [principal_stabilizer_eq]
  exact OddTwoBroughActualTriple.base_mem_globalStabilizer S E.iotaDown psi.1 x

/-- The inherited actual derived-subgroup equality supplies the inner
element; no commutation of the matrix group itself is claimed. -/
theorem conformal_commutator_fixes (a b : PCSp n F) (psi : E.DownPrincipalBrauer) :
    let _ := ambientBrauerAction E downSupport S
    (SemidirectProduct.inl ⁅a, b⁆ : Ambient (n := n) (F := F)) • psi = psi := by
  dsimp only
  letI := ambientBrauerAction E downSupport S
  have hc : ⁅a, b⁆ ∈ (pspEmbedding C).range := by
    rw [← S.derived_image, commutator_eq_closure]
    exact Subgroup.subset_closure (commutator_mem_commutatorSet a b)
  obtain ⟨x, hx⟩ := hc
  rw [← hx]
  exact base_fixes E downSupport S x psi

theorem conformal_actions_commute (a b : PCSp n F) (psi : E.DownPrincipalBrauer) :
    let _ := ambientBrauerAction E downSupport S
    (SemidirectProduct.inl a : Ambient (n := n) (F := F)) •
        ((SemidirectProduct.inl b : Ambient (n := n) (F := F)) • psi) =
      (SemidirectProduct.inl b : Ambient (n := n) (F := F)) •
        ((SemidirectProduct.inl a : Ambient (n := n) (F := F)) • psi) := by
  dsimp only
  letI := ambientBrauerAction E downSupport S
  have hmul : (SemidirectProduct.inl a : Ambient (n := n) (F := F)) *
      SemidirectProduct.inl b =
      SemidirectProduct.inl ⁅a, b⁆ * (SemidirectProduct.inl b * SemidirectProduct.inl a) := by
    simp only [← map_mul]
    congr 1
    simp [commutatorElement_def, mul_assoc]
  calc
    _ = ((SemidirectProduct.inl a : Ambient (n := n) (F := F)) *
        SemidirectProduct.inl b) • psi := (mul_smul _ _ _).symm
    _ = (SemidirectProduct.inl ⁅a, b⁆ * (SemidirectProduct.inl b *
        SemidirectProduct.inl a) : Ambient (n := n) (F := F)) • psi := by rw [hmul]
    _ = _ := by rw [mul_smul, conformal_commutator_fixes, mul_smul]

variable (fixed : FengMalleCorollary43aSource D)

include fixed in
theorem ambient_action_eq_conformal (g : Ambient (n := n) (F := F))
    (psi : E.DownPrincipalBrauer) :
    let _ := ambientBrauerAction E downSupport S
    g • psi = (SemidirectProduct.inl g.left : Ambient (n := n) (F := F)) • psi := by
  dsimp only
  letI := ambientBrauerAction E downSupport S
  conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right g, mul_smul,
    ambientBrauer_field_fixed fixed E downSupport S]

include fixed in
theorem ambient_actions_commute (g h : Ambient (n := n) (F := F))
    (psi : E.DownPrincipalBrauer) :
    let _ := ambientBrauerAction E downSupport S
    g • (h • psi) = h • (g • psi) := by
  dsimp only
  letI := ambientBrauerAction E downSupport S
  rw [ambient_action_eq_conformal E downSupport S fixed g,
    ambient_action_eq_conformal E downSupport S fixed h psi,
    ambient_action_eq_conformal E downSupport S fixed h,
    ambient_action_eq_conformal E downSupport S fixed g psi]
  exact conformal_actions_commute E downSupport S g.left h.left psi

include fixed in
/-- The commutator condition is derived on actual principal characters. -/
theorem ambient_commutator_fixes (g h : Ambient (n := n) (F := F))
    (psi : E.DownPrincipalBrauer) :
    let _ := ambientBrauerAction E downSupport S
    ⁅g, h⁆ • psi = psi := by
  dsimp only
  letI := ambientBrauerAction E downSupport S
  simp only [commutatorElement_def, mul_smul]
  rw [ambient_actions_commute E downSupport S fixed g h]
  simp only [smul_inv_smul]

include fixed downSupport in
/-- The commutator with an actual conformal element belongs to both the
actual conformal image and the actual global Brauer stabilizer. -/
theorem commutator_mem_conformal_stabilizer
    (g : Ambient (n := n) (F := F)) (t : PCSp n F)
    (psi : E.DownPrincipalBrauer) :
    ⁅g, SemidirectProduct.inl t⁆ ∈
        (SemidirectProduct.inl (φ := pcspFieldAction (n := n) (F := F))).range ∧
      ⁅g, SemidirectProduct.inl t⁆ ∈
        OddTwoBroughActualTriple.globalStabilizer S E.iotaDown psi.1 := by
  letI := ambientBrauerAction E downSupport S
  constructor
  · have hr : (⁅g, SemidirectProduct.inl t⁆ : Ambient (n := n) (F := F)).right = 1 := by
      simp [commutatorElement_def]
    refine ⟨(⁅g, SemidirectProduct.inl t⁆ : Ambient (n := n) (F := F)).left, ?_⟩
    apply SemidirectProduct.ext
    · rfl
    · exact hr.symm
  · rw [← principal_stabilizer_eq E downSupport S]
    exact ambient_commutator_fixes E downSupport S fixed g _ psi

include fixed in
/-- Stabilizer equality applies to EVERY ambient translate of the global
character. The selected own raw weight is not changed here. -/
theorem translated_stabilizer_eq (h : Ambient (n := n) (F := F))
    (psi : E.DownPrincipalBrauer) :
    let _ := ambientBrauerAction E downSupport S
    MulAction.stabilizer (Ambient (n := n) (F := F)) (h • psi) =
      MulAction.stabilizer (Ambient (n := n) (F := F)) psi := by
  dsimp only
  letI := ambientBrauerAction E downSupport S
  ext g
  change g • (h • psi) = h • psi ↔ g • psi = psi
  rw [ambient_actions_commute E downSupport S fixed]
  exact (MulAction.injective h).eq_iff

include fixed in
theorem actual_global_stabilizer_translate (h : Ambient (n := n) (F := F))
    (psi : E.DownPrincipalBrauer) :
    let _ := ambientBrauerAction E downSupport S
    OddTwoBroughActualTriple.globalStabilizer S E.iotaDown (h • psi).1 =
      OddTwoBroughActualTriple.globalStabilizer S E.iotaDown psi.1 := by
  dsimp only
  letI := ambientBrauerAction E downSupport S
  rw [← principal_stabilizer_eq E downSupport S,
    ← principal_stabilizer_eq E downSupport S,
    translated_stabilizer_eq E downSupport S fixed]

include fixed in
/-- The SAME arbitrary raw stabilizer remains contained after translating
the global character, provided its original actual containment is known. -/
theorem raw_containment_translate (h : Ambient (n := n) (F := F))
    (psi : E.DownPrincipalBrauer) (W : CharacterWeight 2 K (PSp n F))
    (contained : OddTwoBroughActualTriple.rawStabilizer S W ≤
      OddTwoBroughActualTriple.globalStabilizer S E.iotaDown psi.1) :
    let _ := ambientBrauerAction E downSupport S
    OddTwoBroughActualTriple.rawStabilizer S W ≤
      OddTwoBroughActualTriple.globalStabilizer S E.iotaDown (h • psi).1 := by
  dsimp only
  rw [actual_global_stabilizer_translate E downSupport S fixed]
  exact contained

end ModularRep.PaperProofs.OddTwoPrincipalAmbientOrbitStabilizers


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
