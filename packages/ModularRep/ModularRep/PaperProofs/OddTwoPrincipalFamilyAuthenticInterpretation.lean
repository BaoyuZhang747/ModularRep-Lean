import ModularRep.PaperProofs.OddTwoPrincipalFamilyFibreActions
import ModularRep.PaperProofs.OddTwoPrincipalFamilyOwnRoots
import ModularRep.PaperProofs.OddTwoActingGroupTupleTransport
import ModularRep.PaperProofs.OddTwoGroupEquivTupleTransport
import ModularRep.PaperProofs.OddTwoPrincipalDefinition35Covariance
import ModularRep.PaperProofs.OddTwoFLZ57LiteralMapSource

/-!
# The fixed Full-H_G meaning on every intrinsic selected-root packet

The intrinsic predicate is exactly FibreActions.intrinsicSource: the fixed
family predicate pulled back through the two computed inverse fibre maps.
Every supplied intrinsic own-root packet is pulled back to the SAME fixed
family pair, including its exact stored quotient reduction. Three actual
tuple changes then identify both full raw containment and the standard
relation: the family acting presentation, the routed group equivalence,
and the computed whole-pair inner correction.

The final constructor consumes the EXISTING FullHG.definition35_iff and
its SAME standard predicate. No additional intrinsic meaning, favourable
root packet, common-table convention, relation truth, covariance or seed
is an input. The universal standard coordinate-transport source retains
its existing definition-interpretation scope.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoPrincipalFamilyAuthenticInterpretation

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
open ModularRep.PaperProofs.EvenFieldFLZFullHG
open ModularRep.PaperProofs.OddTwoJordanLabelAndSeedTransport
open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
open ModularRep.PaperProofs.OddTwoTypeASourceJoin
open ModularRep.PaperProofs.OddTwoGroupEquivWeightBlocks
open ModularRep.PaperProofs.OddTwoPrincipalFamilyCharacterData
open ModularRep.PaperProofs.OddTwoPrincipalFamilyAutomorphisms
open ModularRep.PaperProofs.OddTwoPrincipalFamilySelectedReduction
open ModularRep.PaperProofs.OddTwoPrincipalFamilyOwnRoots
open ModularRep.PaperProofs.OddTwoPrincipalFamilyFibreActions
open ModularRep.PaperProofs.OddTwoDefinition35OwnReduction
open ModularRep.PaperProofs.OddTwoActualStabilizerTriple
open ModularRep.PaperProofs.OddTwoActualLocalBlockSupport
open ModularRep.PaperProofs.OddTwoActualCentralInflationPacket
open ModularRep.PaperProofs.OddTwoGroupEquivOwnReduction
open ModularRep.PaperProofs.OddTwoSelectedWeightAutomorphismCoordinates
open ModularRep.PaperProofs.OddTwoOwnCharacterAutomorphismTransport
open ModularRep.PaperProofs.OddTwoStandardBlockTripleTransport
open ModularRep.PaperProofs.OddTwoCentralTwoRelationInflation
open ModularRep.PaperProofs.OddTwoPrincipalDefinition35Covariance
open ModularRep.PaperProofs.OddTwoFLZ57LiteralMapSource

-- The authentic Full-H_G presentation is in Type. This does not restrict
-- its finite group/field class and does not rebuild the accepted universe.
variable {rank : ℕ} {F : Type} [Field F] [Fintype F]

local instance meaningSpFintype : Fintype (Sp rank F) := Fintype.ofFinite _
local instance meaningAutFinite (G : Type) [Group G] [Finite G] : Finite (MulAut G) :=
  Finite.of_injective (fun a : MulAut G => (a : G → G)) DFunLike.coe_injective

section FamilyCoordinates

variable (family : Definition35Family.{0} 2) (block : family.Block)
variable (carrier : OddSymplecticPrincipalCarrier (family.problem block) rank F)
variable (input : TypeAInputSemantics family)
variable (OH : LocalBlockInductionOperations
  (p := 2) (k := family.k) (K := family.K) (G := Sp rank F) (Block := family.Block))
variable (dictionary : PrimitiveDictionary family.blockSource.operations OH
  (groupEquiv family block carrier))

/-- The inverse fibre image maps back to the ORIGINAL intrinsic character.
This is the actual character map and its inverse law, not a value premise. -/
theorem inverseBrauer_character
    (psi : Definition35Brauer (intrinsicProblem family block carrier input OH dictionary
      (selectedReduction family block carrier input OH dictionary))) :
    IrreducibleBrauerCharacter.equivAlongMulEquiv family.iota
      (groupEquiv family block carrier)
      (((toIntrinsicBrauer family block carrier input OH dictionary
        (selectedReduction family block carrier input OH dictionary)).symm psi).1 :
          IBr family.iota) = psi.1 := by
  let E := toIntrinsicBrauer family block carrier input OH dictionary
    (selectedReduction family block carrier input OH dictionary)
  exact (toIntrinsicBrauer_character family block carrier input OH dictionary
    (selectedReduction family block carrier input OH dictionary) (E.symm psi)).symm.trans
      (congrArg Subtype.val (E.apply_symm_apply psi))

/-- K coordinate comparison of the two authentic tuple expressions.
No FLZ predicate or relation truth occurs among the premises. The arbitrary
packet is retained through all three maps and both containment directions. -/
theorem relative_pair_iff
    (adapter : Definition35AutomorphismStabilizerAdapter (family.problem block))
    (standard : BlockTripleSourceSemantics 2 family.k family.K)
    (transport : StandardTransportSource standard)
    (psi : Definition35Brauer (intrinsicProblem family block carrier input OH dictionary
      (selectedReduction family block carrier input OH dictionary)))
    (w : IntrinsicWeight family block carrier input OH dictionary)
    (roots : AdmissibleRoots family block carrier input OH dictionary w) :
    letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
    ((rawStabilizer (family.automorphisms block).gamma
          (familyPair family block carrier input OH dictionary w) ≤
        globalStabilizer family.iota (family.automorphisms block).gamma
          (((toIntrinsicBrauer family block carrier input OH dictionary
            (selectedReduction family block carrier input OH dictionary)).symm psi).1 :
              IBr family.iota)) ∧
      standard.blockIsomorphic (relativeArguments family block
        ((toIntrinsicBrauer family block carrier input OH dictionary
          (selectedReduction family block carrier input OH dictionary)).symm psi)
        (familyWeight family block carrier input OH dictionary w)
        (familyOwnReduction family block carrier input OH dictionary w roots))) ↔
    ((rawStabilizer (MonoidHom.id (MulAut (Sp rank F)))
          (intrinsicPair family block carrier input OH dictionary w) ≤
        globalStabilizer (data family block carrier input OH dictionary).iota
          (MonoidHom.id (MulAut (Sp rank F))) psi.1) ∧
      standard.blockIsomorphic (selectedArguments (data family block carrier input OH dictionary)
        (selectedReduction family block carrier input OH dictionary) w roots psi)) := by
  letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
  let e := groupEquiv family block carrier
  let D := data family block carrier input OH dictionary
  let E := toIntrinsicBrauer family block carrier input OH dictionary
    (selectedReduction family block carrier input OH dictionary)
  let psiF : IBr family.iota := (E.symm psi).1
  let WF := familyPair family block carrier input OH dictionary w
  let X := WF.mapGroupEquiv e
  let V := intrinsicPair family block carrier input OH dictionary w
  let RF := familyOwnReduction family block carrier input OH dictionary w roots
  let RX := mapOwnReduction WF e RF
  let RSp := intrinsicOwnReduction family block carrier input OH dictionary w roots
  let g := selectedCorrection family block carrier input OH dictionary w
  let A := familyAutEquiv family block carrier adapter
  have hA : ∀ a, A a = (family.automorphisms block).gamma a :=
    familyAutEquiv_apply family block carrier adapter
  have hpsi : IrreducibleBrauerCharacter.equivAlongMulEquiv family.iota e psiF = psi.1 :=
    inverseBrauer_character family block carrier input OH dictionary psi
  have hpair : X.rightTwist (coordinateAutomorphism g (1 : MulAut (Sp rank F)))⁻¹ = V := by
    change (imagePair family block carrier input OH dictionary w).rightTwist
        (coordinateAutomorphism (selectedCorrection family block carrier input OH dictionary w)
          (1 : MulAut (Sp rank F)))⁻¹ =
      intrinsicPair family block carrier input OH dictionary w
    rw [coordinateAutomorphism, mul_one]
    exact selectedCorrection_spec family block carrier input OH dictionary w
  have hroots : RootCompatibleAlong
      (ownReductionRoot (k := family.k) V RSp)
      (ownReductionRoot (k := family.k) X RX)
      (ownNormalizerEquiv X V (coordinateAutomorphism g (1 : MulAut (Sp rank F)))
        hpair).toMonoidHom := by
    intro B x z
    change ((ownReductionRoot (k := family.k) WF RF).alongMulEquiv
        (ModularRep.normalizerEquiv e WF.subgroup)).lift z.1 =
      (ownReductionRoot (k := family.k) V RSp).lift z.1
    exact ((ownReductionRoot (k := family.k) WF RF).alongMulEquiv_lift
      (ModularRep.normalizerEquiv e WF.subgroup) z.1).trans
        (familyOwnReduction_lift family block carrier input OH dictionary w roots z.1)
  have hone :
      @HSMul.hSMul (MulAut (Sp rank F))ᵐᵒᵖ (IBr D.iota) (IBr D.iota)
        inferInstance (MulOpposite.op (1 : MulAut (Sp rank F))⁻¹)
        (psi.1 : IBr D.iota) = (psi.1 : IBr D.iota) := by
    simpa only [inv_one, MulOpposite.op_one] using
      (@one_smul (MulAut (Sp rank F))ᵐᵒᵖ (IBr D.iota) inferInstance
        (inferInstance : MulAction (MulAut (Sp rank F))ᵐᵒᵖ (IBr D.iota))
        (psi.1 : IBr D.iota))
  have hc01 := OddTwoActingGroupTupleTransport.fullRawContainment_iff
    family.iota (family.automorphisms block).gamma A hA psiF WF
  have hc12 :
      (rawStabilizer (MonoidHom.id (MulAut family.H)) WF ≤
        globalStabilizer family.iota (MonoidHom.id (MulAut family.H)) psiF) ↔
      (rawStabilizer (MonoidHom.id (MulAut (Sp rank F))) X ≤
        globalStabilizer D.iota (MonoidHom.id (MulAut (Sp rank F))) psi.1) := by
    have h := OddTwoGroupEquivRawTupleCoordinates.fullRawContainment_iff family.iota e psiF WF
    rw [hpsi] at h
    exact h
  have hc23 :
      (rawStabilizer (MonoidHom.id (MulAut (Sp rank F))) X ≤
        globalStabilizer D.iota (MonoidHom.id (MulAut (Sp rank F))) psi.1) ↔
      (rawStabilizer (MonoidHom.id (MulAut (Sp rank F))) V ≤
        globalStabilizer D.iota (MonoidHom.id (MulAut (Sp rank F))) psi.1) := by
    have h := OddTwoActualTupleAutomorphismCoordinates.fullRawContainment_iff D.iota psi.1
      g (1 : MulAut (Sp rank F)) X V hpair
    rw [hone] at h
    exact h
  have ht01 := OddTwoActingGroupTupleTransport.blockIsomorphic_iff
    family.iota (family.automorphisms block).gamma A hA psiF WF RF standard transport
  have ht12 :
      standard.blockIsomorphic (arguments family.iota (MonoidHom.id (MulAut family.H))
        psiF WF RF) ↔
      standard.blockIsomorphic (arguments D.iota (MonoidHom.id (MulAut (Sp rank F)))
        psi.1 X RX) := by
    have h := OddTwoGroupEquivTupleTransport.blockIsomorphic_iff family.iota e psiF WF RF RX
      (mapOwnReduction_horizontal WF e RF) standard transport
    rw [hpsi] at h
    exact h
  have ht23 :
      standard.blockIsomorphic (arguments D.iota (MonoidHom.id (MulAut (Sp rank F)))
        psi.1 X RX) ↔
      standard.blockIsomorphic (arguments D.iota (MonoidHom.id (MulAut (Sp rank F)))
        psi.1 V RSp) := by
    have h := OddTwoActualTupleAutomorphismTransport.blockIsomorphic_iff D.iota psi.1
      g (1 : MulAut (Sp rank F)) X V hpair RX RSp hroots standard transport
    rw [hone] at h
    exact h
  exact and_congr (hc01.trans (hc12.trans hc23)) (ht01.trans (ht12.trans ht23))

end FamilyCoordinates

/-- The existing full-H_G interpretation supplies the stronger intrinsic
meaning, for EVERY admissible packet. The adapter and source are the SAME
two fields of blockSource at this actual pair and block. In particular,
family.automorphisms supplies gamma; it is not substituted for the separate
Definition35AutomorphismStabilizerAdapter. No new meaning source is assumed. -/
def authenticInterpretation
    {pDef : ℕ} (scope : FLZFullHGUniverse pDef 2)
    (coverage : FullHGDefinition35Coverage scope)
    (blockSource : FullHGBlockSource coverage)
    (strictSource : FullHGStrictQuasiIsolationAdapter coverage)
    (interpretation : FullHGInterpretation scope coverage blockSource strictSource)
    (pair : FullHG scope) (block : (coverage.presentation pair).family.Block)
    (carrier : OddSymplecticPrincipalCarrier
      ((coverage.presentation pair).family.problem block) rank F)
    (OH : LocalBlockInductionOperations (p := 2)
      (k := (coverage.presentation pair).family.k)
      (K := (coverage.presentation pair).family.K) (G := Sp rank F)
      (Block := (coverage.presentation pair).family.Block))
    (dictionary : PrimitiveDictionary (coverage.presentation pair).family.blockSource.operations
      OH (groupEquiv (coverage.presentation pair).family block carrier))
    (transport : StandardTransportSource (interpretation.standard pair)) :
    let family := (coverage.presentation pair).family
    let input := interpretation.blockSemantics pair
    letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
    AuthenticDefinition35Interpretation (data family block carrier input OH dictionary)
      (selectedReduction family block carrier input OH dictionary)
      (intrinsicSource family block carrier input OH dictionary
        (selectedReduction family block carrier input OH dictionary)
        (blockSource.automorphisms pair block) (blockSource.source pair block))
      (interpretation.standard pair) := by
  let family := (coverage.presentation pair).family
  let input := interpretation.blockSemantics pair
  letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
  refine ⟨?_⟩
  intro psi w roots
  let E := toIntrinsicBrauer family block carrier input OH dictionary
    (selectedReduction family block carrier input OH dictionary)
  let v := familyWeight family block carrier input OH dictionary w
  let RF := familyOwnReduction family block carrier input OH dictionary w roots
  have compatible : RelativeRootsCompatible family block v RF :=
    ⟨familyOwnReduction_ambientCompatible family block carrier input OH dictionary w roots,
      familyOwnReduction_quotientCompatible family block carrier input OH dictionary w roots⟩
  exact (interpretation.definition35_iff pair block (E.symm psi) v RF compatible).trans
    (relative_pair_iff family block carrier input OH dictionary
      (blockSource.automorphisms pair block) (interpretation.standard pair) transport psi w roots)

end ModularRep.PaperProofs.OddTwoPrincipalFamilyAuthenticInterpretation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
