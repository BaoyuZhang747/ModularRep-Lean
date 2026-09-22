import ModularRep.PaperProofs.OddTwoActualTupleAutomorphismTransport
import ModularRep.PaperProofs.OddTwoCommonRootSelectedPairReductions
import ModularRep.PaperProofs.OddTwoDefinition35TupleBinding

/-!
# Actual principal Definition 3.5 covariance

FLZ Definition 3.5(ii), p.10, uses the FULL raw-pair stabilizer as the
local ambient group. Its standard relation therefore entails containment
in the global character stabilizer. The standalone definition binding
below retains this containment conjunct, on every matched pair and every
admissible selected-root packet. It asserts neither relation.

Covariance is then K: selected class transport supplies an actual inner
correction; one holomorph conjugation transports containment and the
actual tuple; the shared fixed root convention supplies the horizontal
normalizer square. No covariance or root-square source field is added.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoPrincipalDefinition35Covariance

open ModularRep
open ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
open ModularRep.PaperProofs.OddTwoUniversalPrimeToTwoSelfCover
open ModularRep.PaperProofs.OddTwoActualStabilizerTriple
open ModularRep.PaperProofs.OddTwoDefinition35OwnReduction
open ModularRep.PaperProofs.OddTwoDefinition35TupleBinding
open ModularRep.PaperProofs.OddTwoCentralTwoRelationInflation
open ModularRep.PaperProofs.OddTwoActualLocalBlockSupport
open ModularRep.PaperProofs.OddTwoActualCentralInflationPacket
open ModularRep.PaperProofs.OddTwoSelectedWeightAutomorphismCoordinates
open ModularRep.PaperProofs.OddTwoOwnCharacterAutomorphismTransport
open ModularRep.PaperProofs.OddTwoActualTupleAutomorphismCoordinates
open ModularRep.PaperProofs.OddTwoStandardBlockTripleTransport
open ModularRep.PaperProofs.OddTwoActualTupleAutomorphismTransport
open ModularRep.PaperProofs.OddTwoCommonRootSelectedPairReductions

universe u

variable {n : ℕ} {F k K Block : Type u}
variable [Field F] [Fintype F] [Field k] [IsAlgClosed k] [CharP k 2]
variable [Field K] [CharZero K]
variable [MulAction (MulAut (LiteralSp n F))ᵐᵒᵖ Block]

local instance covarianceSpFintype : Fintype (LiteralSp n F) := Fintype.ofFinite _
local instance covarianceAutFinite : Finite (MulAut (LiteralSp n F)) :=
  Finite.of_injective (fun a : MulAut (LiteralSp n F) => (a : LiteralSp n F → LiteralSp n F))
    DFunLike.coe_injective

variable (D : PrincipalCharacterData (n := n) (F := F) (k := k) (K := K)
  (Block := Block))
variable (reduction : ∀ w : D.PrincipalWeight,
  SelectedLocalReductionSource D.blockSource D.principalBlock w)
variable (flz : FLZSourceSemantics (D.problem reduction) (D.automorphisms reduction))
variable (standard : BlockTripleSourceSemantics 2 k K)

/-- Standalone E1 definition interpretation of the AUTHENTIC same relation.
FLZ pp.8--10 require the displayed local group to be a subgroup of the
global group. Under that containment, the existing canonical global and
full-local equivalences identify the actual standard tuple.

The iff is uniform in psi,w and EVERY admissible root packet, whose own
normalizer character is computed from the EXACT P.localReduction. There
is no FM map, relation truth, selected favourable roots or covariance law.
This is not a binding of arbitrary unrelated Prop-valued interpretations.
-/
structure AuthenticDefinition35Interpretation : Prop where
  relation_iff : ∀ (psi : D.PrincipalBrauer) (w : D.PrincipalWeight)
    (roots : SelectedNormalizerRoots D reduction w),
    flz.definition35BlockIsomorphic psi w ↔
      (rawStabilizer (MonoidHom.id (MulAut (LiteralSp n F))) (weightRepresentative D w) ≤
        globalStabilizer D.iota (MonoidHom.id (MulAut (LiteralSp n F))) psi.1) ∧
      standard.blockIsomorphic (selectedArguments D reduction w roots psi)

namespace AuthenticDefinition35Interpretation

variable {D reduction flz standard}
variable (I : AuthenticDefinition35Interpretation D reduction flz standard)

/-- K adapter: the SAME stronger interpretation supplies the accepted
conditional binding used by the Brough-to-Definition-3.5 consumer. -/
def toTupleInterpretation : Definition35TupleInterpretation D reduction flz standard where
  relation_iff psi w roots contained := by
    rw [I.relation_iff psi w roots]
    exact ⟨And.right, fun h => ⟨contained, h⟩⟩

end AuthenticDefinition35Interpretation

local instance covarianceGammaBrauer : MulAction (D.problem reduction).Gamma
    (Definition35Brauer (D.problem reduction)) :=
  definition35BrauerAction (D.problem reduction)

local instance covarianceGammaWeight : MulAction (D.problem reduction).Gamma
    (Definition35Weight (D.problem reduction)) :=
  definition35WeightAction (D.problem reduction)

/-- The exact Gamma action on the underlying actual Brauer character. -/
theorem gamma_brauer_value (a : (D.problem reduction).Gamma)
    (psi : Definition35Brauer (D.problem reduction)) :
    (a • psi).1 =
      @HSMul.hSMul (MulAut (LiteralSp n F))ᵐᵒᵖ (IBr D.iota) (IBr D.iota)
        inferInstance (MulOpposite.op ((a : MulAut (LiteralSp n F))⁻¹)) psi.1 := rfl

/-- Actual class transport supplies an inner correction for the selected
representatives. No equivariance of representative selection is assumed. -/
theorem exists_selected_gamma_coordinate (a : (D.problem reduction).Gamma)
    (w : Definition35Weight (D.problem reduction)) :
    ∃ g : LiteralSp n F,
      (weightRepresentative D w).rightTwist
          (coordinateAutomorphism g (a : MulAut (LiteralSp n F)))⁻¹ =
        weightRepresentative D (a • w) := by
  letI := D.blockSource.operations.ambientBlockData.fintypeBlock
  have h := exists_selected_coordinate (MonoidHom.id (MulAut (LiteralSp n F)))
    D.blockSource D.principalBlock (fun _ => D.principalBlock_fixed _) a w
  exact h

variable (cover : OddSymplecticFullCoverSource n F)
variable (iotaDown : PrimeRegularRootEmbedding 2 k K (LiteralPSp n F))
variable (C : CommonRootConvention D reduction cover iotaDown)
variable (interpretation : AuthenticDefinition35Interpretation D reduction flz standard)
variable (transport : StandardTransportSource standard)

include cover iotaDown C interpretation transport in
/-- Universal covariance on the ACTUAL Gamma and original Definition 3.5
carriers. Roots at w and a*w are computed from one convention. The source
definition binding and universal standard coordinate interpretation are
consumed; no target relation, seed or covariance is a premise. -/
theorem definition35_covariant (a : (D.problem reduction).Gamma)
    (psi : Definition35Brauer (D.problem reduction))
    (w : Definition35Weight (D.problem reduction)) :
    flz.definition35BlockIsomorphic (a • psi) (a • w) ↔
      flz.definition35BlockIsomorphic psi w := by
  obtain ⟨g, hpair⟩ := exists_selected_gamma_coordinate D reduction a w
  let v : D.PrincipalWeight := a • w
  let rootsW : SelectedNormalizerRoots D reduction w :=
    selectedNormalizerRoots D reduction cover iotaDown C w
  let rootsV : SelectedNormalizerRoots D reduction v :=
    selectedNormalizerRoots D reduction cover iotaDown C v
  let R := ownReduction D reduction w rootsW
  let R' := ownReduction D reduction v rootsV
  let beta : MulAut (LiteralSp n F) := coordinateAutomorphism g a
  have hroots : RootCompatibleAlong
      (ownReductionRoot (weightRepresentative D v) R')
      (ownReductionRoot (weightRepresentative D w) R)
      (ownNormalizerEquiv (weightRepresentative D w) (weightRepresentative D v)
        beta hpair).toMonoidHom :=
    upNormalizerRoots_compatible D w v
      (ownNormalizerEquiv (weightRepresentative D w) (weightRepresentative D v)
        beta hpair).toMonoidHom
  have hc :
      (rawStabilizer (MonoidHom.id (MulAut (LiteralSp n F))) (weightRepresentative D w) ≤
        globalStabilizer D.iota (MonoidHom.id (MulAut (LiteralSp n F))) psi.1) ↔
      (rawStabilizer (MonoidHom.id (MulAut (LiteralSp n F))) (weightRepresentative D v) ≤
        globalStabilizer D.iota (MonoidHom.id (MulAut (LiteralSp n F))) (a • psi).1) := by
    rw [gamma_brauer_value D reduction a psi]
    exact fullRawContainment_iff D.iota psi.1 g a
      (weightRepresentative D w) (weightRepresentative D v) hpair
  have ht : standard.blockIsomorphic (selectedArguments D reduction w rootsW psi) ↔
      standard.blockIsomorphic (selectedArguments D reduction v rootsV (a • psi)) := by
    change standard.blockIsomorphic
        (arguments D.iota (MonoidHom.id (MulAut (LiteralSp n F))) psi.1
          (weightRepresentative D w) R) ↔
      standard.blockIsomorphic
        (arguments D.iota (MonoidHom.id (MulAut (LiteralSp n F)))
          (@HSMul.hSMul (MulAut (LiteralSp n F))ᵐᵒᵖ (IBr D.iota) (IBr D.iota)
            inferInstance (MulOpposite.op ((a : MulAut (LiteralSp n F))⁻¹)) psi.1)
          (weightRepresentative D v) R')
    exact blockIsomorphic_iff D.iota psi.1 g a
      (weightRepresentative D w) (weightRepresentative D v) hpair R R' hroots
      standard transport
  rw [interpretation.relation_iff (a • psi) (a • w) rootsV,
    interpretation.relation_iff psi w rootsW]
  exact and_congr hc.symm ht.symm

end ModularRep.PaperProofs.OddTwoPrincipalDefinition35Covariance


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
