import ModularRep.PaperProofs.OddTwoBroughButterflySource
import ModularRep.PaperProofs.OddTwoActualCentralInflationRelation
import ModularRep.PaperProofs.OddTwoDefinition35TupleBinding
import ModularRep.PaperProofs.OddTwoRawContainmentDescent
import ModularRep.PaperProofs.OddTwoPrincipalAmbientOrbitStabilizers

/-!
# The actual Brough-to-Definition 3.5 join for the original weight

An already obtained relation on the actual PSp Brough tuple passes through
the computed butterfly and central inflation, then the universal standard
Definition 3.5 interpretation. Both root squares and the exact selected
local reduction are retained. Actual raw containment is pulled back through
the same group maps.

For a translate of the original principal character, the checked actual
stabilizer equality supplies that containment from the SAME original FM
image. This module assumes neither an orbit witness nor a new matching map.
It does not yet obtain the initial Brough relation or correct the orbit.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoBroughToDefinition35

open ModularRep
open ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
open ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation
open ModularRep.PaperProofs.OddTwoUniversalPrimeToTwoSelfCover
open ModularRep.PaperProofs.OddTwoProjectiveAutomorphismDiagonalJoin
open ModularRep.PaperProofs.OddTwoCentralTwoPrincipalWeightDescent
open ModularRep.PaperProofs.OddTwoCentralTwoRelationInflation
open ModularRep.PaperProofs.OddTwoActualCentralInflationPacket
open ModularRep.PaperProofs.OddTwoActualCentralInflationRelation
open ModularRep.PaperProofs.OddTwoDefinition35OwnReduction
open ModularRep.PaperProofs.OddTwoDefinition35TupleBinding
open ModularRep.PaperProofs.OddTwoPrincipalFieldFixedness
open ModularRep.PaperProofs.OddTwoActualLocalBlockSupport

universe u

variable {n : ℕ} {F k K Block J : Type u}
variable [Field F] [Fintype F] [Field k] [IsAlgClosed k] [CharP k 2]
variable [Field K] [CharZero K]
variable [MulAction (MulAut (LiteralSp n F))ᵐᵒᵖ Block]
variable [MulAction (MulAut (LiteralPSp n F))ᵐᵒᵖ J]

local instance spFintype : Fintype (LiteralSp n F) := Fintype.ofFinite _
local instance pspFintype : Fintype (LiteralPSp n F) := Fintype.ofFinite _

variable (D : PrincipalCharacterData (n := n) (F := F) (k := k) (K := K)
  (Block := Block))
variable (reduction : ∀ w : D.PrincipalWeight,
  SelectedLocalReductionSource D.blockSource D.principalBlock w)
variable {cover : OddSymplecticFullCoverSource n F}
variable (E : PrincipalDescentData (J := J) D cover)
variable (L : FullCoverAutomorphismLiftingSource (n := n) (F := F))
variable {C : CenterIntersectionSource n F} (S : BroughGroupSource C)
variable (standard : BlockTripleSourceSemantics 2 k K)
variable (butterfly : OddTwoBroughButterflySource.MRRLemma311Source S standard)
variable (quotientInterpretation :
  QuotientTupleInterpretation E.brauer cover L E.weightNaturality standard)
variable (inflation : MRRLemma314Source standard)
variable (flz : FLZSourceSemantics (D.problem reduction) (D.automorphisms reduction))
variable (definitionInterpretation : Definition35TupleInterpretation D reduction flz standard)

include butterfly quotientInterpretation inflation definitionInterpretation in
/-- K composes the actual butterfly, the canonical quotient interpretation,
MRR's upward implication, and the universal Definition 3.5 interpretation.
The actual global character is arbitrary in the downstairs principal fibre;
the original selected weight and its exact local reduction remain fixed. -/
theorem definition35_of_brough (psi : E.DownPrincipalBrauer) (w : D.PrincipalWeight)
    (R : CompatiblePairReductions cover D.iota E.iotaDown (weightRepresentative D w))
    (selectedCompatible : RootCompatibleAlong
      (selectedQuotientReduction D reduction w).iota R.upRoot
      (normalizerProjection (weightRepresentative D w).subgroup))
    (contained : OddTwoBroughActualTriple.rawStabilizer S
        (OddTwoCentralTwoRelationInflation.spQuotientPair cover (weightRepresentative D w)) ≤
      OddTwoBroughActualTriple.globalStabilizer S E.iotaDown psi.1)
    (relation : standard.blockIsomorphic
      (OddTwoBroughActualTriple.arguments S E.iotaDown psi.1
        (OddTwoCentralTwoRelationInflation.spQuotientPair cover (weightRepresentative D w))
        (quotientOwnReduction D cover w R))) :
    flz.definition35BlockIsomorphic (E.brauerEquiv psi) w := by
  apply (definitionInterpretation.relation_iff (E.brauerEquiv psi) w
    (selectedRoots D reduction cover w R selectedCompatible) ?_).mpr
  · exact selectedWeight_blockIsomorphic_upward D reduction cover w R selectedCompatible
      E.brauer L E.weightNaturality psi.1 standard quotientInterpretation inflation
      (OddTwoBroughButterflySource.blockIsomorphic_of_brough S butterfly E.iotaDown psi.1
        (OddTwoCentralTwoRelationInflation.spQuotientPair cover (weightRepresentative D w))
        (quotientOwnReduction D cover w R) R.downCompatible relation)
  · exact OddTwoRawContainmentDescent.up_raw_containment_of_brough E.brauer cover
      E.weightNaturality S psi.1 (weightRepresentative D w) contained

variable (downSupport : OperationsBrauerSupport E.iotaDown E.downInjective
  E.downSource.operations)
variable (fixed : FengMalleCorollary43aSource D)

include L in
/-- The selected original FM pair has actual Brough raw containment at
the original downstairs character. The inverse inflation cancels in K. -/
theorem originalFengMalle_raw_containment (FM : D.FengMalleTheorem62LiteralCertificate)
    (psi : E.DownPrincipalBrauer) :
    OddTwoBroughActualTriple.rawStabilizer S
        (OddTwoCentralTwoRelationInflation.spQuotientPair cover
          (weightRepresentative D (FM.omega (E.brauerEquiv psi)))) ≤
      OddTwoBroughActualTriple.globalStabilizer S E.iotaDown psi.1 := by
  exact OddTwoRawContainmentDescent.brough_raw_containment_of_up E.brauer cover L
    E.weightNaturality S psi.1 (weightRepresentative D (FM.omega (E.brauerEquiv psi)))
    (OddTwoPrincipalTripleStabilizerJoin.rawStabilizer_le_globalStabilizer D FM
      (MonoidHom.id (MulAut (OddTwoConformalProjectiveRealisation.Sp n F)))
      (E.brauerEquiv psi))

include downSupport fixed butterfly quotientInterpretation inflation definitionInterpretation in
/-- After an actual ambient translate changes the global character, the
same ORIGINAL FM image still supplies the full local group. The input
relation is on that changed global character and this original own pair. -/
theorem definition35_of_translated_brough
    (FM : D.FengMalleTheorem62LiteralCertificate) (psi : E.DownPrincipalBrauer)
    (h : Ambient (n := n) (F := F))
    (R : CompatiblePairReductions cover D.iota E.iotaDown
      (weightRepresentative D (FM.omega (E.brauerEquiv psi))))
    (selectedCompatible : RootCompatibleAlong
      (selectedQuotientReduction D reduction (FM.omega (E.brauerEquiv psi))).iota R.upRoot
      (normalizerProjection (weightRepresentative D (FM.omega (E.brauerEquiv psi))).subgroup))
    (relation :
      let _ := ambientBrauerAction E downSupport S
      standard.blockIsomorphic
        (OddTwoBroughActualTriple.arguments S E.iotaDown (h • psi).1
          (OddTwoCentralTwoRelationInflation.spQuotientPair cover
            (weightRepresentative D (FM.omega (E.brauerEquiv psi))))
          (quotientOwnReduction D cover (FM.omega (E.brauerEquiv psi)) R))) :
    let _ := ambientBrauerAction E downSupport S
    flz.definition35BlockIsomorphic (E.brauerEquiv (h • psi))
      (FM.omega (E.brauerEquiv psi)) := by
  dsimp only
  letI := ambientBrauerAction E downSupport S
  exact definition35_of_brough D reduction E L S standard butterfly
    quotientInterpretation inflation flz definitionInterpretation (h • psi)
    (FM.omega (E.brauerEquiv psi)) R selectedCompatible
    (OddTwoPrincipalAmbientOrbitStabilizers.raw_containment_translate E downSupport S fixed
      h psi _ (originalFengMalle_raw_containment D E L S FM psi)) relation

end ModularRep.PaperProofs.OddTwoBroughToDefinition35


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
