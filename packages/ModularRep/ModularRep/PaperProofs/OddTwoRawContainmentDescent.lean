import ModularRep.PaperProofs.OddTwoBroughButterflyGroups
import ModularRep.PaperProofs.OddTwoPrincipalTripleStabilizerJoin

/-!
# Actual raw-stabilizer containment through principal descent

The same selected own raw weight is quotiented by the actual Sp centre.
Surjectivity and the already proved Brauer/raw stabilizer preimages carry
containment to PSp and then to the actual Brough ambient group. The selected
FM specialization computes the downstairs global character by inverse
Brauer inflation. No new stabilizer equality or relation source is supplied.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoRawContainmentDescent

open ModularRep.CharacterWeight
open ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation
open ModularRep.PaperProofs.OddTwoActualSemidirectQuotient
open ModularRep.PaperProofs.OddTwoCentralTwoGlobalInflation
open ModularRep.PaperProofs.OddTwoCentralTwoWeightInflation
open ModularRep.PaperProofs.OddTwoCentralTwoRelationInflation
open ModularRep.PaperProofs.OddTwoProjectiveAutomorphismDiagonalJoin
open ModularRep.PaperProofs.OddTwoUniversalPrimeToTwoSelfCover
open ModularRep.PaperProofs.OddTwoBroughButterflyGroups

universe u

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

include B cover L T in
/-- Containment descends through the actual surjective holomorph projection. -/
theorem quotient_raw_containment (psi : IBr iotaDown) (W : CharacterWeight 2 K (Sp n F))
    (contained : rawPairStabilizer W ≤ brauerStabilizer iotaUp (B.brauerEquiv cover psi)) :
    rawPairStabilizer (spQuotientPair cover W) ≤ brauerStabilizer iotaDown psi := by
  intro d hd
  obtain ⟨g, hg⟩ := projection_surjective cover L d
  have hraw : g ∈ rawPairStabilizer W := by
    rw [← rawPairStabilizer_preimage cover T W]
    change projection g ∈ rawPairStabilizer (spQuotientPair cover W)
    rw [hg]
    exact hd
  have hglobal : projection g ∈ brauerStabilizer iotaDown psi := by
    change g ∈ (brauerStabilizer iotaDown psi).comap projection
    rw [brauerStabilizer_preimage B cover psi]
    exact contained hraw
  rw [hg] at hglobal
  exact hglobal

variable {C : CenterIntersectionSource n F} (S : BroughGroupSource C)

include S in
/-- The actual surjective holomorph-to-Brough comparison also preserves
containment of the SAME own raw stabilizer. -/
theorem brough_raw_containment (psi : IBr iotaDown) (W : CharacterWeight 2 K (PSp n F))
    (contained : rawPairStabilizer W ≤ brauerStabilizer iotaDown psi) :
    OddTwoBroughActualTriple.rawStabilizer S W ≤
      OddTwoBroughActualTriple.globalStabilizer S iotaDown psi := by
  intro a ha
  obtain ⟨d, hd⟩ := toBrough_surjective S a
  have hraw : d ∈ OddTwoActualStabilizerTriple.rawStabilizer
      (MonoidHom.id (MulAut (PSp n F))) W := by
    rw [← raw_preimage S W]
    change toBrough S d ∈ OddTwoBroughActualTriple.rawStabilizer S W
    rw [hd]
    exact ha
  have hglobal : d ∈ holGlobal iotaDown psi := contained hraw
  have ha' : toBrough S d ∈ OddTwoBroughActualTriple.globalStabilizer S iotaDown psi := by
    change d ∈ (OddTwoBroughActualTriple.globalStabilizer S iotaDown psi).comap (toBrough S)
    rw [global_preimage S iotaDown psi]
    exact hglobal
  rw [hd] at ha'
  exact ha'

include B cover L T S in
theorem brough_raw_containment_of_up (psi : IBr iotaDown)
    (W : CharacterWeight 2 K (Sp n F))
    (contained : rawPairStabilizer W ≤ brauerStabilizer iotaUp (B.brauerEquiv cover psi)) :
    OddTwoBroughActualTriple.rawStabilizer S (spQuotientPair cover W) ≤
      OddTwoBroughActualTriple.globalStabilizer S iotaDown psi :=
  brough_raw_containment S psi (spQuotientPair cover W)
    (quotient_raw_containment B cover L T psi W contained)

include B cover T S in
/-- Containment also pulls back through the two ACTUAL maps. This is the
direction used after the global character changes while W remains fixed. -/
theorem up_raw_containment_of_brough (psi : IBr iotaDown)
    (W : CharacterWeight 2 K (Sp n F))
    (contained : OddTwoBroughActualTriple.rawStabilizer S (spQuotientPair cover W) ≤
      OddTwoBroughActualTriple.globalStabilizer S iotaDown psi) :
    rawPairStabilizer W ≤ brauerStabilizer iotaUp (B.brauerEquiv cover psi) := by
  intro g hg
  have hraw : projection g ∈ rawPairStabilizer (spQuotientPair cover W) := by
    change g ∈ (rawPairStabilizer (spQuotientPair cover W)).comap projection
    rw [rawPairStabilizer_preimage cover T W]
    exact hg
  have hbraw : toBrough S (projection g) ∈
      OddTwoBroughActualTriple.rawStabilizer S (spQuotientPair cover W) := by
    change projection g ∈
      (OddTwoBroughActualTriple.rawStabilizer S (spQuotientPair cover W)).comap (toBrough S)
    rw [raw_preimage S]
    exact hraw
  have hglobal : projection g ∈ holGlobal iotaDown psi := by
    rw [← global_preimage S iotaDown psi]
    exact contained hbraw
  rw [← brauerStabilizer_preimage B cover psi]
  exact hglobal

include B cover L T S in
theorem raw_containment_iff_brough (psi : IBr iotaDown)
    (W : CharacterWeight 2 K (Sp n F)) :
    (rawPairStabilizer W ≤ brauerStabilizer iotaUp (B.brauerEquiv cover psi)) ↔
      (OddTwoBroughActualTriple.rawStabilizer S (spQuotientPair cover W) ≤
        OddTwoBroughActualTriple.globalStabilizer S iotaDown psi) :=
  ⟨brough_raw_containment_of_up B cover L T S psi W,
    up_raw_containment_of_brough B cover T S psi W⟩

section Selected

open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier (PrincipalCharacterData)
open ModularRep.PaperProofs.OddTwoPrincipalTripleStabilizerJoin

variable {Block : Type u} [MulAction (MulAut (Sp n F))ᵐᵒᵖ Block]
local instance spFintype : Fintype (Sp n F) := Fintype.ofFinite _
variable (D : PrincipalCharacterData (n := n) (F := F) (k := k) (K := K) (Block := Block))
variable (BD : BrauerInflationSources D.iota iotaDown)
variable (FM : D.FengMalleTheorem62LiteralCertificate)

include L T S in
/-- The same FM pair supplies the upstairs containment in K. The global
character downstairs is COMPUTED by inverse actual Brauer inflation. -/
theorem selectedFengMalle_brough_raw_containment (psi : D.PrincipalBrauer) :
    OddTwoBroughActualTriple.rawStabilizer S (spQuotientPair cover (selectedPair D FM psi)) ≤
      OddTwoBroughActualTriple.globalStabilizer S iotaDown
        ((BD.brauerEquiv cover).symm psi.1) := by
  apply brough_raw_containment_of_up BD cover L T S
  rw [Equiv.apply_symm_apply]
  exact rawStabilizer_le_globalStabilizer D FM (MonoidHom.id (MulAut (Sp n F))) psi

end Selected

end ModularRep.PaperProofs.OddTwoRawContainmentDescent


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
