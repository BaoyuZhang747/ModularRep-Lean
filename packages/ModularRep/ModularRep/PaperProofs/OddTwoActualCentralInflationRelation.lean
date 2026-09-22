import ModularRep.PaperProofs.OddTwoActualCentralInflationPacket

/-!
# Canonical quotient-tuple interpretation and the upward MRR consumer

The quotient tuple and the literal PSp tuple have computed whole, base,
local and intersection equivalences. Their ambient maps, root conventions
and own characters are retained below. The sole interpretation source is
an iff for the SAME standard modular block-triple relation, universal in
the actual global character, the ORIGINAL raw weight and every admissible
common-root packet. It asserts neither relation.

K then applies this iff and the already authenticated upward MRR Lemma 3.14.
No orbit witness, replacement weight, final FLZ relation or iBAW conclusion
is a source field. Full raw-stabilizer containment is a separate later join.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoActualCentralInflationRelation

open ModularRep
open ModularRep.CharacterWeight
open ModularRep.PaperProofs.OddTwoActualStabilizerTriple
open ModularRep.PaperProofs.OddTwoActualSemidirectQuotient
open ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation
open ModularRep.PaperProofs.OddTwoProjectiveAutomorphismDiagonalJoin
open ModularRep.PaperProofs.OddTwoCentralTwoGlobalInflation
open ModularRep.PaperProofs.OddTwoCentralTwoWeightInflation
open ModularRep.PaperProofs.OddTwoCentralTwoRelationInflation
open ModularRep.PaperProofs.OddTwoActualCentralInflationGroups
open ModularRep.PaperProofs.OddTwoActualCentralInflationPacket
open ModularRep.PaperProofs.OddTwoActualLocalBlockSupport
open ModularRep.PaperProofs.OddTwoUniversalPrimeToTwoSelfCover

universe u

section CommonRootTransport

variable {p : ℕ} {k K A U V : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group A] [Finite A] [Group U] [Finite U] [Group V] [Finite V]

/-- Two transports of the SAME root have identical field-level lifts.
Thus their compatibility along the displayed homomorphism is K, without
any assumption about independently chosen root embeddings. -/
theorem commonRootAlongMulEquiv_compatible
    (iota : PrimeRegularRootEmbedding p k K A)
    (eU : A ≃* U) (eV : A ≃* V) (f : U →* V) :
    RootCompatibleAlong (iota.alongMulEquiv eV) (iota.alongMulEquiv eU) f := by
  intro R x a
  exact (PrimeRegularRootEmbedding.alongMulEquiv_lift iota eU a.1).trans
    (PrimeRegularRootEmbedding.alongMulEquiv_lift iota eV a.1).symm

end CommonRootTransport

section ActualInterpretation

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

local instance spFintype : Fintype (Sp n F) := Fintype.ofFinite _
local instance pspFintype : Fintype (PSp n F) := Fintype.ofFinite _

variable (psi : IBr iotaDown) (W : CharacterWeight 2 K (Sp n F))
variable (Rup : OwnNormalizerReduction (k := k) W)
variable (Rdown : OwnNormalizerReduction (k := k) (spQuotientPair cover W))
variable (normalizerCompatible : RootCompatibleAlong (p := 2) (k := k) (K := K)
  (G := Subgroup.normalizer ((spQuotientPair cover W).subgroup : Set (PSp n F)))
  (H := Subgroup.normalizer (W.subgroup : Set (Sp n F)))
  (ownReductionRoot (H := PSp n F) (spQuotientPair cover W) Rdown)
  (ownReductionRoot (H := Sp n F) W Rup) (ownNormalizerProjection cover W))

local notation "psiUp" => B.brauerEquiv cover psi
local notation "Wdown" => spQuotientPair cover W
local notation "upAction" => MonoidHom.id (MulAut (Sp n F))
local notation "downAction" => MonoidHom.id (MulAut (PSp n F))
local notation "piStab" => actualStabilizerProjection B cover psi
local notation "qStab" => QuotientGroup.mk'
  (MonoidHom.ker (actualStabilizerProjection B cover psi))
local notation "Nu" => baseSubgroup iotaUp upAction psiUp
local notation "Nd" => baseSubgroup iotaDown downAction psi
local notation "Hu" => localSubgroup iotaUp upAction psiUp W
local notation "Hd" => localSubgroup iotaDown downAction psi Wdown
local notation "Qdata" => packet B cover L T psi W Rup Rdown normalizerCompatible
local notation "Tdown" => arguments iotaDown downAction psi Wdown Rdown

/-- The canonical quotient-image base map, expressed through the literal
PSp coordinates on both sides. It is not an input equivalence. -/
def quotientBaseEquiv : (Nu).map qStab ≃* Nd :=
  (baseImageEquiv B cover L psi).symm.trans (baseEquiv iotaDown downAction psi)

@[simp] theorem quotientBaseEquiv_ambient (x : (Nu).map qStab) :
    (quotientBaseEquiv B cover L psi x : globalStabilizer iotaDown downAction psi) =
      quotientStabilizerEquiv B cover L psi x := by
  have h := congrArg (quotientStabilizerEquiv B cover L psi)
    (baseImageEquiv_coe B cover L psi ((baseImageEquiv B cover L psi).symm x))
  simpa only [quotientBaseEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply] using h.symm

/-- The whole local subgroup is the actual quotient image of the same
upstairs local subgroup, using its proved exact preimage equality. -/
def quotientLocalEquiv : (Hu).map qStab ≃* Hd :=
  quotientImageEquiv piStab (actualStabilizerProjection_surjective B cover L psi)
    Hu Hd (local_preimage B cover T psi W)

@[simp] theorem quotientLocalEquiv_ambient (x : (Hu).map qStab) :
    (quotientLocalEquiv B cover L T psi W x :
      globalStabilizer iotaDown downAction psi) =
      quotientStabilizerEquiv B cover L psi x := rfl

/-- The intersection map retains the OWN normalizer coordinates. -/
def quotientIntersectionEquiv :
    ↥((Nu).map qStab ⊓ (Hu).map qStab) ≃* ↥(Nd ⊓ Hd) :=
  (normalizerImageEquiv B cover L T psi W).symm.trans
    (normalizerEquivIntersection iotaDown downAction psi Wdown)

@[simp] theorem quotientIntersectionEquiv_ambient
    (x : ↥((Nu).map qStab ⊓ (Hu).map qStab)) :
    (quotientIntersectionEquiv B cover L T psi W x :
      globalStabilizer iotaDown downAction psi) =
      quotientStabilizerEquiv B cover L psi x := by
  have h := congrArg (quotientStabilizerEquiv B cover L psi)
    (normalizerImageEquiv_coe B cover L T psi W
      ((normalizerImageEquiv B cover L T psi W).symm x))
  simpa only [quotientIntersectionEquiv, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply] using h.symm

/-- Both transported base roots have the identical field-level lift.
This authenticates the actual canonical base map, not independent roots. -/
theorem quotientBase_root_compatible :
    RootCompatibleAlong (p := 2) (k := k) (K := K)
      (G := ↥Nd) (H := ↥((Nu).map qStab))
      (iotaDown.alongMulEquiv (baseEquiv iotaDown downAction psi))
      (iotaDown.alongMulEquiv (baseImageEquiv B cover L psi))
      (quotientBaseEquiv B cover L psi).toMonoidHom :=
  commonRootAlongMulEquiv_compatible iotaDown (baseImageEquiv B cover L psi)
    (baseEquiv iotaDown downAction psi) (quotientBaseEquiv B cover L psi).toMonoidHom

/-- Both intersection roots transport the SAME own normalizer root. -/
theorem quotientIntersection_root_compatible :
    RootCompatibleAlong (p := 2) (k := k) (K := K)
      (G := ↥(Nd ⊓ Hd)) (H := ↥((Nu).map qStab ⊓ (Hu).map qStab))
      (PrimeRegularRootEmbedding.alongMulEquiv
        (G := Subgroup.normalizer ((spQuotientPair cover W).subgroup : Set (PSp n F)))
        (H := ↥(Nd ⊓ Hd))
        (ownReductionRoot (H := PSp n F) (spQuotientPair cover W) Rdown)
        (normalizerEquivIntersection iotaDown downAction psi Wdown))
      (PrimeRegularRootEmbedding.alongMulEquiv
        (G := Subgroup.normalizer ((spQuotientPair cover W).subgroup : Set (PSp n F)))
        (H := ↥((Nu).map qStab ⊓ (Hu).map qStab))
        (ownReductionRoot (H := PSp n F) (spQuotientPair cover W) Rdown)
        (normalizerImageEquiv B cover L T psi W))
      (quotientIntersectionEquiv B cover L T psi W).toMonoidHom :=
  commonRootAlongMulEquiv_compatible
    (ownReductionRoot (H := PSp n F) (spQuotientPair cover W) Rdown)
    (normalizerImageEquiv B cover L T psi W)
    (normalizerEquivIntersection iotaDown downAction psi Wdown)
    (quotientIntersectionEquiv B cover L T psi W).toMonoidHom

/-- The quotient's base character is the literal downstairs character
through the computed base map. -/
theorem quotientBase_character_values
    (x : PrimeRegularElement (G := (Qdata).downstairs.N) 2) :
    (Qdata).downstairs.theta.1 x = (Tdown).theta.1
      (PrimeRegularElement.map (quotientBaseEquiv B cover L psi).toMonoidHom x) := by
  change psi.1 (PrimeRegularElement.map (baseImageEquiv B cover L psi).symm.toMonoidHom x) =
    psi.1 (PrimeRegularElement.map (baseEquiv iotaDown downAction psi).symm.toMonoidHom
      (PrimeRegularElement.map (quotientBaseEquiv B cover L psi).toMonoidHom x))
  congr 1
  apply Subtype.ext
  change (baseImageEquiv B cover L psi).symm x.1 =
    (baseEquiv iotaDown downAction psi).symm
      (baseEquiv iotaDown downAction psi ((baseImageEquiv B cover L psi).symm x.1))
  exact (MulEquiv.symm_apply_apply _ _).symm

/-- The quotient's local character retains the SAME own normalizer IBr;
no auxiliary quotient reduction or replacement weight is substituted. -/
theorem quotientIntersection_character_values
    (x : PrimeRegularElement (G := ↥((Qdata).downstairs.N ⊓
      (Qdata).downstairs.H)) 2) :
    (Qdata).downstairs.phi.1 x = (Tdown).phi.1
      (PrimeRegularElement.map
        (quotientIntersectionEquiv B cover L T psi W).toMonoidHom x) := by
  change Rdown.brauer.1 (PrimeRegularElement.map
      (normalizerImageEquiv B cover L T psi W).symm.toMonoidHom x) =
    Rdown.brauer.1 (PrimeRegularElement.map
      (normalizerEquivIntersection iotaDown downAction psi Wdown).symm.toMonoidHom
      (PrimeRegularElement.map
        (quotientIntersectionEquiv B cover L T psi W).toMonoidHom x))
  congr 1
  apply Subtype.ext
  change (normalizerImageEquiv B cover L T psi W).symm x.1 =
    (normalizerEquivIntersection iotaDown downAction psi Wdown).symm
      (normalizerEquivIntersection iotaDown downAction psi Wdown
        ((normalizerImageEquiv B cover L T psi W).symm x.1))
  exact (MulEquiv.symm_apply_apply _ _).symm

/-- E1/U interpretation of the SAME standard modular block-triple
definition under the computed canonical quotient equivalence. No source
instance is asserted for an arbitrary unrelated predicate.

The whole map is downstairsGroupEquiv, the base/local/intersection maps
are exactly quotientBaseEquiv, quotientLocalEquiv and
quotientIntersectionEquiv, with the proved ambient/root/character equations
above. Every actual psi, ORIGINAL W and every admissible root packet is
quantified. This field asserts neither side of the iff and assumes no
matching, full raw containment, orbit witness or relation truth. -/
structure QuotientTupleInterpretation
    (standard : BlockTripleSourceSemantics 2 k K) : Prop where
  relation_iff : ∀ (psi : IBr iotaDown) (W : CharacterWeight 2 K (Sp n F))
    (Rup : OwnNormalizerReduction (k := k) W)
    (Rdown : OwnNormalizerReduction (k := k) (spQuotientPair cover W))
    (normalizerCompatible : RootCompatibleAlong (p := 2) (k := k) (K := K)
      (G := Subgroup.normalizer ((spQuotientPair cover W).subgroup : Set (PSp n F)))
      (H := Subgroup.normalizer (W.subgroup : Set (Sp n F)))
      (ownReductionRoot (H := PSp n F) (spQuotientPair cover W) Rdown)
      (ownReductionRoot (H := Sp n F) W Rup) (ownNormalizerProjection cover W)),
    RootCompatibleAlong iotaUp (ownReductionRoot (H := Sp n F) W Rup)
      (Subgroup.normalizer (W.subgroup : Set (Sp n F))).subtype →
    RootCompatibleAlong iotaDown
      (ownReductionRoot (H := PSp n F) (spQuotientPair cover W) Rdown)
      (Subgroup.normalizer ((spQuotientPair cover W).subgroup : Set (PSp n F))).subtype →
    (standard.blockIsomorphic
      (packet B cover L T psi W Rup Rdown normalizerCompatible).downstairs ↔
      standard.blockIsomorphic
        (arguments iotaDown (MonoidHom.id (MulAut (PSp n F))) psi
          (spQuotientPair cover W) Rdown))

include normalizerCompatible in
/-- K: move an already obtained actual downstairs relation through only
the canonical interpretation, then apply MRR's published upward lemma.
The conclusion is on the SAME upstairs global character and ORIGINAL W. -/
theorem blockIsomorphic_upward
    (standard : BlockTripleSourceSemantics 2 k K)
    (interpretation : QuotientTupleInterpretation B cover L T standard)
    (mrr : MRRLemma314Source standard)
    (upAmbientCompatible : RootCompatibleAlong iotaUp (ownReductionRoot (H := Sp n F) W Rup)
      (Subgroup.normalizer (W.subgroup : Set (Sp n F))).subtype)
    (downAmbientCompatible : RootCompatibleAlong iotaDown
      (ownReductionRoot (H := PSp n F) (spQuotientPair cover W) Rdown)
      (Subgroup.normalizer ((Wdown).subgroup : Set (PSp n F))).subtype)
    (h : standard.blockIsomorphic Tdown) :
    standard.blockIsomorphic (arguments iotaUp upAction psiUp W Rup) :=
  blockIsomorphic_of_quotient mrr (arguments iotaUp upAction psiUp W Rup)
    (argumentsProjection B cover psi W Rup).ker
    (packet_kernel_contained B cover L T psi W Rup)
    Qdata ((interpretation.relation_iff psi W Rup Rdown normalizerCompatible
      upAmbientCompatible downAmbientCompatible).mpr h)

end ActualInterpretation

section OriginalSelectedWeight

open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier (PrincipalCharacterData)
open ModularRep.PaperProofs.OddTwoDefinition35OwnReduction
open ModularRep.PaperProofs.OddTwoCentralTwoPrincipalWeightDescent

variable {n : ℕ} {F k K Block : Type u}
variable [Field F] [Fintype F] [Field k] [Field K]
variable [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [MulAction (MulAut (Sp n F))ᵐᵒᵖ Block]
local instance spFintype' : Fintype (Sp n F) := Fintype.ofFinite _

variable (D : PrincipalCharacterData (n := n) (F := F) (k := k) (K := K)
  (Block := Block))
variable (reduction : ∀ w : D.PrincipalWeight,
  SelectedLocalReductionSource D.blockSource D.principalBlock w)
variable (cover : OddSymplecticFullCoverSource n F)
variable {iotaDown : PrimeRegularRootEmbedding 2 k K (PSp n F)}
variable (w : D.PrincipalWeight)
variable (R : CompatiblePairReductions cover D.iota iotaDown (weightRepresentative D w))
variable (selectedCompatible : RootCompatibleAlong
  (selectedQuotientReduction D reduction w).iota R.upRoot
  (OddTwoDefinition35OwnReduction.normalizerProjection (weightRepresentative D w).subgroup))
variable (B : BrauerInflationSources D.iota iotaDown)
variable (L : FullCoverAutomorphismLiftingSource (n := n) (F := F))
variable (T : ActualQuotientNaturality (K := K) (spProjection n F)
  cover.fullCover.1.1 cover.projection_twoKernel)

/-- The arbitrary downstairs global character may change in the BS orbit
argument; the selected principal weight w remains the ORIGINAL one.
Its upstairs own reduction is computed from the exact P.localReduction. -/
theorem selectedWeight_blockIsomorphic_upward (psi : IBr iotaDown)
    (standard : BlockTripleSourceSemantics 2 k K)
    (interpretation : QuotientTupleInterpretation B cover L T standard)
    (mrr : MRRLemma314Source standard)
    (h : standard.blockIsomorphic
      (arguments iotaDown (MonoidHom.id (MulAut (PSp n F))) psi
        (spQuotientPair cover (weightRepresentative D w))
        (quotientOwnReduction D cover w R))) :
    standard.blockIsomorphic
      (arguments D.iota (MonoidHom.id (MulAut (Sp n F))) (B.brauerEquiv cover psi)
        (weightRepresentative D w)
        (ownReduction D reduction w
          (selectedRoots D reduction cover w R selectedCompatible))) :=
  blockIsomorphic_upward B cover L T psi (weightRepresentative D w)
    (ownReduction D reduction w (selectedRoots D reduction cover w R selectedCompatible))
    (quotientOwnReduction D cover w R) R.quotientCompatible
    standard interpretation mrr R.upCompatible R.downCompatible h

end OriginalSelectedWeight

end ModularRep.PaperProofs.OddTwoActualCentralInflationRelation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
