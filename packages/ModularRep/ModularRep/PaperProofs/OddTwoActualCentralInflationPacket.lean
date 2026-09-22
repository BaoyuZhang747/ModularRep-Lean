import ModularRep.PaperProofs.OddTwoActualCentralInflationGroups
import ModularRep.PaperProofs.OddTwoDefinition35OwnReduction
import ModularRep.PaperProofs.OddTwoCentralTwoPrincipalWeightDescent

/-!
# The actual MRR quotient-inflation packet

The quotient groups and both subgroup maps are computed from the existing
actual stabilizer projection. Downstairs roots and characters are transported
through its computed base and own-normalizer image equivalences. Both root
compatibilities and both value equations are derived from the same actual
global inflation and own local reductions. No relation is asserted.

The selected-weight wrapper fixes the ORIGINAL principal weight while the
downstairs global character may vary. Its upstairs local character is computed
from the exact Definition 3.5 quotient reduction, with the same common-root
packet as the central descent. No replacement FM image is selected.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoActualCentralInflationPacket

open ModularRep
open ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.OddTwoActualStabilizerTriple
open ModularRep.PaperProofs.OddTwoActualSemidirectQuotient
open ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation
open ModularRep.PaperProofs.OddTwoProjectiveAutomorphismDiagonalJoin
open ModularRep.PaperProofs.OddTwoCentralTwoGlobalInflation
open ModularRep.PaperProofs.OddTwoCentralTwoWeightInflation
open ModularRep.PaperProofs.OddTwoCentralTwoRelationInflation
open ModularRep.PaperProofs.OddTwoActualCentralInflationGroups
open ModularRep.PaperProofs.OddTwoActualLocalBlockSupport
open ModularRep.PaperProofs.OddTwoUniversalPrimeToTwoSelfCover

universe u

section ExactTransport

variable {p : ℕ} {k K U V U' V' : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group U] [Finite U] [Group V] [Finite V]
variable [Group U'] [Finite U'] [Group V'] [Finite V']
variable (iotaU : PrimeRegularRootEmbedding p k K U)
variable (iotaV : PrimeRegularRootEmbedding p k K V)
variable (f : U →* V) (eU : U ≃* U') (eV : V ≃* V') (f' : U' →* V')
variable (square : ∀ x, f' (eU x) = eV (f x))

include square in
/-- Root compatibility transports through the ACTUAL commuting square.
Only the existing representation pullback and unchanged alongMulEquiv
root lifts are used. -/
theorem rootCompatibleAlong_transport
    (compatible : RootCompatibleAlong iotaV iotaU f) :
    RootCompatibleAlong (iotaV.alongMulEquiv eV) (iotaU.alongMulEquiv eU) f' := by
  intro A x a
  let R : FDRep k V := FDRep.of (Representation.pullback A.ρ eV.toMonoidHom)
  have heval : R.ρ (f (eU.symm x.1)) = A.ρ (f' x.1) := by
    change A.ρ (eV (f (eU.symm x.1))) = A.ρ (f' x.1)
    rw [← square, MulEquiv.apply_symm_apply]
  have ha : a.1 ∈ (R.ρ (f (eU.symm x.1))).charpoly.roots := by
    rw [heval]
    exact a.2
  have h := compatible R (PrimeRegularElement.map eU.symm.toMonoidHom x) ⟨a.1, ha⟩
  simpa only [PrimeRegularRootEmbedding.alongMulEquiv_lift] using h

include square in
/-- An existing actual value equation transports through the same square.
This helper introduces no representation or relation source assertion. -/
theorem values_transport (phiU : IBr iotaU) (phiV : IBr iotaV)
    (values : ∀ x : PrimeRegularElement (G := U) p,
      phiU.1 x = phiV.1 (PrimeRegularElement.map f x))
    (x : PrimeRegularElement (G := U') p) :
    (IrreducibleBrauerCharacter.alongMulEquiv iotaU eU phiU).1 x =
      (IrreducibleBrauerCharacter.alongMulEquiv iotaV eV phiV).1
        (PrimeRegularElement.map f' x) := by
  change phiU.1 (PrimeRegularElement.map eU.symm.toMonoidHom x) =
    phiV.1 (PrimeRegularElement.map eV.symm.toMonoidHom (PrimeRegularElement.map f' x))
  rw [values]
  congr 1
  apply Subtype.ext
  apply eV.injective
  change eV (f (eU.symm x.1)) = eV (eV.symm (f' x.1))
  rw [MulEquiv.apply_symm_apply, ← square, MulEquiv.apply_symm_apply]

end ExactTransport

section OwnReductionAccessors

variable {p : ℕ} {k K H : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group H] [Fintype H]
variable (W : CharacterWeight p K H) (R : OwnNormalizerReduction (k := k) W)

/-- A neutral typed accessor for an own reduction on an abstract raw pair.
At a concrete quotient pair it avoids elaborating the record projection
through the entire ordinary-character transport construction. -/
def ownReductionRoot : PrimeRegularRootEmbedding p k K
    (Subgroup.normalizer (W.subgroup : Set H)) := R.root

/-- The identical own IBr, typed through the neutral root accessor. -/
def ownReductionBrauer : IBr (ownReductionRoot W R) := R.brauer

/-- The same own ordinary-character equation, with no new reduction data. -/
theorem ownReductionValues :
    NormalizerInflatedReduction W.subgroup W.localCharacter
      (ownReductionRoot W R) (ownReductionBrauer W R) := R.own_reduction

end OwnReductionAccessors

section ActualPacket

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

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

/-- The existing normalizer map with the OWN quotient pair's normalizer
exposed in the codomain. Its underlying group projection is unchanged. -/
def ownNormalizerProjection :
    Subgroup.normalizer (W.subgroup : Set (Sp n F)) →*
      Subgroup.normalizer ((Wdown).subgroup : Set (PSp n F)) :=
  normalizerMap (spProjection n F) W.subgroup

variable (Rup : OwnNormalizerReduction (k := k) W)
variable (Rdown : OwnNormalizerReduction (k := k) (spQuotientPair cover W))
variable (normalizerCompatible : RootCompatibleAlong (p := 2) (k := k) (K := K)
  (G := Subgroup.normalizer ((spQuotientPair cover W).subgroup : Set (PSp n F)))
  (H := Subgroup.normalizer (W.subgroup : Set (Sp n F)))
  (ownReductionRoot (H := PSp n F) (spQuotientPair cover W) Rdown)
  (ownReductionRoot (H := Sp n F) W Rup)
  (ownNormalizerProjection cover W))

local notation "piStab" => argumentsProjection B cover psi W Rup
local notation "Tup" => arguments iotaUp upAction psiUp W Rup

/-- The checked base equivalence with the exact tuple subgroup type. -/
def packetUpBaseEquiv : Sp n F ≃* (Tup).N :=
  baseEquiv iotaUp upAction psiUp

/-- The checked own-normalizer equivalence with the exact tuple intersection. -/
def packetUpNormalizerEquiv :
    Subgroup.normalizer (W.subgroup : Set (Sp n F)) ≃* ↥((Tup).N ⊓ (Tup).H) :=
  normalizerEquivIntersection iotaUp upAction psiUp W

/-- The actual quotient-image base equivalence with precisely the quotient
subgroup and group instance used by QuotientInflationData. -/
def packetDownBaseEquiv : PSp n F ≃*
    (Tup).N.map (QuotientGroup.mk' (piStab).ker) :=
  baseImageEquiv B cover L psi

/-- The actual quotient-image own-normalizer equivalence on the exact
QuotientInflationData intersection. No new equivalence is supplied. -/
def packetDownNormalizerEquiv :
    Subgroup.normalizer ((Wdown).subgroup : Set (PSp n F)) ≃*
      ↥((Tup).N.map (QuotientGroup.mk' (piStab).ker) ⊓
        (Tup).H.map (QuotientGroup.mk' (piStab).ker)) :=
  normalizerImageEquiv B cover L T psi W

/-- The same checked base square, with all four exact carrier types exposed. -/
theorem packetBase_square (g : Sp n F) :
    ((QuotientGroup.mk' (piStab).ker).subgroupMap (Tup).N)
        (packetUpBaseEquiv B cover psi W Rup g) =
      packetDownBaseEquiv B cover L psi W Rup (spProjection n F g) :=
  (baseImageEquiv_projection B cover L psi g).symm

/-- The same checked own-normalizer square on the exact tuple types. -/
theorem packetNormalizer_square
    (x : Subgroup.normalizer (W.subgroup : Set (Sp n F))) :
    (Tup).localProjection (piStab).ker (packetUpNormalizerEquiv B cover psi W Rup x) =
      packetDownNormalizerEquiv B cover L T psi W Rup (ownNormalizerProjection cover W x) :=
  (normalizerImageEquiv_projection B cover L T psi W Rup x).symm

/-- The normal subgroup is the actual projection kernel. Every field of
QuotientInflationData is COMPUTED from the fixed groups and own characters.
The local root compatibility is on the actual normalizer projection. -/
def packet :
    (arguments iotaUp upAction psiUp W Rup).QuotientInflationData (piStab).ker where
  iotaN := PrimeRegularRootEmbedding.alongMulEquiv
    (G := PSp n F) (H := (Tup).N.map (QuotientGroup.mk' (piStab).ker))
    iotaDown (packetDownBaseEquiv B cover L psi W Rup)
  iotaM := PrimeRegularRootEmbedding.alongMulEquiv
    (G := Subgroup.normalizer ((Wdown).subgroup : Set (PSp n F)))
    (H := ↥((Tup).N.map (QuotientGroup.mk' (piStab).ker) ⊓
      (Tup).H.map (QuotientGroup.mk' (piStab).ker)))
    (ownReductionRoot (H := PSp n F) Wdown Rdown)
    (packetDownNormalizerEquiv B cover L T psi W Rup)
  theta := IrreducibleBrauerCharacter.alongMulEquiv
    (G := PSp n F) (H := (Tup).N.map (QuotientGroup.mk' (piStab).ker)) iotaDown
    (packetDownBaseEquiv B cover L psi W Rup) psi
  phi := IrreducibleBrauerCharacter.alongMulEquiv
    (G := Subgroup.normalizer ((Wdown).subgroup : Set (PSp n F)))
    (H := ↥((Tup).N.map (QuotientGroup.mk' (piStab).ker) ⊓
      (Tup).H.map (QuotientGroup.mk' (piStab).ker)))
    (ownReductionRoot (H := PSp n F) Wdown Rdown)
    (packetDownNormalizerEquiv B cover L T psi W Rup)
    (ownReductionBrauer (H := PSp n F) Wdown Rdown)
  theta_root_compatible := rootCompatibleAlong_transport
    (U := Sp n F) (V := PSp n F) (U' := (Tup).N)
    (V' := (Tup).N.map (QuotientGroup.mk' (piStab).ker)) iotaUp iotaDown
    (spProjection n F) (packetUpBaseEquiv B cover psi W Rup)
    (packetDownBaseEquiv B cover L psi W Rup)
    ((QuotientGroup.mk' (piStab).ker).subgroupMap
      (Tup).N)
    (packetBase_square B cover L psi W Rup) B.rootCompatible
  phi_root_compatible := rootCompatibleAlong_transport
    (U := Subgroup.normalizer (W.subgroup : Set (Sp n F)))
    (V := Subgroup.normalizer ((Wdown).subgroup : Set (PSp n F)))
    (U' := ↥((Tup).N ⊓ (Tup).H))
    (V' := ↥((Tup).N.map (QuotientGroup.mk' (piStab).ker) ⊓
      (Tup).H.map (QuotientGroup.mk' (piStab).ker)))
    (ownReductionRoot (H := Sp n F) W Rup) (ownReductionRoot (H := PSp n F) Wdown Rdown)
    (ownNormalizerProjection cover W)
    (packetUpNormalizerEquiv B cover psi W Rup)
    (packetDownNormalizerEquiv B cover L T psi W Rup)
    ((arguments iotaUp upAction psiUp W Rup).localProjection (piStab).ker)
    (packetNormalizer_square B cover L T psi W Rup)
    normalizerCompatible
  theta_values := values_transport
    (U := Sp n F) (V := PSp n F) (U' := (Tup).N)
    (V' := (Tup).N.map (QuotientGroup.mk' (piStab).ker)) iotaUp iotaDown
    (spProjection n F) (packetUpBaseEquiv B cover psi W Rup)
    (packetDownBaseEquiv B cover L psi W Rup)
    ((QuotientGroup.mk' (piStab).ker).subgroupMap
      (Tup).N)
    (packetBase_square B cover L psi W Rup)
    psiUp psi (fun x => B.brauerEquiv_value cover psi x)
  phi_values := values_transport
    (U := Subgroup.normalizer (W.subgroup : Set (Sp n F)))
    (V := Subgroup.normalizer ((Wdown).subgroup : Set (PSp n F)))
    (U' := ↥((Tup).N ⊓ (Tup).H))
    (V' := ↥((Tup).N.map (QuotientGroup.mk' (piStab).ker) ⊓
      (Tup).H.map (QuotientGroup.mk' (piStab).ker)))
    (ownReductionRoot (H := Sp n F) W Rup) (ownReductionRoot (H := PSp n F) Wdown Rdown)
    (ownNormalizerProjection cover W)
    (packetUpNormalizerEquiv B cover psi W Rup)
    (packetDownNormalizerEquiv B cover L T psi W Rup)
    ((arguments iotaUp upAction psiUp W Rup).localProjection (piStab).ker)
    (packetNormalizer_square B cover L T psi W Rup)
    (ownReductionBrauer (H := Sp n F) W Rup)
    (ownReductionBrauer (H := PSp n F) Wdown Rdown) (by
      intro x
      have h := ownLocalReduction_inflation (spProjection n F)
        cover.fullCover.1.1 cover.projection_twoKernel W
        (ownReductionRoot (H := Sp n F) W Rup)
        (ownReductionRoot (H := PSp n F) Wdown Rdown)
        (ownReductionBrauer (H := Sp n F) W Rup)
        (ownReductionBrauer (H := PSp n F) Wdown Rdown)
        (ownReductionValues (H := Sp n F) W Rup)
        (ownReductionValues (H := PSp n F) Wdown Rdown)
      exact congrArg (fun chi => chi x) h)

include L T in
/-- The actual MRR kernel-containment hypothesis is already proved K. -/
theorem packet_kernel_contained :
    (piStab).ker ≤ (arguments iotaUp upAction psiUp W Rup).N ⊓
      (arguments iotaUp upAction psiUp W Rup).H :=
  kernel_le_intersection B cover L T psi W

/-- The quotient's entire ambient group is identified by the canonical
first-isomorphism theorem, retaining the actual projection. No relation
invariance under this equivalence is asserted by this data construction. -/
def downstairsGroupEquiv :
    (packet B cover L T psi W Rup Rdown normalizerCompatible).downstairs.G ≃*
      globalStabilizer iotaDown downAction psi :=
  quotientStabilizerEquiv B cover L psi

end ActualPacket

section ExactSelectedReduction

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

/-- The root of the central descent packet is used verbatim for the
computed Definition 3.5 normalizer reduction. The selected quotient root
must be compatible with this SAME root, not a separately chosen one. -/
def selectedRoots : SelectedNormalizerRoots D reduction w where
  root := R.upRoot
  quotientCompatible := selectedCompatible
  ambientCompatible := R.upCompatible

/-- Both reductions on the identical normalizer root have the same own
ordinary values, so their IBr objects agree in K. -/
theorem computedBrauer_eq_pairBrauer :
    (ownReduction D reduction w
      (selectedRoots D reduction cover w R selectedCompatible)).brauer = R.upBrauer := by
  apply Subtype.ext
  ext x
  exact ((ownReduction D reduction w
    (selectedRoots D reduction cover w R selectedCompatible)).own_reduction x).symm.trans
      (R.upReduction x)

def quotientOwnReduction :
    OwnNormalizerReduction (k := k) (spQuotientPair cover (weightRepresentative D w)) where
  root := R.downRoot
  brauer := R.downBrauer
  own_reduction := R.downReduction

variable (B : BrauerInflationSources D.iota iotaDown)
variable (L : FullCoverAutomorphismLiftingSource (n := n) (F := F))
variable (T : ActualQuotientNaturality (K := K) (spProjection n F)
  cover.fullCover.1.1 cover.projection_twoKernel)

/-- The ORIGINAL selected weight w remains fixed while the actual global
character psi may be the one produced by a conformal orbit adjustment.
The source packet contains no replacement weight or relation conclusion. -/
def packetForSelectedWeight (psi : IBr iotaDown) :=
  packet B cover L T psi (weightRepresentative D w)
    (ownReduction D reduction w (selectedRoots D reduction cover w R selectedCompatible))
    (quotientOwnReduction D cover w R) R.quotientCompatible

end ExactSelectedReduction

end ModularRep.PaperProofs.OddTwoActualCentralInflationPacket


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
