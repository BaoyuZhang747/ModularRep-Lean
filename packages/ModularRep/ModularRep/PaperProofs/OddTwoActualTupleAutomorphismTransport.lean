import ModularRep.PaperProofs.OddTwoActualTupleAutomorphismCoordinates
import ModularRep.PaperProofs.OddTwoActualCentralInflationPacket

/-!
# Own-character transport on the actual automorphism tuples

The whole-group and subgroup coordinates are computed by the preceding
module. Here the two own reduction equations supply the local character
pullback, and the actual Brauer action supplies the global pullback.
Two horizontal root-compatibility squares are transported through those
same coordinates. They are explicit conditional K inputs, not a new source
law and not a claimed construction of coherent local roots.

The resulting TupleIsomorphism may then be consumed by the universal
standard definition-transport source. No relation or covariance is assumed
to construct the packet, and the final iff asserts neither relation.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoActualTupleAutomorphismTransport

open ModularRep.CharacterWeight
open ModularRep.PaperProofs.OddTwoActualStabilizerTriple
open ModularRep.PaperProofs.OddTwoSelectedWeightAutomorphismCoordinates
open ModularRep.PaperProofs.OddTwoOwnCharacterAutomorphismTransport
open ModularRep.PaperProofs.OddTwoStandardBlockTripleTransport
open ModularRep.PaperProofs.OddTwoActualTupleAutomorphismCoordinates
open ModularRep.PaperProofs.OddTwoActualCentralInflationPacket
open ModularRep.PaperProofs.OddTwoActualLocalBlockSupport
open ModularRep.PaperProofs.OddTwoCentralTwoRelationInflation

universe u

variable {p : ℕ} {k K H : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group H] [Fintype H]

local instance finiteTransportAut : Finite (MulAut H) :=
  Finite.of_injective (fun a : MulAut H => (a : H → H)) DFunLike.coe_injective

variable (iota : PrimeRegularRootEmbedding p k K H)
variable (psi : IBr iota) (g : H) (a : MulAut H)
variable (W V : CharacterWeight p K H)
variable (hpair : W.rightTwist (coordinateAutomorphism g a)⁻¹ = V)
variable (R : OwnNormalizerReduction (k := k) W)
variable (R' : OwnNormalizerReduction (k := k) V)

local notation "action" => MonoidHom.id (MulAut H)
local notation "psi'" => MulOpposite.op a⁻¹ • psi
local notation "eBase" => displayedBaseEquiv iota psi g a
local notation "eLocal" => displayedIntersectionEquiv iota psi g a W V hpair

/-- The displayed base map commutes with beta in the original H
coordinates. This is a computation of the already fixed map. -/
theorem base_transport_square (x : H) :
    eBase (OddTwoActualStabilizerTriple.baseEquiv iota action psi x) =
      OddTwoActualStabilizerTriple.baseEquiv iota action psi'
        (coordinateAutomorphism g a x) := by
  simp only [displayedBaseEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

/-- The local square uses the SAME computed own-normalizer equivalence. -/
theorem local_transport_square (x : Subgroup.normalizer (W.subgroup : Set H)) :
    eLocal (normalizerEquivIntersection iota action psi W x) =
      normalizerEquivIntersection iota action psi' V
        (ownNormalizerEquiv W V (coordinateAutomorphism g a) hpair x) := by
  simp only [displayedIntersectionEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

/-- The ambient root is literally the same embedding on both copies of H.
Thus its horizontal compatibility needs no additional source input. -/
theorem ambient_root_compatible :
    RootCompatibleAlong iota iota (coordinateAutomorphism g a).toMonoidHom := by
  intro A x z
  rfl

variable (ambientRoots : RootCompatibleAlong iota iota
  (coordinateAutomorphism g a).toMonoidHom)
variable (normalizerRoots : RootCompatibleAlong
  (ownReductionRoot V R') (ownReductionRoot W R)
  (ownNormalizerEquiv W V (coordinateAutomorphism g a) hpair).toMonoidHom)

/-- Conditional K packet on the ACTUAL two tuples. The root squares are
transported along the fixed displayed maps; character values are proved
from the actual action and the two own reductions. In particular, the
local root square is not inferred from equal own character values. -/
def tupleIsomorphism :
    TupleIsomorphism (arguments iota action psi W R)
      (arguments iota action psi' V R') :=
  TupleIsomorphism.ofDisplayed
    (groupCoordinates iota psi g a W V hpair R R') eBase eLocal
    (displayedBaseEquiv_square iota psi g a)
    (displayedIntersectionEquiv_square iota psi g a W V hpair)
    (rootCompatibleAlong_transport iota iota
      (coordinateAutomorphism g a).toMonoidHom
      (OddTwoActualStabilizerTriple.baseEquiv iota action psi)
      (OddTwoActualStabilizerTriple.baseEquiv iota action psi')
      (eBase).toMonoidHom (base_transport_square iota psi g a) ambientRoots)
    (rootCompatibleAlong_transport
      (ownReductionRoot W R) (ownReductionRoot V R')
      (ownNormalizerEquiv W V (coordinateAutomorphism g a) hpair).toMonoidHom
      (normalizerEquivIntersection iota action psi W)
      (normalizerEquivIntersection iota action psi' V)
      (eLocal).toMonoidHom (local_transport_square iota psi g a W V hpair) normalizerRoots)
    (values_transport iota iota (coordinateAutomorphism g a).toMonoidHom
      (OddTwoActualStabilizerTriple.baseEquiv iota action psi)
      (OddTwoActualStabilizerTriple.baseEquiv iota action psi')
      (eBase).toMonoidHom (base_transport_square iota psi g a) psi psi'
      (fun x => (globalBrauer_coordinate_values iota g a psi x).symm))
    (values_transport (ownReductionRoot W R) (ownReductionRoot V R')
      (ownNormalizerEquiv W V (coordinateAutomorphism g a) hpair).toMonoidHom
      (normalizerEquivIntersection iota action psi W)
      (normalizerEquivIntersection iota action psi' V)
      (eLocal).toMonoidHom (local_transport_square iota psi g a W V hpair)
      (ownReductionBrauer W R) (ownReductionBrauer V R')
      (ownBrauer_character_values W V (coordinateAutomorphism g a) hpair R R'))

/-- The actual equal ambient root supplies its own square in K. Only the
horizontal own-normalizer square remains for the common-root supplier. -/
def tupleIsomorphism_of_normalizerRoots :
    TupleIsomorphism (arguments iota action psi W R)
      (arguments iota action psi' V R') :=
  tupleIsomorphism iota psi g a W V hpair R R'
    (ambient_root_compatible iota g a) normalizerRoots

include g hpair normalizerRoots in
/-- The universal authentic standard interpretation is consumed only
after the actual tuple packet is constructed. Neither relation is an
input to the packet, and this iff does not assert either side. -/
theorem blockIsomorphic_iff (standard : BlockTripleSourceSemantics p k K)
    (source : StandardTransportSource standard) :
    standard.blockIsomorphic (arguments iota action psi W R) ↔
      standard.blockIsomorphic (arguments iota action psi' V R') :=
  source.relation_iff _ _
    (tupleIsomorphism_of_normalizerRoots iota psi g a W V hpair R R' normalizerRoots)

end ModularRep.PaperProofs.OddTwoActualTupleAutomorphismTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
