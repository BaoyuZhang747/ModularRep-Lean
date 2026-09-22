import ModularRep.PaperProofs.OddTwoGroupEquivRawTupleCoordinates
import ModularRep.PaperProofs.OddTwoActualCentralInflationPacket

/-!
# Actual own-character tuple transport along a group equivalence

The ambient and subgroup maps are the already computed coordinates for e
and the literal OWN image pair mapGroupEquiv W e. The global Brauer values
come from the actual alongMulEquiv transport. The local Brauer values are
derived from BOTH own reduction equations and the same normalizer values
which define that raw image pair.

The ambient root square is K because alongMulEquiv preserves the lift.
Only the horizontal own-normalizer root square is an explicit conditional
K argument. It is not inferred from equal values and is not a new source
law. The resulting actual TupleIsomorphism is then consumed by the existing
universal authentic standard relation interpretation. Neither relation,
an FLZ predicate, nor a selected-representative correction is assumed.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoGroupEquivTupleTransport

open ModularRep.CharacterWeight
open ModularRep.PaperProofs.OddTwoActualStabilizerTriple
open ModularRep.PaperProofs.OddTwoGroupEquivHolomorphCoordinates
open ModularRep.PaperProofs.OddTwoGroupEquivRawTupleCoordinates
open ModularRep.PaperProofs.OddTwoStandardBlockTripleTransport
open ModularRep.PaperProofs.OddTwoActualCentralInflationPacket
open ModularRep.PaperProofs.OddTwoActualLocalBlockSupport
open ModularRep.PaperProofs.OddTwoCentralTwoRelationInflation

universe u

variable {p : ℕ} {k K G H : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Group H] [Fintype H]

local instance finiteTransportAut (J : Type u) [Group J] [Finite J] : Finite (MulAut J) :=
  Finite.of_injective (fun a : MulAut J => (a : J → J)) DFunLike.coe_injective

variable (iota : PrimeRegularRootEmbedding p k K G) (e : G ≃* H)
variable (psi : IBr iota) (W : CharacterWeight p K G)

local notation "iotaH" => iota.alongMulEquiv e
local notation "psiH" => IrreducibleBrauerCharacter.equivAlongMulEquiv iota e psi
local notation "WH" => W.mapGroupEquiv e
local notation "actionG" => MonoidHom.id (MulAut G)
local notation "actionH" => MonoidHom.id (MulAut H)
local notation "eBase" => baseKernelEquiv iota e psi
local notation "eLocal" => displayedIntersectionEquiv iota e psi W

/-- The actual transported ambient root supplies its horizontal square
on every target representation, without any root-identification premise. -/
theorem ambient_root_compatible :
    RootCompatibleAlong iotaH iota e.toMonoidHom := by
  intro A x z
  exact (iota.alongMulEquiv_lift e z.1).symm

/-- The global values are the actual pullback through e's inverse. -/
theorem global_character_values (x : PrimeRegularElement (G := G) p) :
    psi.1 x = psiH.1 (PrimeRegularElement.map e.toMonoidHom x) := by
  change psi.1 x = psi.1 (PrimeRegularElement.map e.symm.toMonoidHom
    (PrimeRegularElement.map e.toMonoidHom x))
  congr 1
  apply Subtype.ext
  exact (e.symm_apply_apply x.1).symm

/-- Both own reduction equations identify the local Brauer values through
the SAME actual normalizer map as mapGroupEquiv W e. Equal values alone
make no assertion about compatibility of the two chosen root conventions. -/
theorem own_character_values
    (e : G ≃* H) (W : CharacterWeight p K G)
    (R : OwnNormalizerReduction (k := k) W)
    (R' : OwnNormalizerReduction (k := k) (W.mapGroupEquiv e))
    (x : PrimeRegularElement (G := Subgroup.normalizer (W.subgroup : Set G)) p) :
    (ownReductionBrauer (k := k) W R).1 x =
      (ownReductionBrauer (k := k) (W.mapGroupEquiv e) R').1
        (PrimeRegularElement.map (ModularRep.normalizerEquiv e W.subgroup).toMonoidHom x) := by
  calc
    (ownReductionBrauer (k := k) W R).1 x = W.localCharacter (QuotientGroup.mk x.1) :=
      (ownReductionValues (k := k) W R x).symm
    _ = (W.mapGroupEquiv e).localCharacter
        (QuotientGroup.mk (ModularRep.normalizerEquiv e W.subgroup x.1)) :=
      (mapGroupEquiv_normalizer_values W e x.1).symm
    _ = (ownReductionBrauer (k := k) (W.mapGroupEquiv e) R').1
        (PrimeRegularElement.map (ModularRep.normalizerEquiv e W.subgroup).toMonoidHom x) :=
      ownReductionValues (k := k) (W.mapGroupEquiv e) R'
        (PrimeRegularElement.map (ModularRep.normalizerEquiv e W.subgroup).toMonoidHom x)

/-- Conditional K construction on the ACTUAL two tuples. Its sole root
argument is the exact horizontal own-normalizer square, target root first.
Every group map, remaining root square and character value is derived. -/
def tupleIsomorphism
    (iota : PrimeRegularRootEmbedding p k K G) (e : G ≃* H)
    (psi : IBr iota) (W : CharacterWeight p K G)
    (R : OwnNormalizerReduction (k := k) W)
    (R' : OwnNormalizerReduction (k := k) (W.mapGroupEquiv e))
    (normalizerRoots : RootCompatibleAlong
      (ownReductionRoot (k := k) (W.mapGroupEquiv e) R')
      (ownReductionRoot (k := k) W R)
      (ModularRep.normalizerEquiv e W.subgroup).toMonoidHom) :
    TupleIsomorphism (arguments iota (MonoidHom.id (MulAut G)) psi W R)
      (arguments (iota.alongMulEquiv e) (MonoidHom.id (MulAut H))
        (IrreducibleBrauerCharacter.equivAlongMulEquiv iota e psi)
        (W.mapGroupEquiv e) R') :=
  TupleIsomorphism.ofDisplayed
    (groupCoordinates iota e psi W R R')
    (baseKernelEquiv iota e psi) (displayedIntersectionEquiv iota e psi W)
    (baseKernelEquiv_ambient iota e psi)
    (displayedIntersectionEquiv_square iota e psi W)
    (rootCompatibleAlong_transport iota (iota.alongMulEquiv e) e.toMonoidHom
      (OddTwoActualStabilizerTriple.baseEquiv iota (MonoidHom.id (MulAut G)) psi)
      (OddTwoActualStabilizerTriple.baseEquiv (iota.alongMulEquiv e)
        (MonoidHom.id (MulAut H))
        (IrreducibleBrauerCharacter.equivAlongMulEquiv iota e psi))
      (baseKernelEquiv iota e psi).toMonoidHom (baseKernelEquiv_base_square iota e psi)
      (ambient_root_compatible iota e))
    (rootCompatibleAlong_transport
      (ownReductionRoot (k := k) W R)
      (ownReductionRoot (k := k) (W.mapGroupEquiv e) R')
      (ModularRep.normalizerEquiv e W.subgroup).toMonoidHom
      (normalizerEquivIntersection iota (MonoidHom.id (MulAut G)) psi W)
      (normalizerEquivIntersection (iota.alongMulEquiv e) (MonoidHom.id (MulAut H))
        (IrreducibleBrauerCharacter.equivAlongMulEquiv iota e psi) (W.mapGroupEquiv e))
      (displayedIntersectionEquiv iota e psi W).toMonoidHom
      (displayedIntersectionEquiv_normalizer_square iota e psi W)
      normalizerRoots)
    (values_transport iota (iota.alongMulEquiv e) e.toMonoidHom
      (OddTwoActualStabilizerTriple.baseEquiv iota (MonoidHom.id (MulAut G)) psi)
      (OddTwoActualStabilizerTriple.baseEquiv (iota.alongMulEquiv e)
        (MonoidHom.id (MulAut H))
        (IrreducibleBrauerCharacter.equivAlongMulEquiv iota e psi))
      (baseKernelEquiv iota e psi).toMonoidHom
      (baseKernelEquiv_base_square iota e psi) psi
      (IrreducibleBrauerCharacter.equivAlongMulEquiv iota e psi)
      (global_character_values iota e psi))
    (values_transport (ownReductionRoot (k := k) W R)
      (ownReductionRoot (k := k) (W.mapGroupEquiv e) R')
      (ModularRep.normalizerEquiv e W.subgroup).toMonoidHom
      (normalizerEquivIntersection iota (MonoidHom.id (MulAut G)) psi W)
      (normalizerEquivIntersection (iota.alongMulEquiv e) (MonoidHom.id (MulAut H))
        (IrreducibleBrauerCharacter.equivAlongMulEquiv iota e psi) (W.mapGroupEquiv e))
      (displayedIntersectionEquiv iota e psi W).toMonoidHom
      (displayedIntersectionEquiv_normalizer_square iota e psi W)
      (ownReductionBrauer (k := k) W R)
      (ownReductionBrauer (k := k) (W.mapGroupEquiv e) R')
      (own_character_values (k := k) e W R R'))

/-- The existing universal standard interpretation is applied only after
the actual packet is computed. This iff asserts neither relation and
introduces no additional source or desired-covariance premise. -/
theorem blockIsomorphic_iff
    (iota : PrimeRegularRootEmbedding p k K G) (e : G ≃* H)
    (psi : IBr iota) (W : CharacterWeight p K G)
    (R : OwnNormalizerReduction (k := k) W)
    (R' : OwnNormalizerReduction (k := k) (W.mapGroupEquiv e))
    (normalizerRoots : RootCompatibleAlong
      (ownReductionRoot (k := k) (W.mapGroupEquiv e) R')
      (ownReductionRoot (k := k) W R)
      (ModularRep.normalizerEquiv e W.subgroup).toMonoidHom)
    (standard : BlockTripleSourceSemantics p k K)
    (source : StandardTransportSource standard) :
    standard.blockIsomorphic (arguments iota (MonoidHom.id (MulAut G)) psi W R) ↔
      standard.blockIsomorphic (arguments (iota.alongMulEquiv e)
        (MonoidHom.id (MulAut H))
        (IrreducibleBrauerCharacter.equivAlongMulEquiv iota e psi)
        (W.mapGroupEquiv e) R') :=
  source.relation_iff _ _ (tupleIsomorphism iota e psi W R R' normalizerRoots)

end ModularRep.PaperProofs.OddTwoGroupEquivTupleTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
