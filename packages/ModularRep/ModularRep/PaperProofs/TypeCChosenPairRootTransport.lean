import ModularRep.PaperProofs.TypeCSelectedPairGroupEquivCoordinates
import ModularRep.PaperProofs.OddTwoGroupEquivTupleTransport

/-!
# Chosen reductions and actual tuples at the selected whole pair

The ambient convention transported from one fixed source root is independent
of the group equivalence used to reach the same target group. Inner correction
also preserves the transported global class function. These facts identify
the corrected packet with the previously fixed ambient convention and global
character, without comparing independently chosen root embeddings.

The quotient and normalizer reductions below transport the SAME chosen source
packet through a proved equality of whole character pairs. Their actual tuple
isomorphism is consumed only by the existing standard relation interpretation.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeCChosenPairRootTransport

open ModularRep CharacterWeight
open TypeCSelectedPairGroupEquivCoordinates OddTwoGroupEquivOwnReduction
open OddTwoActualStabilizerTriple OddTwoActualCentralInflationPacket
open OddTwoActualLocalBlockSupport OddTwoDefinition35OwnReduction
open OddTwoStandardBlockTripleTransport OddTwoCentralTwoRelationInflation

universe u

variable {p : ℕ} {k K G H : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Group H] [Fintype H]

local instance chosenSubgroupFintype {A : Type u} [Group A] [Finite A]
    (Q : Subgroup A) : Fintype Q := Fintype.ofFinite Q

local instance chosenFiniteAut (A : Type u) [Group A] [Finite A] : Finite (MulAut A) :=
  Finite.of_injective (fun a : MulAut A => (a : A → A)) DFunLike.coe_injective

/-- Both transports use the same source convention and the same cardinality
equality; proof irrelevance identifies those equality proofs. -/
theorem transportedRoot_eq (iota : PrimeRegularRootEmbedding p k K G)
    (e d : G ≃* H) : iota.alongMulEquiv e = iota.alongMulEquiv d := rfl

/-- Inner correction does not alter the already fixed transported root. -/
theorem correctedRoot_eq (iota : PrimeRegularRootEmbedding p k K G)
    (e : G ≃* H) (g : H) :
    iota.alongMulEquiv (correctedEquiv e g) = iota.alongMulEquiv e := rfl

/-- Actual class-function conjugacy invariance removes the inner correction
from the GLOBAL character, while the selected local pair retains it. -/
theorem correctedBrauer_eq (iota : PrimeRegularRootEmbedding p k K G)
    (e : G ≃* H) (g : H) (psi : IBr iota) :
    IrreducibleBrauerCharacter.equivAlongMulEquiv iota (correctedEquiv e g) psi =
      IrreducibleBrauerCharacter.equivAlongMulEquiv iota e psi := by
  apply Subtype.ext
  apply PrimeRegularClassFunction.ext
  intro x
  calc
    _ = (IrreducibleBrauerCharacter.equivAlongMulEquiv iota e psi).1
        ⟨g⁻¹ * x.1 * (g⁻¹)⁻¹, x.2.conj g⁻¹⟩ := by
      change psi.1 _ = psi.1 _
      congr 1
      apply Subtype.ext
      simp [correctedEquiv, PrimeRegularElement.map]
    _ = _ :=
      (IrreducibleBrauerCharacter.equivAlongMulEquiv iota e psi).1.map_conj g⁻¹ x

section Quotient

variable (W : CharacterWeight p K G) (V : CharacterWeight p K H)
variable (e : G ≃* H) (hpair : W.mapGroupEquiv e = V)
variable (rootQ : PrimeRegularRootEmbedding p k K (NormalizerQuotient W.subgroup))
variable (phiQ : IBr rootQ)

/-- The chosen source quotient convention travels through the actual map
to the independently selected whole target pair. -/
def pairQuotientRoot : PrimeRegularRootEmbedding p k K (NormalizerQuotient V.subgroup) :=
  rootQ.alongMulEquiv (pairQuotientEquiv W V e hpair)

def pairQuotientBrauer : IBr (pairQuotientRoot W V e hpair rootQ) :=
  IrreducibleBrauerCharacter.equivAlongMulEquiv rootQ
    (pairQuotientEquiv W V e hpair) phiQ

theorem pairQuotientRoot_lift (z : k) :
    (pairQuotientRoot W V e hpair rootQ).lift z = rootQ.lift z :=
  rootQ.alongMulEquiv_lift (pairQuotientEquiv W V e hpair) z

theorem pairQuotientBrauer_values
    (x : PrimeRegularElement (G := NormalizerQuotient V.subgroup) p) :
    (pairQuotientBrauer W V e hpair rootQ phiQ).1 x =
      phiQ.1 (PrimeRegularElement.map (pairQuotientEquiv W V e hpair).symm.toMonoidHom x) :=
  rfl

/-- The reduction equation is for V's OWN quotient character. -/
theorem pairQuotientBrauer_reduction
    (reduction : ∀ x : PrimeRegularElement (G := NormalizerQuotient W.subgroup) p,
      W.localCharacter x.1 = phiQ.1 x)
    (x : PrimeRegularElement (G := NormalizerQuotient V.subgroup) p) :
    V.localCharacter x.1 = (pairQuotientBrauer W V e hpair rootQ phiQ).1 x := by
  subst V
  exact mappedQuotientBrauer_reduction W e rootQ phiQ reduction x

/-- The quotient square preserves the originally admissible comparison
between the SAME chosen quotient and normalizer roots. -/
theorem pairOwnReduction_quotientCompatible
    (R : OwnNormalizerReduction (k := k) W)
    (rootQ : PrimeRegularRootEmbedding p k K (NormalizerQuotient W.subgroup))
    (compatible : RootCompatibleAlong rootQ (ownReductionRoot W R)
      (normalizerProjection W.subgroup)) :
    RootCompatibleAlong (pairQuotientRoot W V e hpair rootQ)
      (ownReductionRoot V (pairOwnReduction W V e hpair R))
      (normalizerProjection V.subgroup) := by
  subst V
  exact mapOwnReduction_quotientCompatible W e R rootQ compatible

end Quotient

/-- The actual selected normalizer packet is compatible with the ambient
root fixed by the ORIGINAL group map, before inner correction. -/
theorem pairOwnReduction_correctedAmbientCompatible
    (W : CharacterWeight p K G) (V : CharacterWeight p K H)
    (e : G ≃* H) (g : H) (hpair : W.mapGroupEquiv (correctedEquiv e g) = V)
    (R : OwnNormalizerReduction (k := k) W) (iota : PrimeRegularRootEmbedding p k K G)
    (compatible : RootCompatibleAlong iota (ownReductionRoot W R)
      (Subgroup.normalizer (W.subgroup : Set G)).subtype) :
    RootCompatibleAlong (iota.alongMulEquiv e)
      (ownReductionRoot V (pairOwnReduction W V (correctedEquiv e g) hpair R))
      (Subgroup.normalizer (V.subgroup : Set H)).subtype :=
  pairOwnReduction_ambientCompatible W V (correctedEquiv e g) hpair R iota compatible

/-- Whole-pair equality binds the computed tuple to the selected target
pair. The horizontal normalizer square is proved for the chosen transport. -/
def pairTupleIsomorphism
    (iota : PrimeRegularRootEmbedding p k K G) (e : G ≃* H)
    (psi : IBr iota) (W : CharacterWeight p K G) (V : CharacterWeight p K H)
    (hpair : W.mapGroupEquiv e = V) (R : OwnNormalizerReduction (k := k) W) :
    TupleIsomorphism (arguments iota (MonoidHom.id (MulAut G)) psi W R)
      (arguments (iota.alongMulEquiv e) (MonoidHom.id (MulAut H))
        (IrreducibleBrauerCharacter.equivAlongMulEquiv iota e psi)
        V (pairOwnReduction W V e hpair R)) := by
  subst V
  exact OddTwoGroupEquivTupleTransport.tupleIsomorphism iota e psi W R
    (mapOwnReduction W e R) (mapOwnReduction_horizontal W e R)

/-- The selected tuple now uses the original fixed ambient root and global
character. Its local pair and maps retain the actual inner correction. -/
def correctedTupleIsomorphism
    (iota : PrimeRegularRootEmbedding p k K G) (e : G ≃* H) (g : H)
    (psi : IBr iota) (W : CharacterWeight p K G) (V : CharacterWeight p K H)
    (hpair : W.mapGroupEquiv (correctedEquiv e g) = V)
    (R : OwnNormalizerReduction (k := k) W) :
    TupleIsomorphism (arguments iota (MonoidHom.id (MulAut G)) psi W R)
      (arguments (iota.alongMulEquiv e) (MonoidHom.id (MulAut H))
        (IrreducibleBrauerCharacter.equivAlongMulEquiv iota e psi)
        V (pairOwnReduction W V (correctedEquiv e g) hpair R)) := by
  have t := pairTupleIsomorphism iota (correctedEquiv e g) psi W V hpair R
  simp only [correctedBrauer_eq] at t
  simpa only [correctedRoot_eq] using t

/-- Apply the existing authentic standard interpretation to the computed
selected tuple. This equivalence does not assume or assert either relation. -/
theorem corrected_blockIsomorphic_iff
    (iota : PrimeRegularRootEmbedding p k K G) (e : G ≃* H) (g : H)
    (psi : IBr iota) (W : CharacterWeight p K G) (V : CharacterWeight p K H)
    (hpair : W.mapGroupEquiv (correctedEquiv e g) = V)
    (R : OwnNormalizerReduction (k := k) W)
    (standard : BlockTripleSourceSemantics p k K)
    (source : StandardTransportSource standard) :
    standard.blockIsomorphic (arguments iota (MonoidHom.id (MulAut G)) psi W R) ↔
      standard.blockIsomorphic (arguments (iota.alongMulEquiv e)
        (MonoidHom.id (MulAut H))
        (IrreducibleBrauerCharacter.equivAlongMulEquiv iota e psi)
        V (pairOwnReduction W V (correctedEquiv e g) hpair R)) :=
  source.relation_iff _ _ (correctedTupleIsomorphism iota e g psi W V hpair R)

end ModularRep.PaperProofs.TypeCChosenPairRootTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
