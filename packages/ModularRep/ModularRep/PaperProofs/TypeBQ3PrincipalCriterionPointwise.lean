import ModularRep.PaperProofs.TypeBQ3PrincipalCriterionData
import ModularRep.PaperProofs.TypeBQ3PrincipalCriterionConjugatedAmbient

/-! The complete fixed-block extension clause for a prescribed representative.
The ambient, global extension and local extension are the already constructed
ones. Conjugating the base coordinates identifies their restrictions with
the prescribed weight and keeps every intermediate block equation. -/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBQ3PrincipalCriterionPointwise

open ModularRep CharacterWeight
open TypeBQ3PrincipalCriterionData TypeBQ3PrincipalCriterionRepresentatives
open TypeBQ3PrincipalCriterionConjugatedAmbient
open TypeBQ3PrincipalExtensionApplication TypeBQ3PrincipalPairBlockChoice
open TypeBQ3PrincipalWeightInflation
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierActualNormalizerBase
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction

variable {k K Y : Type} [Field k] [Field K] [Group Y] [Finite Y]
variable [CharP k 2] [IsAlgClosed k] [CharZero K]

local instance groupFintype (T : Type) [Group T] [Finite T] : Fintype T :=
  Fintype.ofFinite T
local instance twoPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable (root : PrimeRegularRootEmbedding 2 k K Y) (phi : IBr root)
  (V : CharacterWeight 2 K Y) (reduction : CanonicalRawReduction root V)
  (hc : Subgroup.center Y = ⊥)
  (packet : MatchedExtensionData root phi V reduction hc)

/-- Equality of the displayed local subgroup transports only its type. -/
private def assemble (x : Y) (U : CharacterWeight 2 K Y)
    (D : Subgroup (ActualAutAmbient root phi))
    (hD : D = localGroup U (actualBase root phi) (baseEquiv root phi hc x))
    (localMap : Subgroup.normalizer (U.subgroup : Set Y) →* D)
    (natural : D.subtype.comp localMap =
      (baseEmbedding (actualBase root phi) (baseEquiv root phi hc x)).comp
        (Subgroup.normalizer (U.subgroup : Set Y)).subtype)
    (range : localMap.range = (actualBase root phi).comap D.subtype)
    (localRoot : PrimeRegularRootEmbedding 2 k K D)
    (localCharacter : IBr localRoot)
    (localValues : ∀ n : PrimeRegularElement
        (G := Subgroup.normalizer (U.subgroup : Set Y)) 2,
      localCharacter.val (PrimeRegularElement.map localMap n) =
        U.localCharacter (QuotientGroup.mk n.val))
    (allIntermediate : ∀ J : Subgroup (ActualAutAmbient root phi),
      actualBase root phi ≤ J → IntermediateBlockData 2 k K D
        packet.globalExtension.val.val localCharacter.val J) :
    PrincipalClauseIII root phi U := by
  subst D
  refine {
    A := ActualAutAmbient root phi
    base := actualBase root phi
    eBase := baseEquiv root phi hc x
    baseCentralizer_eq_center := centralizer_eq_center root phi hc
    centerPrimeTo := center_primeTo root phi hc
    originalConjugation := adjustedConjugation root phi x
    conjugation_on_base := fun a y => base_action root phi x y a
    automorphismQuotientEquiv := quotientEquiv root phi hc x
    automorphismQuotientEquiv_natural := quotientEquiv_natural root phi hc x
    globalRoot := packet.globalRoot
    globalCharacter := packet.globalExtension.val
    globalRestriction := ?_
    localMap := localMap
    localMap_natural := natural
    localMap_range := range
    localRoot := localRoot
    localCharacter := localCharacter
    localRestriction := localValues
    intermediate := allIntermediate }
  apply PrimeRegularClassFunction.ext
  intro y
  exact fixed_direct_global_value_after_conjugation root phi V reduction hc packet x y

/-- The same two extensions satisfy all clauses for the inner-twisted weight. -/
def forInnerTwist (x : Y) :
    PrincipalClauseIII root phi (V.rightTwist (MulAut.conj x)) := by
  refine assemble root phi V reduction hc packet x
    (V.rightTwist (MulAut.conj x))
    (embeddedNormalizer (innerEmbedding root phi) V.subgroup)
    (conjugatedEmbedding_direct_normalizer (innerEmbedding root phi) V x).symm
    (directTwistedLocalMap root phi V (MulAut.conj x)) ?_ ?_
    packet.localRoot packet.localExtension.val
    (fixed_direct_local_value_after_twist root phi V reduction hc packet
      (MulAut.conj x)) packet.intermediate
  · apply MonoidHom.ext
    intro n
    exact directTwistedLocalMap_ambient root phi V x n
  · exact directTwistedLocalMap_range root phi V hc (MulAut.conj x)

include packet in
/-- Equality with the prescribed weight class supplies the required actual
representative; no representative or extension equality is an input. -/
theorem exists_for_prescribed (R : CharacterWeight 2 K Y)
    (sameClass : classOf V = classOf R) :
    Nonempty (PrincipalClauseIII root phi R) := by
  refine Exists.elim (exists_inner_twist_eq V R sameClass) ?_
  intro x hx
  rw [← hx]
  exact ⟨forInnerTwist root phi V reduction hc packet x⟩

end ModularRep.PaperProofs.TypeBQ3PrincipalCriterionPointwise


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
