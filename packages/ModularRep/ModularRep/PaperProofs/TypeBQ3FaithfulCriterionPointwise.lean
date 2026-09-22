import ModularRep.PaperProofs.TypeBQ3FaithfulCriterionAmbient
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction

/-!
# The complete identity-ambient clause for a prescribed faithful-block weight

The global character is the original one and the local character is its
prescribed weight's canonical quotient reduction inflated to the normalizer.
The original group is the entire base, so its top block datum supplies every
intermediate clause. The top datum is an internally derived block calculation.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBQ3FaithfulCriterionPointwise

open ModularRep
open TypeBQ3PrincipalCriterionData TypeBQ3PrincipalPairBlockChoice
open TypeBQ3FaithfulCriterionAmbient
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction

variable {k K X : Type} [Field k] [Field K] [Group X] [Finite X]
  [CharP k 2] [IsAlgClosed k] [CharZero K]

local instance groupFintype (T : Type) [Group T] [Finite T] : Fintype T :=
  Fintype.ofFinite T

local instance twoPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable (root : PrimeRegularRootEmbedding 2 k K X) (phi : IBr root)
  (W : CharacterWeight 2 K X)
  (centrePrimeTo : Nat.Coprime 2 (Nat.card (Subgroup.center X)))
  (inertiaInner : MulAction.stabilizer (MulAut X)ᵐᵒᵖ phi ≤
    (RepresentationWeight.innerInverseOpHom (G := X)).range)

/-- The equality changes only the dependent type of the same local data. -/
private def assemble
    (D : Subgroup X)
    (hD : D = localGroup W (⊤ : Subgroup X) (identityBaseEquiv X))
    (localMap : Subgroup.normalizer (W.subgroup : Set X) →* D)
    (natural : D.subtype.comp localMap =
      (baseEmbedding (⊤ : Subgroup X) (identityBaseEquiv X)).comp
        (Subgroup.normalizer (W.subgroup : Set X)).subtype)
    (range : localMap.range = (⊤ : Subgroup X).comap D.subtype)
    (localRoot : PrimeRegularRootEmbedding 2 k K D)
    (localCharacter : IBr localRoot)
    (localValues : ∀ n : PrimeRegularElement
        (G := Subgroup.normalizer (W.subgroup : Set X)) 2,
      localCharacter.val (PrimeRegularElement.map localMap n) =
        W.localCharacter (QuotientGroup.mk n.val))
    (topData : IntermediateBlockData 2 k K D phi.val localCharacter.val
      (⊤ : Subgroup X)) :
    PrincipalClauseIII root phi W := by
  subst D
  refine {
    A := X
    base := ⊤
    eBase := identityBaseEquiv X
    baseCentralizer_eq_center := identityBaseCentralizer X
    centerPrimeTo := centrePrimeTo
    originalConjugation := MulAut.conj
    conjugation_on_base := identityBase_conjugation X
    automorphismQuotientEquiv :=
      quotientEquiv_of_inertia_le_inner root phi inertiaInner
    automorphismQuotientEquiv_natural := quotientEquiv_natural root phi inertiaInner
    globalRoot := root
    globalCharacter := phi
    globalRestriction := ?_
    localMap := localMap
    localMap_natural := natural
    localMap_range := range
    localRoot := localRoot
    localCharacter := localCharacter
    localRestriction := localValues
    intermediate := ?_ }
  · apply PrimeRegularClassFunction.ext
    intro x
    rfl
  · intro J hJ
    have same : J = ⊤ := identityBase_intermediate_eq_top J hJ
    subst J
    exact topData

/-- The already derived top block calculation completes the identity ambient. -/
def of_top_data
    (reduction : CanonicalRawReduction root W)
    (topData : IntermediateBlockData 2 k K
      (Subgroup.normalizer (W.subgroup : Set X)) phi.val reduction.localBrauer.val
      (⊤ : Subgroup X)) :
    PrincipalClauseIII root phi W := by
  refine assemble root phi W centrePrimeTo inertiaInner
    (Subgroup.normalizer (W.subgroup : Set X)) (identityLocalGroup W).symm
    (MonoidHom.id (Subgroup.normalizer (W.subgroup : Set X))) ?_ ?_
    reduction.normalizerRoot reduction.localBrauer ?_ topData
  · rfl
  · ext n
    constructor
    · intro _
      exact Subgroup.mem_top n.val
    · intro _
      exact ⟨n, rfl⟩
  · intro n
    exact (reduction.localBrauer_reduction n).symm

end ModularRep.PaperProofs.TypeBQ3FaithfulCriterionPointwise


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
