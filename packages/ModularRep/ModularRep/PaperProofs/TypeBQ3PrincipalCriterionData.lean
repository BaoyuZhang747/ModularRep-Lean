import ModularRep.WeightCharacterBridge
import ModularRep.PaperProofs.TypeBQ3PrincipalPairBlockChoice
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient

/-! The extension clause for one prescribed weight of a fixed block.
The base embedding and its local normalizer are computed from the displayed
base equivalence. All character and intermediate block data are outputs. -/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBQ3PrincipalCriterionData

open ModularRep
open TypeBQ3PrincipalPairBlockChoice
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient

variable {k K Y : Type} [Field k] [Field K] [Group Y] [Finite Y]
variable [CharP k 2] [IsAlgClosed k] [CharZero K]

local instance groupFintype (T : Type) [Group T] [Finite T] : Fintype T :=
  Fintype.ofFinite T

local instance twoPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The base equivalence determines the ambient embedding. -/
def baseEmbedding {A : Type} [Group A] (base : Subgroup A)
    (eBase : Y ≃* base) : Y →* A :=
  base.subtype.comp eBase.toMonoidHom

/-- The prescribed radical determines its ambient local group. -/
def localGroup (U : CharacterWeight 2 K Y) {A : Type} [Group A]
    (base : Subgroup A) (eBase : Y ≃* base) : Subgroup A :=
  Subgroup.normalizer (U.subgroup.map (baseEmbedding base eBase) : Set A)

/-- Literal extension and block data for the centre-faithful criterion carrier. -/
structure PrincipalClauseIII (root : PrimeRegularRootEmbedding 2 k K Y)
    (phi : IBr root) (U : CharacterWeight 2 K Y) where
  A : Type
  [groupA : Group A]
  [finiteA : Finite A]
  base : Subgroup A
  [baseNormal : base.Normal]
  eBase : Y ≃* base
  baseCentralizer_eq_center :
    Subgroup.centralizer (base : Set A) = Subgroup.center A
  centerPrimeTo : Nat.Coprime 2 (Nat.card (Subgroup.center A))
  originalConjugation : A →* MulAut Y
  conjugation_on_base : ∀ (a : A) (y : Y),
    baseEmbedding base eBase (originalConjugation a y) =
      a * baseEmbedding base eBase y * a⁻¹
  automorphismQuotientEquiv : A ⧸ Subgroup.center A ≃* ActualAutAmbient root phi
  automorphismQuotientEquiv_natural : ∀ a : A,
    (automorphismQuotientEquiv (QuotientGroup.mk' (Subgroup.center A) a)).val =
      CyclicOuterLemma37Concrete.inverseOpHom originalConjugation a
  globalRoot : PrimeRegularRootEmbedding 2 k K A
  globalCharacter : IBr globalRoot
  globalRestriction :
    PrimeRegularClassFunction.pullback (baseEmbedding base eBase) globalCharacter.val =
      phi.val
  localMap : Subgroup.normalizer (U.subgroup : Set Y) →* localGroup U base eBase
  localMap_natural : (localGroup U base eBase).subtype.comp localMap =
    (baseEmbedding base eBase).comp (Subgroup.normalizer (U.subgroup : Set Y)).subtype
  localMap_range : localMap.range = base.comap (localGroup U base eBase).subtype
  localRoot : PrimeRegularRootEmbedding 2 k K (localGroup U base eBase)
  localCharacter : IBr localRoot
  localRestriction : ∀ n : PrimeRegularElement
      (G := Subgroup.normalizer (U.subgroup : Set Y)) 2,
    localCharacter.val (PrimeRegularElement.map localMap n) =
      U.localCharacter (QuotientGroup.mk n.val)
  intermediate : ∀ J : Subgroup A, base ≤ J →
    IntermediateBlockData 2 k K (localGroup U base eBase)
      globalCharacter.val localCharacter.val J

end ModularRep.PaperProofs.TypeBQ3PrincipalCriterionData


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
