import ModularRep.CharacterWeightBlockAssignment
import ModularRep.CharacterWeightRadicalProjection
import ModularRep.EvenCondition61
import ModularRep.EvenUnipotentIBrBlockAssembly
import ModularRep.PaperProofs.EvenFieldFrobeniusPowers
import ModularRep.PaperProofs.EvenFieldLemmas35_36Actual

/-!
# Proposition 3.8 on the literal set of Alperin weights

This module instantiates the even-field Proposition 3.8 adapter on
`CharacterWeight.ConjugacyClass`.  The action of the field group is not a
separate input: it is the restriction of the canonical right automorphism
transport along `oppositeFieldAction`.  Likewise, the weight-to-block map is
definitionally `LocalBlockInductionSource.weightBlock`, obtained from the
local-character block, inflation to the normaliser, and block induction.
The radical carrier is literally `CharacterWeight.RadicalConjugacyClass`;
its action and the projection from weights are the reusable canonical ones.
The designated `Q = 1` class is built from the source proof that the trivial
subgroup is radical, and its field invariance is proved rather than supplied.

The K-level theorem takes a one-field source containing only naturality of the
literal Brauer block assignment.  The step from generic weights to Alperin
weights is a restricted E2/U application of Feng--Malle--Zhang, Theorem 6.2,
whose source carriers, field action, and Condition 6.1 matching are explicit.
The only exported conclusion is the protected literal block-fibre theorem.
No broad context or complete-witness wrapper is exported, and the theorem
does not assume an `IBr`-to-weight bijection, BAW-goodness, iBAW, or its own
conclusion.
-/

namespace ModularRep.PaperProofs.EvenFieldConcreteProposition38Actual

open scoped MonoidAlgebra

open Formalisation
open Formalisation.IBAW
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.IBrBlockBasicSetBridge
open ModularRep.IBrBlockBasicSetBridge.RestrictedIntegralBasicSetOnIBrBlock
open ModularRep.IntegralBasicSetBridge
open ModularRep.ManuscriptVerification.EvenUnipotentCorrespondence
open ModularRep.ManuscriptVerification.EvenUnipotentAssembly
open ModularRep.ManuscriptVerification.EvenUnipotentIBAW
open ModularRep.ManuscriptVerification.EvenUnipotentIBrBlockAssembly
open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPair
open ModularRep.PaperProofs.EvenFieldConcreteLemma35
open ModularRep.PaperProofs.EvenFieldConcreteTypeC
open ModularRep.PaperProofs.EvenFieldEJGCPairActual
open ModularRep.PaperProofs.EvenFieldFMZGenericPair
open ModularRep.PaperProofs.EvenFieldLemma35E1E4Providers
open ModularRep.PaperProofs.EvenFieldOrdinaryCharacters

noncomputable section

/-- The literal set of Alperin weights for the fixed-point group. -/
abbrev ActualWeight (ell : ℕ) (K : Type) [Field K] [CharZero K]
    (r a : ℕ) [Fintype (FiniteSymplecticFixed r a)] :=
  CharacterWeight.ConjugacyClass
    (p := ell) (K := K) (G := FiniteSymplecticFixed r a)

/-- Literal conjugacy classes of radical subgroups of the fixed-point
group. -/
abbrev ActualRadical (ell r a : ℕ) :=
  CharacterWeight.RadicalConjugacyClass
    (p := ell) (G := FiniteSymplecticFixed r a)

/-- The ambient central character used by the actual e-JGC pair source.
The stored finite block instance is installed explicitly so this definition
does not depend on a second enumeration of the same set of blocks. -/
noncomputable def pairAmbientCentralCharacter
    {H A ι k : Type} [Group H] [Fintype H]
    [MulAction (MulAut H) A]
    {ell : ℕ} [Field k] [CharP k ell] [IsAlgClosed k]
    {D : Definitions ℂ H A ι}
    (pairs : PairClassSource ell k D) (B : ι) :
    GroupAlgebraCenter k H →ₐ[k] k := by
  letI : Fintype ι :=
    pairs.blockInduction.ambient.fintypeBlock
  exact pairs.blockInduction.ambient.catalogue.centralCharacter B

/-- The ambient central character used by literal weight block induction.
The stored finite block instance is installed explicitly. -/
noncomputable def weightAmbientCentralCharacter
    {H K k ι : Type} [Group H] [Fintype H]
    [Field K] [CharZero K] [Field k] [IsAlgClosed k]
    [MulAction (MulAut H)ᵐᵒᵖ ι]
    {ell : ℕ}
    (blockSource : LocalBlockInductionSource
      (p := ell) (k := k) (K := K) (G := H) (Block := ι))
    (B : ι) : GroupAlgebraCenter k H →ₐ[k] k := by
  letI : Fintype ι :=
    blockSource.operations.ambientBlockData.fintypeBlock
  exact
    blockSource.operations.ambientBlockData.catalogue.centralCharacter B

/-- The three ambient block descriptions used in the actual Proposition 3.8
endpoint have the same labels, idempotents, and central characters.

The first two fields align the e-JGC pair source with literal weight block
induction.  The last aligns the decomposition used to define `IBr(block)`
with that same literal catalogue.  This source contains no block selector or
character-weight correspondence. -/
structure AmbientBlockAlignment
    {H A K k ι : Type} [Group H] [Fintype H]
    [MulAction (MulAut H) A]
    [Field K] [CharZero K] [Field k] [IsAlgClosed k]
    [MulAction (MulAut H)ᵐᵒᵖ ι]
    {ell : ℕ} [CharP k ell]
    (D : Definitions ℂ H A ι)
    (pairs : PairClassSource ell k D)
    (blockIdempotent : ι → k[H])
    (blockSource : LocalBlockInductionSource
      (p := ell) (k := k) (K := K) (G := H) (Block := ι)) : Prop where
  pair_idempotent : ∀ B : ι,
    pairs.blockInduction.ambient.blockIdempotent B =
      blockSource.operations.ambientBlockData.blockIdempotent B
  pair_centralCharacter : ∀ B : ι,
    pairAmbientCentralCharacter pairs B =
      weightAmbientCentralCharacter blockSource B
  brauer_idempotent : ∀ B : ι,
    blockIdempotent B =
      blockSource.operations.ambientBlockData.blockIdempotent B

/-- The field action on literal weights, obtained only by restricting the
canonical opposite-automorphism action along `oppositeFieldAction`. -/
@[instance_reducible]
def oppositeFieldWeightMulAction
    (r a ell : ℕ) (ha : 0 < a)
    (K : Type) [Field K] [CharZero K]
    [Fintype (FiniteSymplecticFixed r a)] :
    MulAction (FieldGroup a)ᵐᵒᵖ
      (ActualWeight ell K r a) :=
  MulAction.compHom _ (oppositeFieldAction r a ha)

/-- The field action on literal radical-subgroup conjugacy classes, obtained
by restricting canonical opposite-automorphism transport. -/
@[instance_reducible]
def oppositeFieldRadicalMulAction
    (r a ell : ℕ) (ha : 0 < a) :
    MulAction (FieldGroup a)ᵐᵒᵖ (ActualRadical ell r a) :=
  MulAction.compHom _ (oppositeFieldAction r a ha)

/-- The same canonical restriction on an ambient set of blocks. -/
@[instance_reducible]
def oppositeFieldBlockMulAction
    (r a : ℕ) (ha : 0 < a)
    {Block : Type} [MulAction
      (MulAut (FiniteSymplecticFixed r a))ᵐᵒᵖ Block] :
    MulAction (FieldGroup a)ᵐᵒᵖ Block :=
  MulAction.compHom Block (oppositeFieldAction r a ha)

/-- The canonical field action on function-valued Brauer characters. -/
@[instance_reducible]
def oppositeFieldIBrMulAction
    {K k : Type} [Field K] [Field k]
    {ell r a : ℕ} [CharP k ell] [IsAlgClosed k]
    [CharZero K] [Fintype (FiniteSymplecticFixed r a)]
    (ha : 0 < a)
    (iota : PrimeRegularRootEmbedding ell k K
      (FiniteSymplecticFixed r a)) :
    MulAction (FieldGroup a)ᵐᵒᵖ (IBr iota) :=
  MulAction.compHom (IBr iota) (oppositeFieldAction r a ha)

/-- The field group maps to the full automorphism stabiliser of a selected
block whenever that block is field-stable. -/
def oppositeFieldBlockStabilizer
    (r a : ℕ) (ha : 0 < a)
    {Block : Type} [MulAction
      (MulAut (FiniteSymplecticFixed r a))ᵐᵒᵖ Block]
    (block : Block)
    (hfixed : ∀ sigma : (FieldGroup a)ᵐᵒᵖ,
      oppositeFieldAction r a ha sigma • block = block) :
    (FieldGroup a)ᵐᵒᵖ →*
      MulAction.stabilizer
        (MulAut (FiniteSymplecticFixed r a))ᵐᵒᵖ block where
  toFun sigma := ⟨oppositeFieldAction r a ha sigma, hfixed sigma⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (oppositeFieldAction r a ha)
  map_mul' sigma tau := by
    apply Subtype.ext
    exact map_mul (oppositeFieldAction r a ha) sigma tau

/-- The canonical field action on the fibre of the constructed weight-block
map.  It is the pullback of the already constructed full block-stabiliser
action, so no action on the fibre is supplied by the application. -/
@[instance_reducible]
def oppositeFieldWeightFibreMulAction
    {K k Block : Type} [Field K] [Field k] [CharZero K]
    {ell r a : ℕ} [Fintype (FiniteSymplecticFixed r a)]
    [MulAction (MulAut (FiniteSymplecticFixed r a))ᵐᵒᵖ Block]
    (ha : 0 < a)
    (blockSource : LocalBlockInductionSource
      (p := ell) (k := k) (K := K)
      (G := FiniteSymplecticFixed r a) (Block := Block))
    (block : Block)
    (hfixed : ∀ sigma : (FieldGroup a)ᵐᵒᵖ,
      oppositeFieldAction r a ha sigma • block = block) :
    MulAction (FieldGroup a)ᵐᵒᵖ (blockSource.Fibre block) :=
  MulAction.compHom (blockSource.Fibre block)
    (oppositeFieldBlockStabilizer r a ha block hfixed)

@[simp]
theorem oppositeFieldWeightFibre_smul_val
    {K k Block : Type} [Field K] [Field k] [CharZero K]
    {ell r a : ℕ} [Fintype (FiniteSymplecticFixed r a)]
    [MulAction (MulAut (FiniteSymplecticFixed r a))ᵐᵒᵖ Block]
    (ha : 0 < a)
    (blockSource : LocalBlockInductionSource
      (p := ell) (k := k) (K := K)
      (G := FiniteSymplecticFixed r a) (Block := Block))
    (block : Block)
    (hfixed : ∀ sigma : (FieldGroup a)ᵐᵒᵖ,
      oppositeFieldAction r a ha sigma • block = block)
    (sigma : (FieldGroup a)ᵐᵒᵖ) (w : blockSource.Fibre block) :
    let _ : MulAction (FieldGroup a)ᵐᵒᵖ
        (blockSource.Fibre block) :=
      oppositeFieldWeightFibreMulAction ha blockSource block hfixed
    (sigma • w).1 = oppositeFieldAction r a ha sigma • w.1 := by
  exact blockSource.fibre_smul_val block
    ⟨oppositeFieldAction r a ha sigma, hfixed sigma⟩ w

/-- The exact group-carrier match underlying the type-C algebraic source.

This group equivalence is not asserted to be an equivalence of algebraic
groups and does not by itself prove the type-C or nontriality hypotheses.
Those are the named E1/U interpretation of the surrounding Condition 6.1
source; see source-registry entry `SF-C-SC-ALGEBRAIC-MODEL`. -/
structure FMZ62AlgebraicCarrierSourceMatch
    (r : ℕ) (G : Type) [Group G] : Type where
  typeCModelEquiv : G ≃* AmbientSymplectic r

/-- The carrier for the algebraic fixed centre `Z(𝔾)^F` in Condition 6.1.

It is intentionally not identified with `Subgroup.center (FiniteSymplecticFixed
r a)`: these are different objects in general.  The source centre, its
Frobenius, and its inclusion into the same source fixed-point group are all
typed explicitly.  Calling the supplied subgroup the algebraic centre remains
the named E1/U source interpretation.  Its image is nevertheless required to
be the literal group centre of the exact algebraic carrier, so this is not a
free central subgroup. -/
structure FMZ62AlgebraicCentreFixedSource
    (G : Type) [Group G] (baseFrobenius : G →* G) (a : ℕ) : Type 1 where
  FMZAlgebraicCentre : Type
  [groupFMZAlgebraicCentre : Group FMZAlgebraicCentre]
  centreInclusion : FMZAlgebraicCentre →* G
  centreInclusion_injective : Function.Injective centreInclusion
  centreInclusion_range : MonoidHom.range centreInclusion = Subgroup.center G
  FMZCentreBaseFrobenius : FMZAlgebraicCentre →* FMZAlgebraicCentre
  centreFrobenius_natural : ∀ z : FMZAlgebraicCentre,
    centreInclusion (FMZCentreBaseFrobenius z) =
      baseFrobenius (centreInclusion z)

attribute [instance]
  FMZ62AlgebraicCentreFixedSource.groupFMZAlgebraicCentre

/-- Frobenius naturality of the exact algebraic-centre inclusion persists
through every iterate. -/
theorem FMZ62AlgebraicCentreFixedSource.centreInclusion_iterate_natural
    {G : Type} [Group G] {baseFrobenius : G →* G} {a : ℕ}
    (source : FMZ62AlgebraicCentreFixedSource G baseFrobenius a)
    (n : ℕ) (z : source.FMZAlgebraicCentre) :
    source.centreInclusion
        (ModularRep.PaperProofs.EvenFieldFrobeniusPowers.iterateMonoidHom
          source.FMZCentreBaseFrobenius n z) =
      ModularRep.PaperProofs.EvenFieldFrobeniusPowers.iterateMonoidHom
        baseFrobenius n (source.centreInclusion z) := by
  simpa only [ModularRep.PaperProofs.EvenFieldFrobeniusPowers.iterateMonoidHom_apply] using
    (Function.Semiconj.iterate_right source.centreFrobenius_natural n z)

/-- The inclusion of the algebraic fixed centre into the fixed algebraic
group is kernel-constructed from the exact centre inclusion and Frobenius
naturality; it is not an independent source clause. -/
def FMZ62AlgebraicCentreFixedSource.centreFixedInclusion
    {G : Type} [Group G] {baseFrobenius : G →* G} {a : ℕ}
    (source : FMZ62AlgebraicCentreFixedSource G baseFrobenius a) :
    ModularRep.PaperProofs.EvenFieldCyclicFieldAction.FixedPoints
        source.FMZCentreBaseFrobenius a →*
      ModularRep.PaperProofs.EvenFieldCyclicFieldAction.FixedPoints
        baseFrobenius a where
  toFun z := ⟨source.centreInclusion z, by
    change ModularRep.PaperProofs.EvenFieldFrobeniusPowers.iterateMonoidHom
        baseFrobenius a (source.centreInclusion z) = source.centreInclusion z
    rw [← source.centreInclusion_iterate_natural]
    exact congrArg source.centreInclusion z.property⟩
  map_one' := by
    apply Subtype.ext
    exact source.centreInclusion.map_one
  map_mul' x y := by
    apply Subtype.ext
    exact source.centreInclusion.map_mul x y

@[simp]
theorem FMZ62AlgebraicCentreFixedSource.centreFixedInclusion_coe
    {G : Type} [Group G] {baseFrobenius : G →* G} {a : ℕ}
    (source : FMZ62AlgebraicCentreFixedSource G baseFrobenius a)
    (z : ModularRep.PaperProofs.EvenFieldCyclicFieldAction.FixedPoints
      source.FMZCentreBaseFrobenius a) :
    ((source.centreFixedInclusion z :
      ModularRep.PaperProofs.EvenFieldCyclicFieldAction.FixedPoints
        baseFrobenius a) : G) = source.centreInclusion z :=
  rfl

/-- The non-arithmetic part of the source match needed to apply
Feng--Malle--Zhang, Condition 6.1 in concrete type C.

The simple, simply connected, type-C, and nontriality interpretation, the
base `F_2` Frobenius, regular embedding, and algebraic-centre clauses are all
tied to one algebraic carrier.  Their mathematical source semantics are E1/U
because the local development does not formalise those algebraic predicates.
The displayed group maps and equalities do not pretend to prove the missing
algebraic structure. -/
structure FMZ62TypeCCondition61NonArithmeticSource
    (r a : ℕ) (ha : 0 < a) : Type 1 where
  FMZAlgebraicGroup : Type
  [groupFMZAlgebraicGroup : Group FMZAlgebraicGroup]
  typeCCarrier :
    FMZ62AlgebraicCarrierSourceMatch r FMZAlgebraicGroup
  FMZBaseFrobenius : FMZAlgebraicGroup →* FMZAlgebraicGroup
  baseFrobenius_natural : ∀ x : FMZAlgebraicGroup,
    typeCCarrier.typeCModelEquiv (FMZBaseFrobenius x) =
      ambientFrobenius r (typeCCarrier.typeCModelEquiv x)
  definingFrobenius_fixedPointEquiv :
    ModularRep.PaperProofs.EvenFieldCyclicFieldAction.FixedPoints
        FMZBaseFrobenius a ≃*
      FiniteSymplecticFixed r a
  FMZRegularEmbeddingTarget : Type
  [groupFMZRegularEmbeddingTarget : Group FMZRegularEmbeddingTarget]
  regularEmbedding : FMZAlgebraicGroup →* FMZRegularEmbeddingTarget
  regularEmbedding_injective : Function.Injective regularEmbedding
  FMZRegularTargetBaseFrobenius :
    FMZRegularEmbeddingTarget →* FMZRegularEmbeddingTarget
  regularEmbedding_frobenius_natural : ∀ x : FMZAlgebraicGroup,
    regularEmbedding (FMZBaseFrobenius x) =
      FMZRegularTargetBaseFrobenius (regularEmbedding x)
  regularTargetFieldAction_injective : Function.Injective
    (ModularRep.PaperProofs.EvenFieldCyclicFieldAction.fieldActionHom
      FMZRegularTargetBaseFrobenius a ha)
  algebraicCentreFixed : FMZ62AlgebraicCentreFixedSource
    FMZAlgebraicGroup FMZBaseFrobenius a

attribute [instance]
  FMZ62TypeCCondition61NonArithmeticSource.groupFMZAlgebraicGroup
  FMZ62TypeCCondition61NonArithmeticSource.groupFMZRegularEmbeddingTarget

/-- The concrete good-prime reduction for the already fixed type-C source.
For type `C_r` with `r ≥ 2`, the available numerical content is exactly that
`ell` is odd.  The interpretation as the published good-prime condition is
attached to the same source, not exposed as a generic predicate. -/
structure FMZ62TypeCGoodPrimeSourceClause
    (r a ell : ℕ) (ha : 0 < a)
    (source : FMZ62TypeCCondition61NonArithmeticSource r a ha) : Type 1 where
  ellOdd : Odd ell
  sourceTypeCModel : source.FMZAlgebraicGroup ≃* AmbientSymplectic r
  sourceTypeCModel_eq :
    sourceTypeCModel = source.typeCCarrier.typeCModelEquiv

/-- The concrete, type-C part of Feng--Malle--Zhang, Condition 6.1.

`S35.e1e4.ellPrime` supplies primality.  `typeCGoodPrime.ellOdd` is the
concrete good-prime reduction, while the displayed cardinality is that of the
typed algebraic fixed centre `Z(𝔾)^F`, not of `Z(G^F)`.  The remaining
algebraic semantics are named source clauses inside the exact `nonArithmetic`
object; no BAW or Definition 3.5 predicate occurs here.
-/
structure FMZ62TypeCCondition61Applicability
    {A Dual ι : Type}
    [Group Dual] [Fintype Dual]
    (r a ell : ℕ) (ha : 0 < a)
    [Fintype (FiniteSymplecticFixed r a)]
    [MulAction (MulAut (FiniteSymplecticFixed r a)) A]
    [Fintype ι]
    [MulAction (MulAut (FiniteSymplecticFixed r a))ᵐᵒᵖ ι]
    (D : Definitions ℂ (FiniteSymplecticFixed r a) A ι)
    (coherence : InnerCoherence D) (block : ι)
    (S35 : Inputs (A := A) (Block := ι) (Dual := Dual)
      r a ell ha D coherence block) : Type 1 where
  rankAtLeastTwo : 2 ≤ r
  nonArithmetic : FMZ62TypeCCondition61NonArithmeticSource r a ha
  typeCGoodPrime : FMZ62TypeCGoodPrimeSourceClause
    r a ell ha nonArithmetic
  algebraicCentreFixedFintype : Fintype
    (ModularRep.PaperProofs.EvenFieldCyclicFieldAction.FixedPoints
      nonArithmetic.algebraicCentreFixed.FMZCentreBaseFrobenius a)
  algebraicCentreFixedCard_one :
    @Fintype.card
      (ModularRep.PaperProofs.EvenFieldCyclicFieldAction.FixedPoints
        nonArithmetic.algebraicCentreFixed.FMZCentreBaseFrobenius a)
      algebraicCentreFixedFintype = 1

/-- The numerical exclusion in Condition 6.1 is a kernel consequence of the
typed type-C applicability packet. -/
theorem FMZ62TypeCCondition61Applicability.condition61_not_dvd_two_q_centre
    {A Dual ι : Type}
    [Group Dual] [Fintype Dual]
    (r a ell : ℕ) (ha : 0 < a)
    [Fintype (FiniteSymplecticFixed r a)]
    [MulAction (MulAut (FiniteSymplecticFixed r a)) A]
    [Fintype ι]
    [MulAction (MulAut (FiniteSymplecticFixed r a))ᵐᵒᵖ ι]
    (D : Definitions ℂ (FiniteSymplecticFixed r a) A ι)
    (coherence : InnerCoherence D) (block : ι)
    (S35 : Inputs (A := A) (Block := ι) (Dual := Dual)
      r a ell ha D coherence block)
    (source : FMZ62TypeCCondition61Applicability
      r a ell ha D coherence block S35) :
    ¬ ell ∣ 2 * (2 ^ a) *
      (@Fintype.card
        (ModularRep.PaperProofs.EvenFieldCyclicFieldAction.FixedPoints
          source.nonArithmetic.algebraicCentreFixed.FMZCentreBaseFrobenius a)
        source.algebraicCentreFixedFintype) := by
  exact
    ModularRep.ManuscriptVerification.EvenCondition61.condition61_not_dvd_two_q_centre
      S35.e1e4.ellPrime source.typeCGoodPrime.ellOdd rfl
      source.algebraicCentreFixedCard_one

/-- The regular-embedding fixed group constructed from the E1/U source
presentation.  Identifying it with the cited `\widetilde G^F` remains U. -/
abbrev FMZ62RegularFixedGroup
    (r a : ℕ) (ha : 0 < a)
    (source : FMZ62TypeCCondition61NonArithmeticSource r a ha) :=
  ModularRep.PaperProofs.EvenFieldCyclicFieldAction.FixedPoints
    source.FMZRegularTargetBaseFrobenius a

/-- The type-C field group acts on the regular-embedding fixed group through
the target Frobenius stored in the same Condition 6.1 source. -/
noncomputable def FMZ62RegularFieldAction
    (r a : ℕ) (ha : 0 < a)
    (source : FMZ62TypeCCondition61NonArithmeticSource r a ha) :
    FieldGroup a →* MulAut (FMZ62RegularFixedGroup r a ha source) :=
  ModularRep.PaperProofs.EvenFieldCyclicFieldAction.fieldActionHom
    source.FMZRegularTargetBaseFrobenius a ha

/-- The field factor is the literal source automorphism subgroup required by
Theorem 6.2.  Faithfulness is an E1/U source fact for the exact K-defined
action, rather than a consequence of the abstract fixed-point construction. -/
theorem FMZ62RegularFieldAction_injective
    (r a : ℕ) (ha : 0 < a)
    (source : FMZ62TypeCCondition61NonArithmeticSource r a ha) :
    Function.Injective (FMZ62RegularFieldAction r a ha source) :=
  by
    simpa only [FMZ62RegularFieldAction] using
      source.regularTargetFieldAction_injective

/-- The K-constructed semidirect product presented to Theorem 6.2.  Its
identification with the cited `\widetilde G^F \rtimes \mathcal B` is U. -/
abbrev FMZ62TheoremGroup
    (r a : ℕ) (ha : 0 < a)
    (source : FMZ62TypeCCondition61NonArithmeticSource r a ha) :=
  FMZ62RegularFixedGroup r a ha source ⋊[
    FMZ62RegularFieldAction r a ha source] FieldGroup a

/-- The opposite of the presented semidirect product, used to express the
manuscript's right automorphism action as a Lean left action. -/
abbrev FMZ62TheoremActor
    (r a : ℕ) (ha : 0 < a)
    (source : FMZ62TypeCCondition61NonArithmeticSource r a ha) :=
  (FMZ62TheoremGroup r a ha source)ᵐᵒᵖ

/-- The canonical inclusion of the type-C field group into the theorem
actor.  No caller-supplied field stabiliser or abstract actor occurs here. -/
def FMZ62FieldIntoTheoremActor
    (r a : ℕ) (ha : 0 < a)
    (source : FMZ62TypeCCondition61NonArithmeticSource r a ha) :
    (FieldGroup a)ᵐᵒᵖ →* FMZ62TheoremActor r a ha source :=
  MonoidHom.op
    (SemidirectProduct.inr :
      FieldGroup a →* FMZ62TheoremGroup r a ha source)

/-- A typed presentation of the cited source block and its semidirect-product
action.  The block labels are identified with the literal set of blocks, and
the canonical field inclusion is required to agree with the concrete type-C
field action.  The U-level source instantiation identifies this presentation
with the published block `B`; Lean does not derive that identification. -/
structure FMZ62TheoremBlockPresentation
    {A Dual ι : Type}
    [Group Dual] [Fintype Dual]
    (r a ell : ℕ) (ha : 0 < a)
    [Fintype (FiniteSymplecticFixed r a)]
    [MulAction (MulAut (FiniteSymplecticFixed r a)) A]
    [Fintype ι]
    [MulAction (MulAut (FiniteSymplecticFixed r a))ᵐᵒᵖ ι]
    (D : Definitions ℂ (FiniteSymplecticFixed r a) A ι)
    (coherence : InnerCoherence D) (block : ι)
    (S35 : Inputs (A := A) (Block := ι) (Dual := Dual)
      r a ell ha D coherence block)
    (condition61 : FMZ62TypeCCondition61Applicability
      r a ell ha D coherence block S35) : Type 1 where
  SourceBlockLabel : Type
  sourceBlock : SourceBlockLabel
  blockActionE1U : MulAction
    (FMZ62TheoremActor r a ha condition61.nonArithmetic) SourceBlockLabel
  blockLabelEquiv : SourceBlockLabel ≃ ι
  blockLabel_target : blockLabelEquiv sourceBlock = block
  fieldAction_natural :
    ∀ (sigma : (FieldGroup a)ᵐᵒᵖ) (B : SourceBlockLabel),
      blockLabelEquiv
          (blockActionE1U.smul
            (FMZ62FieldIntoTheoremActor
              r a ha condition61.nonArithmetic sigma) B) =
        oppositeFieldAction r a ha sigma • blockLabelEquiv B

/-- The literal stabiliser of the presented source block inside the
K-constructed semidirect-product actor. -/
def FMZ62TheoremBlockStabilizer
    {A Dual ι : Type}
    [Group Dual] [Fintype Dual]
    (r a ell : ℕ) (ha : 0 < a)
    [Fintype (FiniteSymplecticFixed r a)]
    [MulAction (MulAut (FiniteSymplecticFixed r a)) A]
    [Fintype ι]
    [MulAction (MulAut (FiniteSymplecticFixed r a))ᵐᵒᵖ ι]
    (D : Definitions ℂ (FiniteSymplecticFixed r a) A ι)
    (coherence : InnerCoherence D) (block : ι)
    (S35 : Inputs (A := A) (Block := ι) (Dual := Dual)
      r a ell ha D coherence block)
    (condition61 : FMZ62TypeCCondition61Applicability
      r a ell ha D coherence block S35)
    (presentation : FMZ62TheoremBlockPresentation
      r a ell ha D coherence block S35 condition61) :
    Subgroup (FMZ62TheoremActor
      r a ha condition61.nonArithmetic) :=
  @MulAction.stabilizer
    (FMZ62TheoremActor r a ha condition61.nonArithmetic)
    presentation.SourceBlockLabel _ presentation.blockActionE1U
    presentation.sourceBlock

/-- Field stability of the literal block places the canonical field
inclusion in the literal theorem block stabiliser. -/
def FMZ62TheoremBlockPresentation.fieldIntoBlockStabilizer
    {A Dual ι : Type}
    [Group Dual] [Fintype Dual]
    (r a ell : ℕ) (ha : 0 < a)
    [Fintype (FiniteSymplecticFixed r a)]
    [MulAction (MulAut (FiniteSymplecticFixed r a)) A]
    [Fintype ι]
    [MulAction (MulAut (FiniteSymplecticFixed r a))ᵐᵒᵖ ι]
    (D : Definitions ℂ (FiniteSymplecticFixed r a) A ι)
    (coherence : InnerCoherence D) (block : ι)
    (S35 : Inputs (A := A) (Block := ι) (Dual := Dual)
      r a ell ha D coherence block)
    (condition61 : FMZ62TypeCCondition61Applicability
      r a ell ha D coherence block S35)
    (presentation : FMZ62TheoremBlockPresentation
      r a ell ha D coherence block S35 condition61)
    (hfixed : ∀ sigma : (FieldGroup a)ᵐᵒᵖ,
      oppositeFieldAction r a ha sigma • block = block) :
    (FieldGroup a)ᵐᵒᵖ →*
      FMZ62TheoremBlockStabilizer
        r a ell ha D coherence block S35 condition61 presentation where
  toFun sigma := ⟨FMZ62FieldIntoTheoremActor
      r a ha condition61.nonArithmetic sigma, by
    change presentation.blockActionE1U.smul
        (FMZ62FieldIntoTheoremActor
          r a ha condition61.nonArithmetic sigma)
        presentation.sourceBlock = presentation.sourceBlock
    apply presentation.blockLabelEquiv.injective
    calc
      presentation.blockLabelEquiv
          (presentation.blockActionE1U.smul
            (FMZ62FieldIntoTheoremActor
              r a ha condition61.nonArithmetic sigma)
            presentation.sourceBlock) =
          oppositeFieldAction r a ha sigma •
            presentation.blockLabelEquiv presentation.sourceBlock :=
        presentation.fieldAction_natural sigma presentation.sourceBlock
      _ = block := by rw [presentation.blockLabel_target, hfixed sigma]
      _ = presentation.blockLabelEquiv presentation.sourceBlock :=
        presentation.blockLabel_target.symm⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (FMZ62FieldIntoTheoremActor
      r a ha condition61.nonArithmetic)
  map_mul' sigma tau := by
    apply Subtype.ext
    exact map_mul (FMZ62FieldIntoTheoremActor
      r a ha condition61.nonArithmetic) sigma tau

/-- The source carrier and action match for the presented block in Theorem 6.2.
The generic and Alperin carriers are families indexed by the source block
labels, and only their fibres at `sourceBlock` enter the theorem endpoint.
The indices `pairs` and `alignment` tie this match to the exact e-JGC source
and ambient block catalogue consumed by Proposition 3.8. -/
structure FMZ62TypeCCarrierActionBlockSourceMatch
    {A Dual K k ι : Type}
    [Group Dual] [Fintype Dual]
    [Field K] [Field k] [CharZero K]
    (r a ell : ℕ) (ha : 0 < a)
    [CharP k ell] [IsAlgClosed k]
    [Fintype (FiniteSymplecticFixed r a)]
    [MulAction (MulAut (FiniteSymplecticFixed r a)) A]
    [Fintype ι]
    [MulAction (MulAut (FiniteSymplecticFixed r a))ᵐᵒᵖ ι]
    (D : Definitions ℂ (FiniteSymplecticFixed r a) A ι)
    (coherence : InnerCoherence D) (block : ι)
    (S35 : Inputs (A := A) (Block := ι) (Dual := Dual)
      r a ell ha D coherence block)
    (condition61 : FMZ62TypeCCondition61Applicability
      r a ell ha D coherence block S35)
    (pairs : PairClassSource ell k D)
    {blockIdempotent : ι → k[FiniteSymplecticFixed r a]}
    (blockSource : LocalBlockInductionSource
      (p := ell) (k := k) (K := K)
      (G := FiniteSymplecticFixed r a) (Block := ι))
    (alignment : AmbientBlockAlignment
      D pairs blockIdempotent blockSource)
    (hfixed : ∀ sigma : (FieldGroup a)ᵐᵒᵖ,
      oppositeFieldAction r a ha sigma • block = block)
    (presentation : FMZ62TheoremBlockPresentation
      r a ell ha D coherence block S35 condition61) : Type 1 where
  fmzGenericWeights : presentation.SourceBlockLabel → Type
  fmzAlperinWeights : presentation.SourceBlockLabel → Type
  fmzFullGenericAction : MulAction
    (FMZ62TheoremBlockStabilizer
      r a ell ha D coherence block S35 condition61 presentation)
    (fmzGenericWeights presentation.sourceBlock)
  fmzFullAlperinAction : MulAction
    (FMZ62TheoremBlockStabilizer
      r a ell ha D coherence block S35 condition61 presentation)
    (fmzAlperinWeights presentation.sourceBlock)
  genericWeightEquiv :
    fmzGenericWeights presentation.sourceBlock ≃ W D coherence block
  alperinWeightEquiv :
    fmzAlperinWeights presentation.sourceBlock ≃ blockSource.Fibre block
  generic_natural :
    let fixation :=
      ModularRep.PaperProofs.EvenFieldLemmas35_36Actual.lemma_3_5_actual
        r a ell ha D coherence block S35
    ∀ (sigma : (FieldGroup a)ᵐᵒᵖ)
        (w : fmzGenericWeights presentation.sourceBlock),
      genericWeightEquiv
          (fmzFullGenericAction.smul
            (presentation.fieldIntoBlockStabilizer
              r a ell ha D coherence block S35 condition61 hfixed sigma) w) =
        (genericWeightOppositeMulAction fixation).smul
          sigma (genericWeightEquiv w)
  alperin_natural :
    ∀ (sigma : (FieldGroup a)ᵐᵒᵖ)
        (w : fmzAlperinWeights presentation.sourceBlock),
      alperinWeightEquiv
          (fmzFullAlperinAction.smul
            (presentation.fieldIntoBlockStabilizer
              r a ell ha D coherence block S35 condition61 hfixed sigma) w) =
        (oppositeFieldWeightFibreMulAction
          (r := r) (a := a) ha blockSource block hfixed).smul
          sigma (alperinWeightEquiv w)

/-- The sole E2 endpoint used from Feng--Malle--Zhang, Theorem 6.2: an
existential equivariant bijection for the literal stabiliser in the presented
semidirect product.  Identifying this presentation with the published
`\widetilde G^F`, `\mathcal B`, and block `B` remains U.  Parts (a)--(b)
of the cited theorem are absent because this route does not consume them. -/
structure FMZ62FullBlockStabilizerEquivariantEndpoint
    {A Dual K k ι : Type}
    [Group Dual] [Fintype Dual]
    [Field K] [Field k] [CharZero K]
    (r a ell : ℕ) (ha : 0 < a)
    [CharP k ell] [IsAlgClosed k]
    [Fintype (FiniteSymplecticFixed r a)]
    [MulAction (MulAut (FiniteSymplecticFixed r a)) A]
    [Fintype ι]
    [MulAction (MulAut (FiniteSymplecticFixed r a))ᵐᵒᵖ ι]
    (D : Definitions ℂ (FiniteSymplecticFixed r a) A ι)
    (coherence : InnerCoherence D) (block : ι)
    (S35 : Inputs (A := A) (Block := ι) (Dual := Dual)
      r a ell ha D coherence block)
    (condition61 : FMZ62TypeCCondition61Applicability
      r a ell ha D coherence block S35)
    (pairs : PairClassSource ell k D)
    {blockIdempotent : ι → k[FiniteSymplecticFixed r a]}
    (blockSource : LocalBlockInductionSource
      (p := ell) (k := k) (K := K)
      (G := FiniteSymplecticFixed r a) (Block := ι))
    (alignment : AmbientBlockAlignment
      D pairs blockIdempotent blockSource)
    (hfixed : ∀ sigma : (FieldGroup a)ᵐᵒᵖ,
      oppositeFieldAction r a ha sigma • block = block)
    (presentation : FMZ62TheoremBlockPresentation
      r a ell ha D coherence block S35 condition61)
    (sourceMatch : FMZ62TypeCCarrierActionBlockSourceMatch
      r a ell ha D coherence block S35 condition61 pairs blockSource
      alignment hfixed presentation) : Prop where
  exists_full_block_stabilizer_equivariant_bijection :
    Nonempty (EquivariantEquiv
      (FMZ62TheoremBlockStabilizer
        r a ell ha D coherence block S35 condition61 presentation)
      (sourceMatch.fmzGenericWeights presentation.sourceBlock)
      (sourceMatch.fmzAlperinWeights presentation.sourceBlock)
      sourceMatch.fmzFullGenericAction.smul
      sourceMatch.fmzFullAlperinAction.smul)

/-- The source-carrier field endpoint obtained in K by restricting the sole
full-stabiliser E2 endpoint along the canonical field inclusion. -/
abbrev FMZ62RestrictedSourceFieldEquivariantEndpoint
    {A Dual K k ι : Type}
    [Group Dual] [Fintype Dual]
    [Field K] [Field k] [CharZero K]
    (r a ell : ℕ) (ha : 0 < a)
    [CharP k ell] [IsAlgClosed k]
    [Fintype (FiniteSymplecticFixed r a)]
    [MulAction (MulAut (FiniteSymplecticFixed r a)) A]
    [Fintype ι]
    [MulAction (MulAut (FiniteSymplecticFixed r a))ᵐᵒᵖ ι]
    (D : Definitions ℂ (FiniteSymplecticFixed r a) A ι)
    (coherence : InnerCoherence D) (block : ι)
    (S35 : Inputs (A := A) (Block := ι) (Dual := Dual)
      r a ell ha D coherence block)
    (condition61 : FMZ62TypeCCondition61Applicability
      r a ell ha D coherence block S35)
    (pairs : PairClassSource ell k D)
    {blockIdempotent : ι → k[FiniteSymplecticFixed r a]}
    (blockSource : LocalBlockInductionSource
      (p := ell) (k := k) (K := K)
      (G := FiniteSymplecticFixed r a) (Block := ι))
    (alignment : AmbientBlockAlignment
      D pairs blockIdempotent blockSource)
    (hfixed : ∀ sigma : (FieldGroup a)ᵐᵒᵖ,
      oppositeFieldAction r a ha sigma • block = block)
    (presentation : FMZ62TheoremBlockPresentation
      r a ell ha D coherence block S35 condition61)
    (sourceMatch : FMZ62TypeCCarrierActionBlockSourceMatch
      r a ell ha D coherence block S35 condition61 pairs blockSource
      alignment hfixed presentation) :=
  Nonempty (EquivariantEquiv (FieldGroup a)ᵐᵒᵖ
    (sourceMatch.fmzGenericWeights presentation.sourceBlock)
    (sourceMatch.fmzAlperinWeights presentation.sourceBlock)
    (fun sigma w ↦ sourceMatch.fmzFullGenericAction.smul
      (presentation.fieldIntoBlockStabilizer
        r a ell ha D coherence block S35 condition61 hfixed sigma) w)
    (fun sigma w ↦ sourceMatch.fmzFullAlperinAction.smul
      (presentation.fieldIntoBlockStabilizer
        r a ell ha D coherence block S35 condition61 hfixed sigma) w))

/-- Restrict the sole full source endpoint along the canonical homomorphism
from the type-C field group to the literal theorem block stabiliser. -/
def FMZ62FullBlockStabilizerEquivariantEndpoint.toRestrictedSourceEndpoint
    {A Dual K k ι : Type}
    [Group Dual] [Fintype Dual]
    [Field K] [Field k] [CharZero K]
    (r a ell : ℕ) (ha : 0 < a)
    [CharP k ell] [IsAlgClosed k]
    [Fintype (FiniteSymplecticFixed r a)]
    [MulAction (MulAut (FiniteSymplecticFixed r a)) A]
    [Fintype ι]
    [MulAction (MulAut (FiniteSymplecticFixed r a))ᵐᵒᵖ ι]
    (D : Definitions ℂ (FiniteSymplecticFixed r a) A ι)
    (coherence : InnerCoherence D) (block : ι)
    (S35 : Inputs (A := A) (Block := ι) (Dual := Dual)
      r a ell ha D coherence block)
    (condition61 : FMZ62TypeCCondition61Applicability
      r a ell ha D coherence block S35)
    (pairs : PairClassSource ell k D)
    {blockIdempotent : ι → k[FiniteSymplecticFixed r a]}
    (blockSource : LocalBlockInductionSource
      (p := ell) (k := k) (K := K)
      (G := FiniteSymplecticFixed r a) (Block := ι))
    (alignment : AmbientBlockAlignment
      D pairs blockIdempotent blockSource)
    (hfixed : ∀ sigma : (FieldGroup a)ᵐᵒᵖ,
      oppositeFieldAction r a ha sigma • block = block)
    (presentation : FMZ62TheoremBlockPresentation
      r a ell ha D coherence block S35 condition61)
    (sourceMatch : FMZ62TypeCCarrierActionBlockSourceMatch
      r a ell ha D coherence block S35 condition61 pairs blockSource
      alignment hfixed presentation)
    (endpoint : FMZ62FullBlockStabilizerEquivariantEndpoint
      r a ell ha D coherence block S35 condition61 pairs blockSource
      alignment hfixed presentation sourceMatch) :
    FMZ62RestrictedSourceFieldEquivariantEndpoint
      r a ell ha D coherence block S35 condition61 pairs blockSource
      alignment hfixed presentation sourceMatch := by
  obtain ⟨omega⟩ :=
    endpoint.exists_full_block_stabilizer_equivariant_bijection
  exact ⟨restrictEquivariantEquiv
    (presentation.fieldIntoBlockStabilizer
      r a ell ha D coherence block S35 condition61 hfixed) omega⟩

/-- The literal Lean-carrier endpoint obtained in K by source restriction
and reindexing.  It is an abbreviation for an existential equivalence, not a
second externally constructible source record. -/
abbrev FMZ62RestrictedFieldEquivariantEndpoint
    {A Dual K k ι : Type}
    [Group Dual] [Fintype Dual]
    [Field K] [Field k] [CharZero K]
    (r a ell : ℕ) (ha : 0 < a)
    [CharP k ell] [IsAlgClosed k]
    [Fintype (FiniteSymplecticFixed r a)]
    [MulAction (MulAut (FiniteSymplecticFixed r a)) A]
    [Fintype ι]
    [MulAction (MulAut (FiniteSymplecticFixed r a))ᵐᵒᵖ ι]
    (D : Definitions ℂ (FiniteSymplecticFixed r a) A ι)
    (coherence : InnerCoherence D) (block : ι)
    (S35 : Inputs (A := A) (Block := ι) (Dual := Dual)
      r a ell ha D coherence block)
    (condition61 : FMZ62TypeCCondition61Applicability
      r a ell ha D coherence block S35)
    (pairs : PairClassSource ell k D)
    {blockIdempotent : ι → k[FiniteSymplecticFixed r a]}
    (blockSource : LocalBlockInductionSource
      (p := ell) (k := k) (K := K)
      (G := FiniteSymplecticFixed r a) (Block := ι))
    (alignment : AmbientBlockAlignment
      D pairs blockIdempotent blockSource)
    (hfixed : ∀ sigma : (FieldGroup a)ᵐᵒᵖ,
      oppositeFieldAction r a ha sigma • block = block)
    (presentation : FMZ62TheoremBlockPresentation
      r a ell ha D coherence block S35 condition61)
    (sourceMatch : FMZ62TypeCCarrierActionBlockSourceMatch
      r a ell ha D coherence block S35 condition61 pairs blockSource
      alignment hfixed presentation) :=
  let fixation :=
    ModularRep.PaperProofs.EvenFieldLemmas35_36Actual.lemma_3_5_actual
      r a ell ha D coherence block S35
  Nonempty (EquivariantEquiv (FieldGroup a)ᵐᵒᵖ (W D coherence block)
    (blockSource.Fibre block)
    (genericWeightOppositeMulAction fixation).smul
    (oppositeFieldWeightFibreMulAction
      (r := r) (a := a) ha blockSource block hfixed).smul)

/-- Reindex an equivariant equivalence along explicit equivalences of the
acting group and both carriers.  This is the K transport used below; it does
not choose the existential source bijection. -/
def reindexEquivariantEquiv
    {E₀ X₀ Y₀ E X Y : Type*}
    {alpha₀ : E₀ → X₀ → X₀} {beta₀ : E₀ → Y₀ → Y₀}
    {alpha : E → X → X} {beta : E → Y → Y}
    (eE : E₀ ≃ E) (eX : X₀ ≃ X) (eY : Y₀ ≃ Y)
    (hX : ∀ s x, eX (alpha₀ s x) = alpha (eE s) (eX x))
    (hY : ∀ s y, eY (beta₀ s y) = beta (eE s) (eY y))
    (omega : EquivariantEquiv E₀ X₀ Y₀ alpha₀ beta₀) :
    EquivariantEquiv E X Y alpha beta where
  toEquiv := eX.symm.trans (omega.toEquiv.trans eY)
  equivariant := by
    intro t x
    have hx :
        eX.symm (alpha t x) = alpha₀ (eE.symm t) (eX.symm x) := by
      apply eX.injective
      simpa using (hX (eE.symm t) (eX.symm x)).symm
    change eY (omega.toEquiv (eX.symm (alpha t x))) =
      beta t (eY (omega.toEquiv (eX.symm x)))
    rw [hx, omega.equivariant]
    simpa using hY (eE.symm t) (omega.toEquiv (eX.symm x))

/-- A source application of the restricted endpoint after its Condition 6.1
and carrier/action/block matches have been fixed.  This is not a rendering of
all of Feng--Malle--Zhang, Theorem 6.2: parts (a)--(b) are intentionally absent
because no downstream declaration consumes them. -/
structure FMZ62TypeCRestrictedApplication
    {A Dual K k ι : Type}
    [Group Dual] [Fintype Dual]
    [Field K] [Field k] [CharZero K]
    (r a ell : ℕ) (ha : 0 < a)
    [CharP k ell] [IsAlgClosed k]
    [Fintype (FiniteSymplecticFixed r a)]
    [MulAction (MulAut (FiniteSymplecticFixed r a)) A]
    [Fintype ι]
    [MulAction (MulAut (FiniteSymplecticFixed r a))ᵐᵒᵖ ι]
    (D : Definitions ℂ (FiniteSymplecticFixed r a) A ι)
    (coherence : InnerCoherence D) (block : ι)
    (S35 : Inputs (A := A) (Block := ι) (Dual := Dual)
      r a ell ha D coherence block)
    (pairs : PairClassSource ell k D)
    {blockIdempotent : ι → k[FiniteSymplecticFixed r a]}
    (blockSource : LocalBlockInductionSource
      (p := ell) (k := k) (K := K)
      (G := FiniteSymplecticFixed r a) (Block := ι))
    (alignment : AmbientBlockAlignment
      D pairs blockIdempotent blockSource)
    (hfixed : ∀ sigma : (FieldGroup a)ᵐᵒᵖ,
      oppositeFieldAction r a ha sigma • block = block) : Type 1 where
  condition61 : FMZ62TypeCCondition61Applicability
    r a ell ha D coherence block S35
  blockPresentation : FMZ62TheoremBlockPresentation
    r a ell ha D coherence block S35 condition61
  sourceMatch : FMZ62TypeCCarrierActionBlockSourceMatch
    r a ell ha D coherence block S35 condition61 pairs blockSource
    alignment hfixed blockPresentation
  fullBlockStabilizerEndpoint : FMZ62FullBlockStabilizerEquivariantEndpoint
    r a ell ha D coherence block S35 condition61 pairs blockSource
    alignment hfixed blockPresentation sourceMatch

/-- Extract the restricted source endpoint from the one full-stabilizer source
endpoint stored in the application packet. -/
def FMZ62TypeCRestrictedApplication.toRestrictedSourceEndpoint
    {A Dual K k ι : Type}
    [Group Dual] [Fintype Dual]
    [Field K] [Field k] [CharZero K]
    (r a ell : ℕ) (ha : 0 < a)
    [CharP k ell] [IsAlgClosed k]
    [Fintype (FiniteSymplecticFixed r a)]
    [MulAction (MulAut (FiniteSymplecticFixed r a)) A]
    [Fintype ι]
    [MulAction (MulAut (FiniteSymplecticFixed r a))ᵐᵒᵖ ι]
    (D : Definitions ℂ (FiniteSymplecticFixed r a) A ι)
    (coherence : InnerCoherence D) (block : ι)
    (S35 : Inputs (A := A) (Block := ι) (Dual := Dual)
      r a ell ha D coherence block)
    (pairs : PairClassSource ell k D)
    {blockIdempotent : ι → k[FiniteSymplecticFixed r a]}
    (blockSource : LocalBlockInductionSource
      (p := ell) (k := k) (K := K)
      (G := FiniteSymplecticFixed r a) (Block := ι))
    (alignment : AmbientBlockAlignment
      D pairs blockIdempotent blockSource)
    (hfixed : ∀ sigma : (FieldGroup a)ᵐᵒᵖ,
      oppositeFieldAction r a ha sigma • block = block)
    (application : FMZ62TypeCRestrictedApplication
      r a ell ha D coherence block S35 pairs blockSource alignment hfixed) :
    FMZ62RestrictedSourceFieldEquivariantEndpoint
      r a ell ha D coherence block S35 application.condition61 pairs
      blockSource alignment hfixed application.blockPresentation
      application.sourceMatch :=
  FMZ62FullBlockStabilizerEquivariantEndpoint.toRestrictedSourceEndpoint
    r a ell ha D coherence block S35 application.condition61 pairs
    blockSource alignment hfixed application.blockPresentation
    application.sourceMatch application.fullBlockStabilizerEndpoint

/-- Project the source-carrier endpoint to the literal Lean carriers by the
explicit equivalences and action naturality in `sourceMatch`. -/
def FMZ62TypeCRestrictedApplication.toRestrictedFieldEndpoint
    {A Dual K k ι : Type}
    [Group Dual] [Fintype Dual]
    [Field K] [Field k] [CharZero K]
    (r a ell : ℕ) (ha : 0 < a)
    [CharP k ell] [IsAlgClosed k]
    [Fintype (FiniteSymplecticFixed r a)]
    [MulAction (MulAut (FiniteSymplecticFixed r a)) A]
    [Fintype ι]
    [MulAction (MulAut (FiniteSymplecticFixed r a))ᵐᵒᵖ ι]
    (D : Definitions ℂ (FiniteSymplecticFixed r a) A ι)
    (coherence : InnerCoherence D) (block : ι)
    (S35 : Inputs (A := A) (Block := ι) (Dual := Dual)
      r a ell ha D coherence block)
    (pairs : PairClassSource ell k D)
    {blockIdempotent : ι → k[FiniteSymplecticFixed r a]}
    (blockSource : LocalBlockInductionSource
      (p := ell) (k := k) (K := K)
      (G := FiniteSymplecticFixed r a) (Block := ι))
    (alignment : AmbientBlockAlignment
      D pairs blockIdempotent blockSource)
    (hfixed : ∀ sigma : (FieldGroup a)ᵐᵒᵖ,
      oppositeFieldAction r a ha sigma • block = block)
    (application : FMZ62TypeCRestrictedApplication
      r a ell ha D coherence block S35 pairs blockSource alignment hfixed) :
    FMZ62RestrictedFieldEquivariantEndpoint
      r a ell ha D coherence block S35 application.condition61 pairs
      blockSource alignment hfixed application.blockPresentation
      application.sourceMatch := by
  obtain ⟨omega⟩ :=
    FMZ62TypeCRestrictedApplication.toRestrictedSourceEndpoint
      r a ell ha D coherence block S35 pairs blockSource alignment hfixed
      application
  exact ⟨reindexEquivariantEquiv
    (Equiv.refl (FieldGroup a)ᵐᵒᵖ)
    application.sourceMatch.genericWeightEquiv
    application.sourceMatch.alperinWeightEquiv
    application.sourceMatch.generic_natural
    application.sourceMatch.alperin_natural omega⟩

/-- The exact E1 transport datum used by the K-level block-fibre
correspondence.  This source deliberately contains no sector, radical,
defect-zero, normalisation, extension, or character-triple fields. -/
structure ActualBijectionSource
    {K k ι : Type}
    [Field K] [Field k] [CharZero K]
    (r a ell : ℕ) (ha : 0 < a)
    [CharP k ell] [IsAlgClosed k]
    [Fintype (FiniteSymplecticFixed r a)]
    (iota : PrimeRegularRootEmbedding ell k K
      (FiniteSymplecticFixed r a))
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    [Fintype ι]
    {blockIdempotent : ι → k[FiniteSymplecticFixed r a]}
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    [MulAction (MulAut (FiniteSymplecticFixed r a))ᵐᵒᵖ ι] where
  brauerBlock_transport : ∀ (sigma : (FieldGroup a)ᵐᵒᵖ)
      (phi : IBr iota),
    irreducibleBrauerCharacterBlock iota
        hinj blocks
        (oppositeFieldAction r a ha sigma • phi) =
      oppositeFieldAction r a ha sigma •
        irreducibleBrauerCharacterBlock iota hinj blocks phi

/-- Field stability of a selected block converts the narrow transport datum
into the stability hypothesis used by the stable-reduction bridge. -/
theorem ActualBijectionSource.isAutomorphismStableIBrBlock
    {K k ι : Type}
    [Field K] [Field k] [CharZero K]
    {r a ell : ℕ} (ha : 0 < a)
    [CharP k ell] [IsAlgClosed k]
    [Fintype (FiniteSymplecticFixed r a)]
    (iota : PrimeRegularRootEmbedding ell k K
      (FiniteSymplecticFixed r a))
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    [Fintype ι]
    {blockIdempotent : ι → k[FiniteSymplecticFixed r a]}
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    [MulAction (MulAut (FiniteSymplecticFixed r a))ᵐᵒᵖ ι]
    (S : ActualBijectionSource r a ell ha iota hinj blocks)
    (block : ι)
    (hfixed : ∀ sigma : (FieldGroup a)ᵐᵒᵖ,
      oppositeFieldAction r a ha sigma • block = block) :
    IsAutomorphismStableIBrBlock
      (oppositeFieldAction r a ha) iota hinj blocks block := by
  intro sigma phi hphi
  rw [S.brauerBlock_transport, hphi, hfixed sigma]

/-- A fixed choice of the actual-carrier correspondence proved by Lemma 3.7.
The intermediate disjoint union is indexed by the orbit quotient of the
literal `D.inL` pairs and uses their genuine inertia quotients. -/
noncomputable def selectedLemma36CorrespondenceActual
    {A Dual CitedRelativeWeylGroup ι k : Type}
    [Group Dual] [Fintype Dual]
    [Group CitedRelativeWeylGroup]
    (r a ell : ℕ) (ha : 0 < a)
    [Field k] [CharP k ell] [IsAlgClosed k]
    [Fintype (FiniteSymplecticFixed r a)]
    [MulAction (MulAut (FiniteSymplecticFixed r a)) A]
    (D : Definitions ℂ (FiniteSymplecticFixed r a) A ι)
    (coherence : InnerCoherence D) (block : ι)
    (S35 : Inputs (A := A) (Block := ι) (Dual := Dual)
      r a ell ha D coherence block)
    (pairs : PairClassSource ell k D)
    (initial : pairs.RestrictedPair block)
    (GeneralisedSeries : Set (Irr ℂ (FiniteSymplecticFixed r a)))
    [Fintype (W D coherence block)]
    [Fintype (pairs.DefectZeroUnion block)]
    (cited :
      ModularRep.PaperProofs.EvenFieldLemmas35_36Actual.CitedData
        (CitedRelativeWeylGroup := CitedRelativeWeylGroup) ell
        (S35.e1e4.toExactProvider r a ell ha).inBlock
        (S35.e1e4.toExactProvider r a ell ha).globalSeries.series
        D coherence block pairs initial GeneralisedSeries) :
    let fixation :=
      ModularRep.PaperProofs.EvenFieldLemmas35_36Actual.lemma_3_5_actual
        r a ell ha D coherence block S35
    EquivariantEquiv (FieldGroup a)ᵐᵒᵖ
      (↑(XC ell
        (S35.e1e4.toExactProvider r a ell ha).inBlock
        (S35.e1e4.toExactProvider r a ell ha).globalSeries.series))
      (W D coherence block)
      (characterOppositeMulAction fixation).smul
      (genericWeightOppositeMulAction fixation).smul :=
  Classical.choice
    (ModularRep.PaperProofs.EvenFieldLemmas35_36Actual.lemma_3_6_actual
      r a ell ha D coherence block S35 pairs initial GeneralisedSeries cited)

/-- The substantive Proposition 3.8 bijection on literal carriers.

The target is definitionally the fibre of the block map constructed by
`LocalBlockInductionSource`.  Its field action is also constructed here from
`oppositeFieldAction`; there is no weight action or weight-block map among the
arguments.  The only final correspondence supplied is the cited E2 map from
generic weights to this literal fibre. -/
theorem proposition_3_8_equivariant_bijection_actual
    {A Dual CitedRelativeWeylGroup K O k ι : Type}
    [Group Dual] [Fintype Dual]
    [Group CitedRelativeWeylGroup]
    [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
    [CharZero K]
    (r a ell : ℕ) (ha : 0 < a) [CharP k ell] [IsAlgClosed k]
    [Fintype (FiniteSymplecticFixed r a)]
    [Finite (FieldGroup a)ᵐᵒᵖ] [IsCyclic (FieldGroup a)ᵐᵒᵖ]
    [MulAction (MulAut (FiniteSymplecticFixed r a)) A]
    [Fintype ι]
    [MulAction (MulAut (FiniteSymplecticFixed r a))ᵐᵒᵖ ι]
    (block : ι)
    (D : Definitions ℂ (FiniteSymplecticFixed r a) A ι)
    (coherence : InnerCoherence D)
    (S35 : Inputs (A := A) (Block := ι) (Dual := Dual)
      r a ell ha D coherence block)
    (pairs : PairClassSource ell k D)
    (initial : pairs.RestrictedPair block)
    (GeneralisedSeries : Set (Irr ℂ (FiniteSymplecticFixed r a)))
    [Fintype (W D coherence block)]
    [Fintype (pairs.DefectZeroUnion block)]
    (cited :
      ModularRep.PaperProofs.EvenFieldLemmas35_36Actual.CitedData
        (CitedRelativeWeylGroup := CitedRelativeWeylGroup) ell
        (S35.e1e4.toExactProvider r a ell ha).inBlock
        (S35.e1e4.toExactProvider r a ell ha).globalSeries.series
        D coherence block pairs initial GeneralisedSeries)
    (iota : PrimeRegularRootEmbedding ell k K
      (FiniteSymplecticFixed r a))
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    {blockIdempotent : ι → k[FiniteSymplecticFixed r a]}
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (blockSource : LocalBlockInductionSource
      (p := ell) (k := k) (K := K)
      (G := FiniteSymplecticFixed r a) (Block := ι))
    (alignment : AmbientBlockAlignment D pairs blockIdempotent blockSource)
    (source : ActualBijectionSource
      r a ell ha iota hinj blocks)
    (hfixed : ∀ sigma : (FieldGroup a)ᵐᵒᵖ,
      oppositeFieldAction r a ha sigma • block = block)
    (Msys : ModularSystem ell K O k)
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (basicSet : RestrictedIntegralBasicSetOnIBrBlock
      iota hinj blocks block
        (↑(XC ell
          (S35.e1e4.toExactProvider r a ell ha).inBlock
          (S35.e1e4.toExactProvider r a ell ha).globalSeries.series))
        (decompositionMapOfStableReduction Msys iota hcompat))
    [Finite (↑(XC ell
      (S35.e1e4.toExactProvider r a ell ha).inBlock
      (S35.e1e4.toExactProvider r a ell ha).globalSeries.series))]
    (fmz62 : FMZ62TypeCRestrictedApplication
      r a ell ha D coherence block S35 pairs blockSource alignment hfixed)
    (conlon : PaperProofs.ConlonBasicSet.PadicConlonMarkDetection.{0, 0}
      (p := 2) (A := (FieldGroup a)ᵐᵒᵖ))
    (burnside : PaperProofs.ConlonBasicSet.PublishedBurnsideMarkInjectivity.{0, 0}
      (A := (FieldGroup a)ᵐᵒᵖ)) :
    let fixation :=
      ModularRep.PaperProofs.EvenFieldLemmas35_36Actual.lemma_3_5_actual
        r a ell ha D coherence block S35
    let _ : MulAction (FieldGroup a)ᵐᵒᵖ
        (↑(XC ell
          (S35.e1e4.toExactProvider r a ell ha).inBlock
          (S35.e1e4.toExactProvider r a ell ha).globalSeries.series)) :=
      characterOppositeMulAction fixation
    let _ : MulAction (FieldGroup a)ᵐᵒᵖ (W D coherence block) :=
      genericWeightOppositeMulAction fixation
    ∀ hordinary : OrdinaryTwistCompatibleLabels basicSet
        (oppositeFieldAction r a ha),
      let hstable := source.isAutomorphismStableIBrBlock
        ha iota hinj blocks block hfixed
      Nonempty (EquivariantEquiv (FieldGroup a)ᵐᵒᵖ
        (IBrBlock iota hinj blocks block) (blockSource.Fibre block)
        (automorphismIBrBlockMulAction
          (oppositeFieldAction r a ha) hstable).smul
        (oppositeFieldWeightFibreMulAction
          (r := r) (a := a) ha blockSource block hfixed).smul) := by
  dsimp only
  intro hordinary
  let fixation :=
    ModularRep.PaperProofs.EvenFieldLemmas35_36Actual.lemma_3_5_actual
      r a ell ha D coherence block S35
  letI : MulAction (FieldGroup a)ᵐᵒᵖ
      (↑(XC ell
        (S35.e1e4.toExactProvider r a ell ha).inBlock
        (S35.e1e4.toExactProvider r a ell ha).globalSeries.series)) :=
    characterOppositeMulAction fixation
  letI : MulAction (FieldGroup a)ᵐᵒᵖ (W D coherence block) :=
    genericWeightOppositeMulAction fixation
  letI : MulAction (FieldGroup a)ᵐᵒᵖ ι :=
    oppositeFieldBlockMulAction r a ha
  letI : MulAction (FieldGroup a)ᵐᵒᵖ (IBr iota) :=
    oppositeFieldIBrMulAction ha iota
  letI : MulAction (FieldGroup a)ᵐᵒᵖ (ActualWeight ell K r a) :=
    oppositeFieldWeightMulAction r a ell ha K
  have hstable : IsAutomorphismStableIBrBlock
      (oppositeFieldAction r a ha) iota hinj blocks block :=
    source.isAutomorphismStableIBrBlock
      ha iota hinj blocks block hfixed
  letI : MulAction (FieldGroup a)ᵐᵒᵖ
      (IBrBlock iota hinj blocks block) :=
    automorphismIBrBlockMulAction (oppositeFieldAction r a ha) hstable
  letI : MulAction (FieldGroup a)ᵐᵒᵖ
      (blockSource.Fibre block) :=
    oppositeFieldWeightFibreMulAction
      (r := r) (a := a) ha blockSource block hfixed
  let e :
      (↑(XC ell
        (S35.e1e4.toExactProvider r a ell ha).inBlock
        (S35.e1e4.toExactProvider r a ell ha).globalSeries.series)) ≃
        IBrBlock iota hinj blocks block :=
    basicToIBrBlockOfStableReduction iota hinj blocks block Msys hcompat
      basicSet (oppositeFieldAction r a ha) hstable hordinary
      (ModularRep.isCyclic_quotient_pCore 2 ((FieldGroup a)ᵐᵒᵖ))
      conlon burnside
  have he : ∀ (sigma : (FieldGroup a)ᵐᵒᵖ)
      (x : ↑(XC ell
        (S35.e1e4.toExactProvider r a ell ha).inBlock
        (S35.e1e4.toExactProvider r a ell ha).globalSeries.series)),
      e (sigma • x) = sigma • e x :=
    basicToIBrBlockOfStableReduction_equivariant iota hinj blocks block Msys
      hcompat basicSet (oppositeFieldAction r a ha) hstable hordinary
      (ModularRep.isCyclic_quotient_pCore 2 ((FieldGroup a)ᵐᵒᵖ))
      conlon burnside
  let first : EquivariantEquiv (FieldGroup a)ᵐᵒᵖ
      (IBrBlock iota hinj blocks block)
      (↑(XC ell
        (S35.e1e4.toExactProvider r a ell ha).inBlock
        (S35.e1e4.toExactProvider r a ell ha).globalSeries.series))
      (· • ·) (· • ·) :=
    equivariantEquivSymm
      (show EquivariantEquiv (FieldGroup a)ᵐᵒᵖ
          (↑(XC ell
            (S35.e1e4.toExactProvider r a ell ha).inBlock
            (S35.e1e4.toExactProvider r a ell ha).globalSeries.series))
          (IBrBlock iota hinj blocks block) (· • ·) (· • ·) from
        ⟨e, he⟩)
  let middle := selectedLemma36CorrespondenceActual
    r a ell ha D coherence block S35 pairs initial GeneralisedSeries cited
  obtain ⟨genericToAlperin⟩ :=
    FMZ62TypeCRestrictedApplication.toRestrictedFieldEndpoint
      r a ell ha D coherence block S35 pairs blockSource alignment hfixed
      fmz62
  exact ⟨equivariantEquivTrans
    (equivariantEquivTrans first middle) genericToAlperin⟩

end

end ModularRep.PaperProofs.EvenFieldConcreteProposition38Actual


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
