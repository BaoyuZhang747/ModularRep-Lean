import ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
import ModularRep.PaperProofs.EvenFieldFLZDefinition35Transport
import ModularRep.PaperProofs.EvenFieldLemmas35_36Actual
import ModularRep.PaperProofs.EvenFieldProposition38Lemma37Bridge
import ModularRep.PaperProofs.EvenFieldProposition39FullHGStrictBlockCore
import ModularRep.PaperProofs.EvenFieldProposition39OutsideOrder
import ModularRep.PaperProofs.EvenFieldProposition39StructuralCases
import ModularRep.PaperProofs.EvenFieldProposition39SplitLowRank
import ModularRep.PaperProofs.EvenFieldProposition39Sp6CyclicFiveSeven
import ModularRep.PaperProofs.EvenFieldProposition39Sp6Three
import ModularRep.PaperProofs.EvenFieldProposition39Suzuki
import ModularRep.PaperProofs.EvenFieldProposition39TypeA
import ModularRep.IBrBlockBasicSetBridge

/-!
# Conditional universe-zero high-rank route for even-field Proposition 3.9

This module is deliberately additive.  It provides the source-facing
universe-zero route for the rank at least four branch without passing through
the legacy generic relative router.  The conclusion-producing external input
in this route is instead the fixed `FLZ318Source.applyTheorem318` gate for the
cited Theorem 3.18.

The protected Proposition 3.8 endpoint needed here is the rewritten
literal-pair bridge
`EvenFieldProposition38Lemma37Bridge.proposition_3_8_to_lemma_3_7_actual`.
It is intentionally not replaced by a local axiom, a legacy pair-class
conversion, or a caller-supplied `CyclicEndgameData`.

The cover belongs exclusively to `SelfCoverSourceIdentification` on the
concrete self-cover side.  The target Definition 3.5 endpoint is cover-free.

The dispatcher derives the outside-order case from divisibility of the
literal presented group order.  The external classifier is used only when
that prime divides the order and can return only a noncoprime type `A` or type
`C` case.  In the high rank branch the classifier equality carries the rank
and positive field exponent through every later source.  In its Suzuki branch
the classifier equality carries the positive
twist parameter.  The branch source fixes the cover model and separates the
Corollary 6.3 packet, the indexed Spath passage, and the Definition 3.5
relation implication.  Lean passes the odd-prime proof explicitly.
-/

noncomputable section

namespace ModularRep.PaperProofs.EvenFieldProposition39HighRankU0

open scoped MonoidAlgebra Pointwise

open Formalisation
open ModularRep
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.IBrBlockBasicSetBridge
open ModularRep.IBrBlockBasicSetBridge.RestrictedIntegralBasicSetOnIBrBlock
open ModularRep.IntegralBasicSetBridge
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.ManuscriptVerification.EvenUnipotentCorrespondence
open ModularRep.ManuscriptVerification.StrictQuasiIsolation
open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs.CyclicOuterLemma37ActualBlockFibres
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPair
open ModularRep.PaperProofs.EvenFieldConcreteLemma35
open ModularRep.PaperProofs.EvenFieldConcreteProposition38Actual
open ModularRep.PaperProofs.EvenFieldConcreteTypeC
open ModularRep.PaperProofs.EvenFieldEJGCPairActual
open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.EvenFieldFLZ318SelfCover
open ModularRep.PaperProofs.EvenFieldFLZ318SelfCoverExplicitHypotheses
open ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
open ModularRep.PaperProofs.EvenFieldFLZDefinition35Transport
open ModularRep.PaperProofs.EvenFieldFLZFullHG
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFMZGenericPair
open ModularRep.PaperProofs.EvenFieldLemma35E1E4Providers
open ModularRep.PaperProofs.EvenFieldLemmas35_36Actual
open ModularRep.PaperProofs.EvenFieldOrdinaryCharacters
open ModularRep.PaperProofs.EvenFieldProposition38Lemma37Bridge
open ModularRep.PaperProofs.EvenFieldProposition39FullHGStrictBlocks
open ModularRep.PaperProofs.EvenFieldProposition39OutsideOrder
open ModularRep.PaperProofs.EvenFieldProposition39Relative
open ModularRep.PaperProofs.EvenFieldProposition39SplitLowRank
open ModularRep.PaperProofs.EvenFieldProposition39Sp6CyclicFiveSeven
open ModularRep.PaperProofs.EvenFieldProposition39Sp6Three
open ModularRep.PaperProofs.EvenFieldProposition39Suzuki
open ModularRep.PaperProofs.EvenFieldProposition39TypeA

/-! ## Concrete model of a classified high-rank pair -/

/-- Source identification of one classified high rank `FullHG` pair with the
literal even-field symplectic fixed-point model used by Proposition 3.8.
The exact classifier equality fixes the rank and field exponent before any
block or theorem source is selected. -/
structure HighRankPairConcreteModelU0 {ell : ℕ}
    {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    (classification : FullHGTypeCClassificationSource scope)
    (pair : FullHG scope)
    (parameter : HighRankParameter)
    (hcase : classification.structuralCase coverage pair =
      .typeC (.rankAtLeastFour parameter)) where
  fixedPointModel :
    pair.1.algebraicPair.FixedPointGroup ≃*
      FiniteSymplecticFixed parameter.rank parameter.fieldExponent

/-- Compose the presentation's existing fixed-point equivalence with the
chosen concrete symplectic model.  Compatibility with the block, character,
weight, and action carriers remains E1/U and is supplied by
`HighRankConcreteEndpointCarrierMatchU0`.  Preservation of the Definition 3.5
relation is kept separately in the E2/U certificate
`HighRankConcreteEndpointRelationForwardU0`. -/
def HighRankPairConcreteModelU0.familyToConcrete {ell : ℕ}
    {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    {classification : FullHGTypeCClassificationSource scope}
    {pair : FullHG scope}
    {parameter : HighRankParameter}
    {hcase : classification.structuralCase coverage pair =
      .typeC (.rankAtLeastFour parameter)}
    (model : HighRankPairConcreteModelU0 classification pair parameter hcase)
    (presentation : FLZHGDefinition35Presentation ell pair.1) :
    presentation.family.H ≃*
      FiniteSymplecticFixed parameter.rank parameter.fieldExponent :=
  presentation.fixedPointEquiv.trans model.fixedPointModel

/-! ## Literal Proposition 3.8 input packet -/

/-- The exact non-legacy input package for the literal Phase C--D
Proposition 3.8--Lemma 2.10 bridge.  In particular, the FMZ carrier is fixed
by `PairClassSource`.  There is no free pair class, predicate, relative Weyl
family, defect zero predicate, or legacy conversion in this structure.  The
map from generic weights to Alperin weights is present only through the named
E2/U existence source for Feng--Malle--Zhang, Theorem 6.2. -/
structure P38LiteralBridgeInputs (r a ell : ℕ) (ha : 0 < a) where
  A : Type
  Dual : Type
  CitedRelativeWeylGroup : Type
  K : Type
  O : Type
  k : Type
  ι : Type
  [groupDual : Group Dual]
  [fintypeDual : Fintype Dual]
  [groupCitedRelativeWeylGroup : Group CitedRelativeWeylGroup]
  [fieldK : Field K]
  [commRingO : CommRing O]
  [isDomainO : IsDomain O]
  [fieldk : Field k]
  [algebraOK : Algebra O K]
  [charZeroK : CharZero K]
  [charPk : CharP k ell]
  [algClosedk : IsAlgClosed k]
  [fintypeFixed : Fintype (FiniteSymplecticFixed r a)]
  [finiteFieldOpp : Finite (FieldGroup a)ᵐᵒᵖ]
  [cyclicFieldOpp : IsCyclic (FieldGroup a)ᵐᵒᵖ]
  [finiteField : Finite (FieldGroup a)]
  [cyclicField : IsCyclic (FieldGroup a)]
  [mulActionA : MulAction (MulAut (FiniteSymplecticFixed r a)) A]
  [fintypeBlock : Fintype ι]
  [mulActionBlock : MulAction (MulAut (FiniteSymplecticFixed r a))ᵐᵒᵖ ι]
  D : Definitions ℂ (FiniteSymplecticFixed r a) A ι
  coherence : InnerCoherence D
  block : ι
  S35 : Inputs (A := A) (Block := ι) (Dual := Dual)
    r a ell ha D coherence block
  pairs : PairClassSource ell k D
  initial : pairs.RestrictedPair block
  GeneralisedSeries : Set (Irr ℂ (FiniteSymplecticFixed r a))
  [fintypeW : Fintype (W D coherence block)]
  [fintypeDefectZeroUnion : Fintype (pairs.DefectZeroUnion block)]
  cited : ModularRep.PaperProofs.EvenFieldLemmas35_36Actual.CitedData
    (CitedRelativeWeylGroup := CitedRelativeWeylGroup)
    ell (S35.e1e4.toExactProvider r a ell ha).inBlock
    (S35.e1e4.toExactProvider r a ell ha).globalSeries.series
    D coherence block pairs initial GeneralisedSeries
  iota : PrimeRegularRootEmbedding ell k K (FiniteSymplecticFixed r a)
  hinj : IrreducibleBrauerCharacterInjectivity iota
  blockIdempotent : ι → k[FiniteSymplecticFixed r a]
  blocks : BlockIdempotentDecomposition blockIdempotent
  blockSource : LocalBlockInductionSource
    (p := ell) (k := k) (K := K) (G := FiniteSymplecticFixed r a)
    (Block := ι)
  alignment : AmbientBlockAlignment D pairs blockIdempotent blockSource
  T : FibreTransportSource iota hinj blocks (fieldAction r a ha) block
  Msys : ModularSystem ell K O k
  hcompat : StableReductionBrauerCharacterCompatibility Msys iota
  basicSet : RestrictedIntegralBasicSetOnIBrBlock iota hinj blocks block
    (↑(XC ell (S35.e1e4.toExactProvider r a ell ha).inBlock
      (S35.e1e4.toExactProvider r a ell ha).globalSeries.series))
    (decompositionMapOfStableReduction Msys iota hcompat)
  [finiteXC : Finite (↑(XC ell
    (S35.e1e4.toExactProvider r a ell ha).inBlock
    (S35.e1e4.toExactProvider r a ell ha).globalSeries.series))]
  fmz62 :
    let hfixed := oppositeFieldBlock_fixed_of_fibreTransport
      (ha := ha) (iota := iota) (hinj := hinj) (blocks := blocks)
      (block := block) (T := T)
    FMZ62TypeCRestrictedApplication
      r a ell ha D coherence block S35 pairs blockSource alignment hfixed
  conlon : PaperProofs.ConlonBasicSet.PadicConlonMarkDetection.{0, 0}
    (p := 2) (A := (FieldGroup a)ᵐᵒᵖ)
  burnside : PaperProofs.ConlonBasicSet.PublishedBurnsideMarkInjectivity.{0, 0}
    (A := (FieldGroup a)ᵐᵒᵖ)
  principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} ell k
  localReduction : ∀ w : LiteralWeightFibre blockSource block,
    SelectedLocalReductionSource blockSource block w
  ordinary :
    let fixation :=
      ModularRep.PaperProofs.EvenFieldLemmas35_36Actual.lemma_3_5_actual
        r a ell ha D coherence block S35
    let _ : MulAction (FieldGroup a)ᵐᵒᵖ
        (↑(XC ell
          (S35.e1e4.toExactProvider r a ell ha).inBlock
          (S35.e1e4.toExactProvider r a ell ha).globalSeries.series)) :=
      characterOppositeMulAction fixation
    OrdinaryTwistCompatibleLabels basicSet (oppositeFieldAction r a ha)

attribute [instance]
  P38LiteralBridgeInputs.groupDual
  P38LiteralBridgeInputs.fintypeDual
  P38LiteralBridgeInputs.groupCitedRelativeWeylGroup
  P38LiteralBridgeInputs.fieldK
  P38LiteralBridgeInputs.commRingO
  P38LiteralBridgeInputs.isDomainO
  P38LiteralBridgeInputs.fieldk
  P38LiteralBridgeInputs.algebraOK
  P38LiteralBridgeInputs.charZeroK
  P38LiteralBridgeInputs.charPk
  P38LiteralBridgeInputs.algClosedk
  P38LiteralBridgeInputs.mulActionA
  P38LiteralBridgeInputs.fintypeBlock
  P38LiteralBridgeInputs.mulActionBlock
  P38LiteralBridgeInputs.fintypeW
  P38LiteralBridgeInputs.fintypeDefectZeroUnion
  P38LiteralBridgeInputs.finiteXC

/-- Obtain the protected cyclic endgame only by invoking the rewritten literal
Phase C--D bridge.  There is intentionally no field of
`P38LiteralBridgeInputs` with this result type. -/
noncomputable def P38LiteralBridgeInputs.endgame
    {r a ell : ℕ} {ha : 0 < a}
    (source : P38LiteralBridgeInputs r a ell ha) :
    let _ := source.fintypeFixed
    let _ := source.finiteFieldOpp
    let _ := source.cyclicFieldOpp
    let _ := source.finiteField
    let _ := source.cyclicField
    CyclicEndgameData
      (iota := source.iota) (hinj := source.hinj) (blocks := source.blocks)
      (phi := fieldAction r a ha)
      (blockSource := source.blockSource) (block := source.block) source.T
      (canonicalRawNormalizerQuotientInput
        (p := ell) (K := source.K)
        (H := FiniteSymplecticFixed r a))
      source.localReduction :=
  letI := source.fintypeFixed
  letI := source.finiteFieldOpp
  letI := source.cyclicFieldOpp
  letI := source.finiteField
  letI := source.cyclicField
  Classical.choice
    (ModularRep.PaperProofs.EvenFieldProposition38Lemma37Bridge.proposition_3_8_to_lemma_3_7_actual
        r a ell ha source.block source.D
        source.coherence source.S35 source.pairs source.initial
        source.GeneralisedSeries source.cited source.iota source.hinj source.blocks
        source.blockSource source.alignment source.T source.Msys source.hcompat source.basicSet
        source.fmz62 source.conlon source.burnside source.principle
        source.localReduction source.ordinary)

/-! ## Cover-owned Theorem 3.18 source packet -/

/-- The minimal structural E1 packet for the concrete self-cover application.
The cover itself is owned here, once for the concrete fixed-point group, and
is never attached to the target Definition 3.5 endpoint. -/
structure HighRankSelfCoverAmbientU0
    {r a ell : ℕ} {ha : 0 < a}
    (source : P38LiteralBridgeInputs r a ell ha) where
  identification :
    let _ := source.fintypeFixed
    SelfCoverSourceIdentification
      (p := ell) (H := FiniteSymplecticFixed r a)
  automorphismMap_bijective :
    Function.Bijective (semidirectToMulAut
      (fieldAction r a ha))

/-- Build the structural clauses from the owned cover identification. -/
def HighRankSelfCoverAmbientU0.structural
    {r a ell : ℕ} {ha : 0 < a}
    {source : P38LiteralBridgeInputs r a ell ha}
    (ambient : HighRankSelfCoverAmbientU0 source) :
    StructuralSource (fieldAction r a ha) := by
  letI := source.fintypeFixed
  exact
    { perfect := ⟨ambient.identification.ellPrimeCover.perfect⟩
      centerless := ambient.identification.center_eq_bot
      automorphismMap_bijective := ambient.automorphismMap_bijective }

abbrev selfCoverProblem {r a ell : ℕ} {ha : 0 < a}
    (source : P38LiteralBridgeInputs r a ell ha) :=
  let _ := source.fintypeFixed
  let _ := source.finiteField
  SelfCoverProblem source.iota source.hinj source.blocks
      (fieldAction r a ha) source.blockSource source.block
      source.T source.localReduction

abbrev selfCoverAutomorphisms {r a ell : ℕ} {ha : 0 < a}
    (source : P38LiteralBridgeInputs r a ell ha)
    (ambient : HighRankSelfCoverAmbientU0 source) :=
  let _ := source.fintypeFixed
  let _ := source.finiteField
  let _ := source.cyclicField
  SelfCoverAutomorphisms source.iota source.hinj source.blocks
      (fieldAction r a ha) source.blockSource source.block
      source.T source.localReduction ambient.structural

/-- The E1/U carrier and action match between the concrete Proposition 3.8
block and one exact block of the full `H_G` family.  It is indexed by the pair,
the concrete model, the target block, and the Proposition 3.8 package.  It
contains no block source, cover ambient data, source semantics, or Definition
3.5 relation.  The `gamma_compatible` field retains the semantic comparison
with the fixed-point equivalence.  The abstract forward transport uses the
three carrier equivalences and their naturality directly, so it does not
consume that additional comparison. -/
structure HighRankConcreteEndpointCarrierMatchU0 {ell : ℕ}
    {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    {classification : FullHGTypeCClassificationSource scope}
    (pair : FullHG scope)
    (parameter : HighRankParameter)
    (hcase : classification.structuralCase coverage pair =
      .typeC (.rankAtLeastFour parameter))
    (model : HighRankPairConcreteModelU0 classification pair parameter hcase)
    (block : PairBlock coverage pair)
    (p38 : P38LiteralBridgeInputs parameter.rank parameter.fieldExponent ell
      parameter.positiveFieldExponent) where
  gammaEquiv :
    let _ := p38.fintypeFixed
    let _ := p38.finiteField
    let _ := p38.cyclicField
    (selfCoverProblem p38).Gamma ≃*
      ((coverage.presentation pair).family.problem block).Gamma
  brauerEquiv :
    let _ := p38.fintypeFixed
    let _ := p38.finiteField
    let _ := p38.cyclicField
    Definition35Brauer (selfCoverProblem p38) ≃
      Definition35Brauer ((coverage.presentation pair).family.problem block)
  weightEquiv :
    let _ := p38.fintypeFixed
    let _ := p38.finiteField
    let _ := p38.cyclicField
    Definition35Weight (selfCoverProblem p38) ≃
      Definition35Weight ((coverage.presentation pair).family.problem block)
  brauer_naturality :
    let _ := p38.fintypeFixed
    let _ := p38.finiteField
    let _ := p38.cyclicField
    let P := selfCoverProblem p38
    let Q := (coverage.presentation pair).family.problem block
    let _ : MulAction P.Gamma (Definition35Brauer P) :=
      definition35BrauerAction P
    let _ : MulAction Q.Gamma (Definition35Brauer Q) :=
      definition35BrauerAction Q
    ∀ (g : P.Gamma) (psi : Definition35Brauer P),
      brauerEquiv (g • psi) = gammaEquiv g • brauerEquiv psi
  weight_naturality :
    let _ := p38.fintypeFixed
    let _ := p38.finiteField
    let _ := p38.cyclicField
    let P := selfCoverProblem p38
    let Q := (coverage.presentation pair).family.problem block
    let _ : MulAction P.Gamma (Definition35Weight P) :=
      definition35WeightAction P
    let _ : MulAction Q.Gamma (Definition35Weight Q) :=
      definition35WeightAction Q
    ∀ (g : P.Gamma) (w : Definition35Weight P),
      weightEquiv (g • w) = gammaEquiv g • weightEquiv w
  gamma_compatible :
    let _ := p38.fintypeFixed
    let _ := p38.finiteField
    let _ := p38.cyclicField
    ((coverage.presentation pair).family.problem block).gamma.comp
        gammaEquiv.toMonoidHom =
      (MulAut.congr
        (model.familyToConcrete (coverage.presentation pair)).symm).toMonoidHom.comp
          (semidirectToMulAut
            (fieldAction parameter.rank parameter.fieldExponent
              parameter.positiveFieldExponent))

/-- The E2/U assertion that the fixed self-cover relation is carried forward
to the relation of the exact target block.  This proposition contains no
carrier choices.  Its source and target semantics are fixed by its indices. -/
structure HighRankConcreteEndpointRelationForwardU0 {ell : ℕ}
    {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    {classification : FullHGTypeCClassificationSource scope}
    (blockSource : FullHGBlockSource coverage)
    (pair : FullHG scope)
    (parameter : HighRankParameter)
    (hcase : classification.structuralCase coverage pair =
      .typeC (.rankAtLeastFour parameter))
    (model : HighRankPairConcreteModelU0 classification pair parameter hcase)
    (block : PairBlock coverage pair)
    (p38 : P38LiteralBridgeInputs parameter.rank parameter.fieldExponent ell
      parameter.positiveFieldExponent)
    (ambient : let _ := p38.fintypeFixed
      HighRankSelfCoverAmbientU0 p38)
    (carrierMatch : HighRankConcreteEndpointCarrierMatchU0
      pair parameter hcase model block p38)
    (selfCoverSource :
      let _ := p38.fintypeFixed
      let _ := p38.finiteField
      let _ := p38.cyclicField
      FLZSourceSemantics
        (selfCoverProblem p38) (selfCoverAutomorphisms p38 ambient)) : Prop where
  relation_forward :
    let _ := p38.fintypeFixed
    let _ := p38.finiteField
    let _ := p38.cyclicField
    ∀ (psi : Definition35Brauer (selfCoverProblem p38))
      (w : Definition35Weight (selfCoverProblem p38)),
      selfCoverSource.definition35BlockIsomorphic psi w →
        (blockSource.source pair block).definition35BlockIsomorphic
          (carrierMatch.brauerEquiv psi) (carrierMatch.weightEquiv w)

/-- Combine the ordinary forward transport from the fixed carrier data and
the separate proof of relation preservation. -/
def HighRankConcreteEndpointRelationForwardU0.toForwardTransport
    {ell : ℕ} {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    {blockSource : FullHGBlockSource coverage}
    {classification : FullHGTypeCClassificationSource scope}
    {pair : FullHG scope}
    {parameter : HighRankParameter}
    {hcase : classification.structuralCase coverage pair =
      .typeC (.rankAtLeastFour parameter)}
    {model : HighRankPairConcreteModelU0 classification pair parameter hcase}
    {block : PairBlock coverage pair}
    {p38 : P38LiteralBridgeInputs parameter.rank parameter.fieldExponent ell
      parameter.positiveFieldExponent}
    {ambient : let _ := p38.fintypeFixed
      HighRankSelfCoverAmbientU0 p38}
    {carrierMatch : HighRankConcreteEndpointCarrierMatchU0
      pair parameter hcase model block p38}
    {selfCoverSource :
      let _ := p38.fintypeFixed
      let _ := p38.finiteField
      let _ := p38.cyclicField
      FLZSourceSemantics
        (selfCoverProblem p38) (selfCoverAutomorphisms p38 ambient)}
    (certificate : HighRankConcreteEndpointRelationForwardU0
      blockSource pair parameter hcase model block p38 ambient carrierMatch
        selfCoverSource) :
    let _ := p38.fintypeFixed
    let _ := p38.finiteField
    let _ := p38.cyclicField
    Definition35ForwardTransport
      (selfCoverProblem p38) (selfCoverAutomorphisms p38 ambient) selfCoverSource
      ((coverage.presentation pair).family.problem block)
      (blockSource.automorphisms pair block)
      (blockSource.source pair block) := by
  letI := p38.fintypeFixed
  letI := p38.finiteField
  letI := p38.cyclicField
  exact
    { gammaEquiv := carrierMatch.gammaEquiv
      brauerEquiv := carrierMatch.brauerEquiv
      weightEquiv := carrierMatch.weightEquiv
      brauer_naturality := carrierMatch.brauer_naturality
      weight_naturality := carrierMatch.weight_naturality
      relation_forward := certificate.relation_forward }

/-- The theorem-specific high-rank source package.  Its fields are source
inputs for Proposition 3.8, Lemma 2.10, and Theorem 3.18.  The only
conclusion-producing component is the named external
`FLZ318Source.applyTheorem318` gate.  The exact source-to-target carrier match
is a separate E1/U object, and forward preservation of the fixed relation is a
separate E2/U proposition.
The classifier fixes the formal rank and field exponent before `model`, and
the exact classifier equality indexes this entire source package. -/
structure HighRankP38To318SourceU0 {ell : ℕ}
    {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    (blockSource : FullHGBlockSource coverage)
    (classification : FullHGTypeCClassificationSource scope)
    (pair : FullHG scope)
    (parameter : HighRankParameter)
    (hcase : classification.structuralCase coverage pair =
      .typeC (.rankAtLeastFour parameter))
    (model : HighRankPairConcreteModelU0 classification pair parameter hcase)
    (block : PairBlock coverage pair) where
  p38 : P38LiteralBridgeInputs parameter.rank parameter.fieldExponent ell
    parameter.positiveFieldExponent
  ambient :
    let _ := p38.fintypeFixed
    HighRankSelfCoverAmbientU0 p38
  globalRootInputs :
    let _ := p38.fintypeFixed
    let _ := p38.finiteField
    ∀ psi : BrauerFibre p38.iota p38.hinj p38.blocks p38.block,
      ClauseIVAGlobalRootInput p38.iota p38.hinj p38.blocks
        (fieldAction parameter.rank parameter.fieldExponent
          parameter.positiveFieldExponent)
        p38.blockSource p38.block p38.T psi
  localRootInputs :
    let _ := p38.fintypeFixed
    let _ := p38.finiteField
    ∀ psi : BrauerFibre p38.iota p38.hinj p38.blocks p38.block,
      ClauseIVBLocalRootInput
        (field := fieldAction parameter.rank parameter.fieldExponent
          parameter.positiveFieldExponent)
        (blockSource := p38.blockSource) (block := p38.block)
        (localReduction := p38.localReduction)
          (p38.endgame.omega.toEquiv psi)
  selfCoverSource :
    let _ := p38.fintypeFixed
    let _ := p38.finiteField
    let _ := p38.cyclicField
    FLZSourceSemantics
      (selfCoverProblem p38) (selfCoverAutomorphisms p38 ambient)
  endpointCarrierMatch :
    HighRankConcreteEndpointCarrierMatchU0
      pair parameter hcase model block p38
  endpointRelationForward :
    HighRankConcreteEndpointRelationForwardU0
      blockSource pair parameter hcase model block p38 ambient
        endpointCarrierMatch selfCoverSource
  theorem318 :
    let _ := p38.fintypeFixed
    let _ := p38.finiteFieldOpp
    let _ := p38.cyclicFieldOpp
    let _ := p38.finiteField
    let _ := p38.cyclicField
    FLZ318Source p38.iota p38.hinj p38.blocks
      (fieldAction parameter.rank parameter.fieldExponent
        parameter.positiveFieldExponent)
      p38.blockSource p38.block p38.T
      p38.localReduction ambient.structural p38.endgame selfCoverSource

/-- The kernel-facing endpoint: derive the cyclic endgame from the protected
literal Proposition 3.8 bridge, combine the explicit Theorem 3.18 package,
apply its fixed E2 source operation, and transport only the cover-free
Definition 3.5 endpoint. -/
theorem HighRankP38To318SourceU0.toDefinition35
    {ell : ℕ} {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    {blockSource : FullHGBlockSource coverage}
    {classification : FullHGTypeCClassificationSource scope}
    {pair : FullHG scope}
    {parameter : HighRankParameter}
    {hcase : classification.structuralCase coverage pair =
      .typeC (.rankAtLeastFour parameter)}
    {model : HighRankPairConcreteModelU0 classification pair parameter hcase}
    {block : PairBlock coverage pair}
    (source : HighRankP38To318SourceU0 blockSource classification pair
      parameter hcase model block) :
    HasDefinition35IBAW blockSource pair block := by
  letI : Fintype
      (FiniteSymplecticFixed parameter.rank parameter.fieldExponent) :=
    source.p38.fintypeFixed
  letI : Finite (FieldGroup parameter.fieldExponent)ᵐᵒᵖ :=
    source.p38.finiteFieldOpp
  letI : IsCyclic (FieldGroup parameter.fieldExponent)ᵐᵒᵖ :=
    source.p38.cyclicFieldOpp
  letI : Finite (FieldGroup parameter.fieldExponent) := source.p38.finiteField
  letI : IsCyclic (FieldGroup parameter.fieldExponent) :=
    source.p38.cyclicField
  let operations := source.theorem318.operations
  let endpointTransport :=
    source.endpointRelationForward.toForwardTransport
  let hypotheses := completedExplicitPackage_of_cyclicEndgame
    (iota := source.p38.iota) (hinj := source.p38.hinj)
    (blocks := source.p38.blocks)
    (field := fieldAction parameter.rank parameter.fieldExponent
      parameter.positiveFieldExponent)
    (blockSource := source.p38.blockSource) (block := source.p38.block)
    (T := source.p38.T) (localReduction := source.p38.localReduction)
    source.ambient.structural operations source.theorem318.operationAdapters
      source.p38.endgame source.globalRootInputs source.localRootInputs
  exact Nonempty.map endpointTransport.map
    (definition35IBAWBijection_of_theorem318
      (iota := source.p38.iota) (hinj := source.p38.hinj)
      (blocks := source.p38.blocks)
      (field := fieldAction parameter.rank parameter.fieldExponent
        parameter.positiveFieldExponent)
      (blockSource := source.p38.blockSource) (block := source.p38.block)
      (T := source.p38.T) (localReduction := source.p38.localReduction)
      (structural := source.ambient.structural)
      (endgame := source.p38.endgame) source.selfCoverSource
      source.theorem318 hypotheses source.ambient.identification)

/-! ## Direct U0 Proposition 3.9 dispatcher -/

/-- The U0 source record for one pair in the full `H_G` carrier.  The branch
sources outside high rank and the Bonnafé identity input are the existing
narrow or family adapters. The type A field fixes an actual SL/SU
presentation and the cover-free source on the same finite-splitting family.
`strictBlock_u0` supplies the defining and nondefining prime proofs and
projects the selected block. The split low rank field is indexed by the classifier's exact
`SplitLowRankParameter`.  It then fixes the concrete model and cover, certifies
the full universal central extension, separates a complete Definition 4.1
packet from the Definition 3.5 passage, and uses the same converter.  The high
rank input is the theorem-specific Proposition
3.8--Theorem 3.18 package above, not a Definition 3.5 conclusion.  It fixes one
concrete model before the selected unipotent block varies. -/
structure PairSourceInputsU0 {ell : ℕ}
    {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    (blockSource : FullHGBlockSource coverage)
    (strictSource : FullHGStrictQuasiIsolationAdapter coverage)
    (classification : FullHGTypeCClassificationSource scope)
    (pair : FullHG scope)
    (strictData : PairStrictBlockSource strictSource pair) where
  outsideOrder : ¬ ell ∣ Nat.card (coverage.presentation pair).family.H →
    ∀ block, strictSource.predicate pair block →
      OutsideOrderSource (coverage.presentation pair).family block
        (blockSource.automorphisms pair block)
        (blockSource.source pair block)
  typeA : classification.structuralCase coverage pair = .typeA →
    CoverFreeTypeAApplication (coverage.presentation pair).family
      (blockSource.automorphisms pair) (blockSource.source pair)
  bonnafeIdentity : ∀ {form : TypeCForm} {s : strictData.Dual},
    classification.structuralCase coverage pair = .typeC form →
      NotContainedInProperLevi (Subgroup.centralizer {s} : Set strictData.Dual)
        strictData.IsProperLevi →
      s = 1
  highRankP38To318 :
    ∀ (parameter : HighRankParameter)
      (hcase : classification.structuralCase coverage pair =
        .typeC (.rankAtLeastFour parameter)),
      Σ model : HighRankPairConcreteModelU0 classification pair parameter hcase,
        ∀ block, strictSource.predicate pair block →
          strictData.label block = 1 →
          HighRankP38To318SourceU0 blockSource classification pair parameter
            hcase model block
  splitLowRank : ∀ (parameter : SplitLowRankParameter)
      (hcase : classification.structuralCase coverage pair =
        .typeC (.splitLowRank parameter)),
    SchaefferFrySplitLowRankFamilySource classification pair parameter hcase
      (blockSource.automorphisms pair) (blockSource.source pair)
  sp6AtThree : classification.structuralCase coverage pair =
      .typeC (.splitSp6Two .three) →
    Sp6TwoThreeSource (coverage.presentation pair).family
      (blockSource.automorphisms pair) (blockSource.source pair)
  sp6AtFive : classification.structuralCase coverage pair =
      .typeC (.splitSp6Two .five) →
    Sp6TwoCyclicFiveSevenSource .five (coverage.presentation pair).family
      (blockSource.automorphisms pair) (blockSource.source pair)
  sp6AtSeven : classification.structuralCase coverage pair =
      .typeC (.splitSp6Two .seven) →
    Sp6TwoCyclicFiveSevenSource .seven (coverage.presentation pair).family
      (blockSource.automorphisms pair) (blockSource.source pair)
  suzuki : ∀ (parameter : SuzukiParameter)
      (hcase : classification.structuralCase coverage pair =
        .typeC (.simpleSuzuki parameter)),
    SpathSuzukiFamilySource classification pair parameter hcase
      (blockSource.automorphisms pair) (blockSource.source pair)

/-- Direct Proposition 3.9 dispatch for a U0 pair.  This deliberately avoids
the legacy relative router: the rank-at-least-four case consumes its
theorem-specific source package directly. -/
theorem strictBlock_u0 {ell : ℕ}
    {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    (blockSource : FullHGBlockSource coverage)
    (strictSource : FullHGStrictQuasiIsolationAdapter coverage)
    (classification : FullHGTypeCClassificationSource scope)
    (pair : FullHG scope)
    (strictData : PairStrictBlockSource strictSource pair)
    (source : PairSourceInputsU0 blockSource strictSource classification pair
      strictData) :
    ∀ block, strictSource.predicate pair block →
      HasDefinition35IBAW blockSource pair block := by
  intro block hstrict
  cases hcase : classification.structuralCase coverage pair with
  | primeOutsideOrder =>
      have hnotDvd :
          ¬ ell ∣ Nat.card (coverage.presentation pair).family.H :=
        (classification.structuralCase_eq_primeOutsideOrder_iff
          coverage pair).mp hcase
      exact
        (source.outsideOrder hnotDvd block hstrict).hasDefinition35IBAWBijection
  | typeA =>
      exact (source.typeA hcase).blockWitness scope.definingPrime scope.distinctPrimes block
  | typeC form =>
      have hquasi :
          NotContainedInProperLevi
            (Subgroup.centralizer {strictData.label block} : Set strictData.Dual)
            strictData.IsProperLevi :=
        quasiIsolated_of_strictlyQuasiIsolated
          (strictData.finiteCentralizer_le (strictData.label block))
          (strictData.connectedCentralizer_le (strictData.label block))
          (strictData.strictLabel block hstrict)
      have hlabel : strictData.label block = 1 :=
        source.bonnafeIdentity hcase hquasi
      cases form with
      | rankAtLeastFour parameter =>
          obtain ⟨model, highRankSource⟩ :=
            source.highRankP38To318 parameter hcase
          exact (highRankSource block hstrict hlabel).toDefinition35
      | splitLowRank parameter =>
          exact (source.splitLowRank parameter hcase).blockWitness block
      | splitSp6Two prime =>
          cases prime with
          | three => exact (source.sp6AtThree hcase).blockWitness block
          | five => exact (source.sp6AtFive hcase).blockWitness block
          | seven => exact (source.sp6AtSeven hcase).blockWitness block
      | simpleSuzuki parameter =>
          exact (source.suzuki parameter hcase).blockWitness
            scope.distinctPrimes block

/-- Combine the strict-block arm over the literal universe-zero full-`H_G`
carrier without passing through the legacy generic router. -/
theorem fullHG_strictBlocks_of_proposition39_u0 {ell : ℕ}
    {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    (blockSource : FullHGBlockSource coverage)
    (strictSource : FullHGStrictQuasiIsolationAdapter coverage)
    (classification : FullHGTypeCClassificationSource scope)
    (strictData : ∀ pair : FullHG scope,
      PairStrictBlockSource strictSource pair)
    (source : ∀ pair : FullHG scope,
      PairSourceInputsU0 blockSource strictSource classification pair
        (strictData pair)) :
    FullHGRelativeHypothesis55StrictBlocks blockSource strictSource where
  iBAWBijection pair block hstrict :=
    strictBlock_u0 blockSource strictSource classification pair (strictData pair)
      (source pair) block hstrict

end ModularRep.PaperProofs.EvenFieldProposition39HighRankU0


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
