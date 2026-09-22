import ManuscriptIBAW.TypeC.EvenApplicationTransport
import ManuscriptIBAW.TypeC.EvenApplicationCriterion
import ModularRep.PaperProofs.OddTwoWeightGroupEquiv
import ModularRep.BrauerCharacterEquivTransport

noncomputable section
namespace ManuscriptIBAW.TypeC.EvenApplication
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

open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldProposition39HighRankU0

/-- Source identifications (E1/U) between the block in Proposition 3.8 and the
specified block of the full H_G family. The data fix the pair, concrete
group model, target block, coefficient fields, transported root and induced
maps on Brauer characters and weight classes. The `gamma_compatible`
equation compares the group map with the fixed point isomorphism. The
relation in Definition 3.5 is transported separately. -/
structure EndpointCarrierMatch {ell : ℕ}
    {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    {classification : FullHGTypeCClassificationSource scope}
    (pair : FullHG scope)
    (parameter : HighRankParameter)
    (hcase : classification.structuralCase coverage pair =
      .typeC (.rankAtLeastFour parameter))
    (model : HighRankPairConcreteModelU0 classification pair parameter hcase)
    (block : PairBlock coverage pair)
    (p38 : UnipotentInputs parameter.rank parameter.fieldExponent ell
      parameter.positiveFieldExponent) where
  gammaEquiv :
    let _ := p38.fintypeFixed
    let _ := p38.finiteField
    let _ := p38.cyclicField
    (currentProblem p38).Gamma ≃*
      ((coverage.presentation pair).family.problem block).Gamma
  brauerEquiv :
    let _ := p38.fintypeFixed
    let _ := p38.finiteField
    let _ := p38.cyclicField
    Definition35Brauer (currentProblem p38) ≃
      Definition35Brauer ((coverage.presentation pair).family.problem block)
  weightEquiv :
    let _ := p38.fintypeFixed
    let _ := p38.finiteField
    let _ := p38.cyclicField
    Definition35Weight (currentProblem p38) ≃
      Definition35Weight ((coverage.presentation pair).family.problem block)
  modularField_eq : p38.k = (coverage.presentation pair).family.k
  ordinaryField_eq : p38.K = (coverage.presentation pair).family.K
  ambientRoot_compatible :
    let _ := p38.fintypeFixed
    HEq (p38.iota.alongMulEquiv
      (model.familyToConcrete (coverage.presentation pair)).symm)
      (coverage.presentation pair).family.iota
  brauer_compatible :
    let _ := p38.fintypeFixed
    let _ := p38.finiteField
    ∀ psi : Definition35Brauer (currentProblem p38),
      HEq (brauerEquiv psi).1
        (IrreducibleBrauerCharacter.alongMulEquiv p38.iota
          (model.familyToConcrete (coverage.presentation pair)).symm psi.1)
  weight_compatible :
    let _ := p38.fintypeFixed
    let _ := p38.finiteField
    ∀ w : Definition35Weight (currentProblem p38),
      HEq (weightEquiv w).1
        (Quotient.mk'' (Quotient.mk''
          ((selectedCharacterWeight p38.blockSource p38.block w).mapGroupEquiv
            (model.familyToConcrete (coverage.presentation pair)).symm)) :
          CharacterWeight.ConjugacyClass (p := ell) (K := p38.K)
            (G := (coverage.presentation pair).family.H))
  brauer_naturality :
    let _ := p38.fintypeFixed
    let _ := p38.finiteField
    let _ := p38.cyclicField
    let P := currentProblem p38
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
    let P := currentProblem p38
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

/-- All source and target maps have their actual group, scalar and character
coordinates before any relation is transported. -/
def EndpointCarrierMatch.physicalCoordinates
    {ell : ℕ} {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    {classification : FullHGTypeCClassificationSource scope}
    {pair : FullHG scope} {parameter : HighRankParameter}
    {hcase : classification.structuralCase coverage pair =
      .typeC (.rankAtLeastFour parameter)}
    {model : HighRankPairConcreteModelU0 classification pair parameter hcase}
    {block : PairBlock coverage pair}
    {p38 : UnipotentInputs parameter.rank parameter.fieldExponent ell
      parameter.positiveFieldExponent}
    (coordinates : EndpointCarrierMatch pair parameter hcase model block p38) :
    let _ := p38.fintypeFixed
    let _ := p38.finiteField
    PhysicalCoordinates (currentProblem p38)
      ((coverage.presentation pair).family.problem block) := by
  letI := p38.fintypeFixed
  letI := p38.finiteField
  exact
    { groupEquiv := (model.familyToConcrete (coverage.presentation pair)).symm
      prime_eq := rfl
      modularField_eq := coordinates.modularField_eq
      ordinaryField_eq := coordinates.ordinaryField_eq
      root_compatible := coordinates.ambientRoot_compatible
      gammaEquiv := coordinates.gammaEquiv
      brauerEquiv := coordinates.brauerEquiv
      weightEquiv := coordinates.weightEquiv
      gamma_compatible := coordinates.gamma_compatible
      brauer_compatible := coordinates.brauer_compatible
      weight_compatible := coordinates.weight_compatible
      brauer_naturality := coordinates.brauer_naturality
      weight_naturality := coordinates.weight_naturality }

/-- Sources for the unipotent application in higher rank. The classification
fixes the rank and field before the concrete model and block are chosen.
Apply the published criterion to the constructed bijection, then use
invariance of the standard relation under the specified change of
coordinates. -/
structure HighRankSource {ell : ℕ}
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
  p38 : UnipotentInputs parameter.rank parameter.fieldExponent ell
    parameter.positiveFieldExponent
  ambient :
    let _ := p38.fintypeFixed
    SelfCoverAmbient p38
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
      (currentProblem p38) (currentAutomorphisms p38 ambient)
  endpointCarrierMatch :
    EndpointCarrierMatch
      pair parameter hcase model block p38
  standardMeaning :
    let _ := p38.fintypeFixed
    let _ := p38.finiteField
    let _ := p38.cyclicField
    StandardInterpretations (currentProblem p38)
      ((coverage.presentation pair).family.problem block)
      (currentAutomorphisms p38 ambient) (blockSource.automorphisms pair block)
      selfCoverSource (blockSource.source pair block)
  standardTransport :
    let _ := p38.fintypeFixed
    let _ := p38.finiteField
    let _ := p38.cyclicField
    StandardIsomorphismSource standardMeaning.standardP
  bawRelation :
    let _ := p38.fintypeFixed
    FLZBAWGoodRelation (currentProblem p38)
    (currentAutomorphisms p38 ambient) ambient.identification.ellPrimeCover
  relationPassage : RelationPassage p38 ambient bawRelation selfCoverSource
  theorem318 : CriterionSource p38 ambient bawRelation

/-- Deduce the cyclic criterion hypotheses from Proposition 3.8, apply the
stated source for Theorem 3.18, and transport the resulting relation in
Definition 3.5 to the specified block. This last relation does not require a
choice of cover. -/
theorem HighRankSource.toDefinition35
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
    (source : HighRankSource blockSource classification pair
      parameter hcase model block) :
    HasDefinition35IBAW blockSource pair block := by
  let : Fintype
      (FiniteSymplecticFixed parameter.rank parameter.fieldExponent) :=
    source.p38.fintypeFixed
  let : Finite (FieldGroup parameter.fieldExponent)ᵐᵒᵖ :=
    source.p38.finiteFieldOpp
  let : IsCyclic (FieldGroup parameter.fieldExponent)ᵐᵒᵖ :=
    source.p38.cyclicFieldOpp
  let : Finite (FieldGroup parameter.fieldExponent) := source.p38.finiteField
  let : IsCyclic (FieldGroup parameter.fieldExponent) :=
    source.p38.cyclicField
  let forward := source.endpointCarrierMatch.physicalCoordinates.toForwardTransport
    source.standardMeaning source.standardTransport
  exact Nonempty.map forward.map
    (unipotent_definition35 source.p38 source.ambient source.bawRelation
      source.theorem318 source.globalRootInputs source.localRootInputs
      source.selfCoverSource source.relationPassage)

end ManuscriptIBAW.TypeC.EvenApplication

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
