import ModularRep.PaperProofs.EvenFieldP38ChosenDefinition35Transport
import ModularRep.PaperProofs.EvenFieldProposition39SemisimpleRouting

/-!
# The actual chosen-packet caller in a classified high-rank block

The existing P38 playlist, specified dictionary, chosen compatible packets,
standard-definition dictionaries and named FLZ 3.18 inputs are bundled here.
There is no carrier-equivalence or relation-forward field. Those fields of
the old high-rank routing API are computed from the actual chosen-packet
transport, including its group-coordinate square.

The explicit FLZ hypotheses are built from the protected aligned endgame
and its two existing extension-root inputs. The family witness uses the
bijection returned by FLZ 3.18. No equality with the endgame map is asserted.
This is the strict-block input to the guarded full-HG router, not a converse
from Definition 3.5 to equation (3.17) or the complete original condition.
-/

noncomputable section

namespace ModularRep.PaperProofs.EvenFieldP38ChosenHighRankApplication

open ModularRep CharacterWeight
open CyclicOuterLemma37Concrete CyclicOuterLemma37ActualBlockFibres
open EvenFieldConcreteTypeC EvenFieldFLZDefinition35Family EvenFieldFLZSourceConditions
open EvenFieldClassifiedP38FamilyPacket EvenFieldP38ChosenFamilyReduction
open EvenFieldP38ChosenDefinition35Transport EvenFieldBlockGroupEquivCoordinates
open EvenFieldProposition39HighRankU0 EvenFieldFLZ318FixedTheoremGate
open EvenFieldFLZ318SelfCoverExplicitHypotheses EvenFieldFLZDefinition35Transport
open EvenFieldFLZFullHG EvenFieldProposition39Relative
open EvenFieldProposition39FullHGStrictBlocks
open OddTwoCentralTwoRelationInflation OddTwoStandardBlockTripleTransport

section Family

variable {ell r a : ℕ} (family : Definition35Family.{0} ell)
variable (ha : 0 < a) [Fintype (FiniteSymplecticFixed r a)]
variable (e : family.H ≃* FiniteSymplecticFixed r a) (b : family.Block)
variable (adapter : Definition35AutomorphismStabilizerAdapter (family.problem b))
variable (familyFlz : FLZSourceSemantics (family.problem b) adapter)

/-- Only the already named authentic inputs. The actual family, its
coefficients, group map, block and source predicate are indices. No desired
matching, fibre map, action square or forward relation is a field. -/
structure ChosenApplicationInputs where
  source : FamilyInputs family ha e b
  dictionary : PhysicalDictionary family ha e b source
  packets : ∀ w : Definition35Weight (family.problem b),
    ChosenOwnReduction (family.problem b) w
  standard : BlockTripleSourceSemantics ell family.k family.K
  transport : StandardTransportSource standard
  ambient : HighRankSelfCoverAmbientU0
    (FamilyInputs.toP38 family ha e b (alignedInputs family ha e b source dictionary))
  concreteFlz : FLZSourceSemantics (concreteProblem family ha e b source dictionary)
    (concreteAdapter family ha e b source dictionary ambient)
  familyMeaning : ChosenDefinition35Interpretation (family.problem b)
    adapter familyFlz standard packets
  concreteMeaning : ChosenDefinition35Interpretation
    (concreteProblem family ha e b source dictionary)
    (concreteAdapter family ha e b source dictionary ambient) concreteFlz standard
    (concretePackets family ha e b source dictionary packets)
  globalRootInputs :
    let p38 := FamilyInputs.toP38 family ha e b
      (alignedInputs family ha e b source dictionary)
    letI := source.finiteField
    ∀ psi : BrauerFibre p38.iota p38.hinj p38.blocks p38.block,
      ClauseIVAGlobalRootInput p38.iota p38.hinj p38.blocks
        (fieldAction r a ha) p38.blockSource p38.block p38.T psi
  localRootInputs :
    let p38 := FamilyInputs.toP38 family ha e b
      (alignedInputs family ha e b source dictionary)
    letI := source.finiteField
    ∀ psi : BrauerFibre p38.iota p38.hinj p38.blocks p38.block,
      ClauseIVBLocalRootInput (field := fieldAction r a ha)
        (blockSource := p38.blockSource) (block := p38.block)
        (localReduction := p38.localReduction) (p38.endgame.omega.toEquiv psi)
  theorem318 : alignedTheorem318Source family ha e b source dictionary ambient concreteFlz

variable (data : ChosenApplicationInputs family ha e b adapter familyFlz)

/-- The literal P38 input has the rebuilt quotient table fixed before any
FLZ witness is selected. -/
abbrev ChosenApplicationInputs.p38 :=
  FamilyInputs.toP38 family ha e b
    (alignedInputs family ha e b data.source data.dictionary)

/-- The actual inverse maps and relation proof, all computed by the
chosen-packet consumer. -/
def ChosenApplicationInputs.endpointTransport : Definition35ForwardTransport
    (selfCoverProblem (data.p38 family ha e b adapter familyFlz))
    (selfCoverAutomorphisms (data.p38 family ha e b adapter familyFlz) data.ambient)
    data.concreteFlz (family.problem b) adapter familyFlz :=
  forwardTransport family ha e b data.source data.dictionary data.packets adapter
    data.ambient data.standard data.transport familyFlz data.concreteFlz
    data.familyMeaning data.concreteMeaning

/-- Remove the inverse/op notation in the proved action equation. This is
the literal group square required by the old classified carrier API. -/
theorem ChosenApplicationInputs.endpointTransport_gamma
    (d : (selfCoverProblem (data.p38 family ha e b adapter familyFlz)).Gamma) :
    (family.problem b).gamma
        ((data.endpointTransport family ha e b adapter familyFlz).gammaEquiv d) =
      MulAut.congr e.symm
        ((selfCoverProblem (data.p38 family ha e b adapter familyFlz)).gamma d) := by
  let Eg := EvenFieldP38FamilyGammaEquivariance.gammaEquiv family ha e b
    (alignedInputs family ha e b data.source data.dictionary)
    (alignedDictionary family ha e b data.source data.dictionary) adapter data.ambient
  have h := EvenFieldP38FamilyGammaEquivariance.gammaEquiv_action family ha e b
    (alignedInputs family ha e b data.source data.dictionary)
    (alignedDictionary family ha e b data.source data.dictionary) adapter data.ambient
    ((Eg.symm d)⁻¹)
  have hu := congrArg MulOpposite.unop h
  change (selfCoverProblem (data.p38 family ha e b adapter familyFlz)).gamma
      ((Eg ((Eg.symm d)⁻¹))⁻¹) =
    MulAut.congr e ((family.problem b).gamma (((Eg.symm d)⁻¹)⁻¹)) at hu
  have hs : (selfCoverProblem (data.p38 family ha e b adapter familyFlz)).gamma d =
      MulAut.congr e ((family.problem b).gamma (Eg.symm d)) := by
    simpa only [map_inv, Eg.apply_symm_apply, inv_inv] using hu
  ext x
  have hx := congrArg
    (fun f : MulAut (FiniteSymplecticFixed r a) => e.symm (f (e x))) hs
  change e.symm
      ((selfCoverProblem (data.p38 family ha e b adapter familyFlz)).gamma d (e x)) =
    e.symm (e ((family.problem b).gamma (Eg.symm d) (e.symm (e x)))) at hx
  change (family.problem b).gamma (Eg.symm d) x =
    e.symm ((selfCoverProblem (data.p38 family ha e b adapter familyFlz)).gamma d (e x))
  have hc : e.symm (e ((family.problem b).gamma (Eg.symm d) (e.symm (e x)))) =
      (family.problem b).gamma (Eg.symm d) x :=
    (e.symm_apply_apply _).trans
      (congrArg (fun y : family.H => (family.problem b).gamma (Eg.symm d) y)
        (e.symm_apply_apply x))
  exact hc.symm.trans hx.symm

/-- Combine the existing completed package from the protected endgame
and the same named global/local extension-root inputs. -/
def ChosenApplicationInputs.explicitHypotheses :
    alignedExplicitHypotheses family ha e b data.source data.dictionary data.ambient
      data.concreteFlz data.theorem318 := by
  letI := data.source.finiteFieldOpp
  letI := data.source.cyclicFieldOpp
  letI := data.source.finiteField
  letI := data.source.cyclicField
  let p38 := data.p38 family ha e b adapter familyFlz
  exact completedExplicitPackage_of_cyclicEndgame
    (iota := p38.iota) (hinj := p38.hinj) (blocks := p38.blocks)
    (field := fieldAction r a ha) (blockSource := p38.blockSource)
    (block := p38.block) (T := p38.T) (localReduction := p38.localReduction)
    data.ambient.structural data.theorem318.operations data.theorem318.operationAdapters
    p38.endgame data.globalRootInputs data.localRootInputs

include data in
/-- The actual caller applies the EXISTING FLZ theorem and transports its
returned bijection. No caller-supplied completed package is needed. -/
theorem ChosenApplicationInputs.familyWitness :
    Nonempty (Definition35IBAWBijection (family.problem b) adapter familyFlz) :=
  familyBijection_of_theorem318 family ha e b data.source data.dictionary data.packets
    adapter data.ambient data.standard data.transport familyFlz data.concreteFlz
    data.familyMeaning data.concreteMeaning data.theorem318
    (data.explicitHypotheses family ha e b adapter familyFlz)

end Family

section Classified

variable {ell : ℕ} {scope : FLZFullHGUniverse 2 ell}
variable {coverage : FullHGDefinition35Coverage scope}
variable (blockSource : FullHGBlockSource coverage)
variable (classification : FullHGTypeCClassificationSource scope)
variable (pair : FullHG scope) (parameter : HighRankParameter)
variable (hcase : classification.structuralCase coverage pair =
  .typeC (.rankAtLeastFour parameter))
variable (model : HighRankPairConcreteModelU0 classification pair parameter hcase)
variable [Fintype (FiniteSymplecticFixed parameter.rank parameter.fieldExponent)]
variable (block : PairBlock coverage pair)

/-- Specialize every source component to the classified pair's actual
presentation and its existing fixed-point-to-concrete equivalence. -/
abbrev ClassifiedInputs := ChosenApplicationInputs
  (coverage.presentation pair).family parameter.positiveFieldExponent
  (model.familyToConcrete (coverage.presentation pair)) block
  (blockSource.automorphisms pair block) (blockSource.source pair block)

variable (data : ClassifiedInputs blockSource classification pair parameter hcase model block)

/-- The old carrier-match record is now a K output. Its three equivalences,
two action laws and exact fixed-point group square are all computed. -/
def endpointCarrierMatch : HighRankConcreteEndpointCarrierMatchU0
    pair parameter hcase model block
    (data.p38 (coverage.presentation pair).family parameter.positiveFieldExponent
      (model.familyToConcrete (coverage.presentation pair)) block
      (blockSource.automorphisms pair block) (blockSource.source pair block)) := by
  let family := (coverage.presentation pair).family
  let e := model.familyToConcrete (coverage.presentation pair)
  let T := data.endpointTransport family parameter.positiveFieldExponent e block
    (blockSource.automorphisms pair block) (blockSource.source pair block)
  exact
    { gammaEquiv := T.gammaEquiv
      brauerEquiv := T.brauerEquiv
      weightEquiv := T.weightEquiv
      brauer_naturality := T.brauer_naturality
      weight_naturality := T.weight_naturality
      gamma_compatible := by
        apply MonoidHom.ext
        intro d
        exact data.endpointTransport_gamma family parameter.positiveFieldExponent e block
          (blockSource.automorphisms pair block) (blockSource.source pair block) d }

/-- Feed the unchanged guarded high-rank router with actual computed
carrier and relation fields. No free old match or forward source is accepted. -/
def toHighRankSource : HighRankP38To318SourceU0 blockSource classification pair
    parameter hcase model block where
  p38 := data.p38 (coverage.presentation pair).family parameter.positiveFieldExponent
    (model.familyToConcrete (coverage.presentation pair)) block
    (blockSource.automorphisms pair block) (blockSource.source pair block)
  ambient := data.ambient
  globalRootInputs := data.globalRootInputs
  localRootInputs := data.localRootInputs
  selfCoverSource := data.concreteFlz
  endpointCarrierMatch := endpointCarrierMatch blockSource classification pair parameter
    hcase model block data
  endpointRelationForward :=
    { relation_forward :=
        (data.endpointTransport (coverage.presentation pair).family
          parameter.positiveFieldExponent
          (model.familyToConcrete (coverage.presentation pair)) block
          (blockSource.automorphisms pair block) (blockSource.source pair block)).relation_forward }
  theorem318 := data.theorem318

include data in
/-- Fixed-family output for this exact classified pair and block. This
invokes the chosen-packet caller, preserving the source's returned map. -/
theorem toDefinition35 : HasDefinition35IBAW blockSource pair block :=
  data.familyWitness (coverage.presentation pair).family parameter.positiveFieldExponent
    (model.familyToConcrete (coverage.presentation pair)) block
    (blockSource.automorphisms pair block) (blockSource.source pair block)

end Classified

end ModularRep.PaperProofs.EvenFieldP38ChosenHighRankApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
