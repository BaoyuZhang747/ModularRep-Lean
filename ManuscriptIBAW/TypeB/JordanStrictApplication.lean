import ManuscriptIBAW.TypeB.JordanRouting
import ManuscriptIBAW.TypeB.PrincipalApplication

/-!
# The complete strict block hypothesis for Type B

The relative class contains every required algebraic pair, including the
ambient pair and exceptional lower Spin factors. The selected strict labels
agree with those in the original source models. Type A uses its published
application for all blocks, B2 uses Li–Li and central lifting, and the
Spin groups of higher rank use the principal construction, including its
exceptional field case.
-/

noncomputable section
set_option autoImplicit false

namespace ManuscriptIBAW.TypeB.JordanStrictApplication

open ModularRep ModularRep.PaperProofs
open EvenFieldFLZDefinition35Family EvenFieldFLZSourceConditions EvenFieldFLZFullHG
open TypeBCurrentStrictRouting OddTwoFullHGPrincipalRouting OddTwoTypeASourceJoin
open OddTwoJordanLabelAndSeedTransport

variable {p : ℕ} {scope : FLZFullHGUniverse p 2}
  {coverage : FullHGDefinition35Coverage scope}
  {strictSource : FullHGStrictQuasiIsolationAdapter coverage}
  (blockSource : FullHGBlockSource coverage)
  (interpretation : ManuscriptIBAW.Jordan.TypeBLocalized.FullHGInterpretation
    scope coverage blockSource strictSource)

/-- The assumptions are indexed by the specified group classification. The
completed principal construction and the resulting family bijection are
conclusions. -/
inductive BranchSources (pair : FullHG scope) :
    TypeBCurrentStrictRouting.RelativePairSource p (coverage.presentation pair).family
      (strictSource.predicate pair) → Type 1 where
  | typeA {rank : ℕ} {positive : 0 < rank}
      {presentation : TypeAActualPresentation p rank (coverage.presentation pair).family.H}
      (application : TypeAApplicationData (coverage.presentation pair).family presentation
        (blockSource.automorphisms pair) (blockSource.source pair)) :
      BranchSources pair (.typeA rank positive presentation)
  | rankTwo {data : SymplecticJordanData p 2 (coverage.presentation pair).family
        (strictSource.predicate pair)}
      (construction : ∀ (b : (coverage.presentation pair).family.Block),
        strictSource.predicate pair b →
        ManuscriptIBAW.TypeC.LiLiSource.RankTwoPrincipalInputs data.coordinates.F
          ((coverage.presentation pair).family.problem b)
          (blockSource.automorphisms pair b) (blockSource.source pair b)) :
      BranchSources pair (.rankTwo data)
  | spin {rank : ℕ} {rankAtLeastThree : 3 ≤ rank}
      {data : SpinJordanData p rank (coverage.presentation pair).family
        (strictSource.predicate pair)}
      (construction : ∀ (b : (coverage.presentation pair).family.Block)
        (h : strictSource.predicate pair b),
        PrincipalApplication.PrincipalApplicationInputs (coverage.presentation pair).family b
          data.coordinates (data.principalCarrier rankAtLeastThree b h)
          (blockSource.automorphisms pair b) (blockSource.source pair b)) :
      BranchSources pair (.spin rank rankAtLeastThree data)

/-- Construct the witness on the same block from its selected structural case. -/
theorem BranchSources.blockWitness {pair : FullHG scope}
    {route : TypeBCurrentStrictRouting.RelativePairSource p (coverage.presentation pair).family
      (strictSource.predicate pair)}
    (sources : BranchSources blockSource pair route)
    (b : (coverage.presentation pair).family.Block) (h : strictSource.predicate pair b) :
    Nonempty (Definition35IBAWBijection ((coverage.presentation pair).family.problem b)
      (blockSource.automorphisms pair b) (blockSource.source pair b)) := by
  cases sources with
  | @typeA rank positive presentation application =>
      exact application.blockWitness scope.definingPrime scope.distinctPrimes positive b
  | rankTwo construction =>
      exact ⟨JordanRouting.rankTwoBijection blockSource pair b (construction b h)⟩
  | spin construction => exact (construction b h).exists_witness

/-- The same interpretation determines the label and complete source data in
each case. The `FullHG` relation retains every required cover. -/
structure Sources (routing : FullHGRouting coverage strictSource) where
  labels : JordanRouting.FullLabelBinding blockSource interpretation routing
  atPair : ∀ pair : FullHG scope,
    BranchSources blockSource pair (routing.atPair pair)

theorem Sources.strictBlocks {routing : FullHGRouting coverage strictSource}
    (sources : Sources blockSource interpretation routing) :
    FullHGRelativeHypothesis55StrictBlocks blockSource strictSource :=
  { iBAWBijection := fun pair b h =>
      (sources.atPair pair).blockWitness blockSource b h }

end ManuscriptIBAW.TypeB.JordanStrictApplication

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
