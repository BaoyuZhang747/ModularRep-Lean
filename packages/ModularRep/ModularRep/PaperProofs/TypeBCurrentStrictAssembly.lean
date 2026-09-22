import ModularRep.PaperProofs.TypeBCurrentStrictRouting
import ModularRep.PaperProofs.TypeBCurrentPrincipalInputs

/-!
# Strict-block construction over the complete relative type B class

The source package is indexed by the exhaustive structural route of each
actual relative pair. Type A uses the published fixed-family application;
rank two uses the corrected principal seed construction; every Spin rank
at least three uses the current principal supplier on that factor's own
field, including its exceptional rank-three field-three branch.

The selected principal carriers are derived from the same source-strict
block by the established Jordan routing. All coefficient fields, roots,
groups, block labels, automorphism adapters and Definition 3.5 relations
are those of the original relative-family presentation. No final witness
on all relative pairs, and no selected subfamily of pairs, is an input.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBCurrentStrictAssembly

open ModularRep
open EvenFieldFLZDefinition35Family EvenFieldFLZSourceConditions EvenFieldFLZFullHG
open OddTwoFullHGPrincipalRouting OddTwoTypeASourceJoin
open TypeBCurrentStrictRouting TypeBCurrentPrincipalInputs

/-- Construction inputs for precisely the branch selected by the actual
group classification. The corrected B2 packet and the Spin packet contain
their construction data; their resulting block bijections are computed.
The older type-A algebraic-closure convention is confined to that branch
and is not imposed on a Spin splitting modular system. -/
inductive BranchInputs {p : ℕ} (family : Definition35Family 2)
    (isStrict : family.Block → Prop)
    (automorphisms : ∀ block : family.Block,
      Definition35AutomorphismStabilizerAdapter (family.problem block))
    (semantics : ∀ block : family.Block,
      FLZSourceSemantics (family.problem block) (automorphisms block)) :
    TypeBCurrentStrictRouting.RelativePairSource p family isStrict → Type 1 where
  | typeA {rank : ℕ} {positive : 0 < rank}
      {presentation : TypeAActualPresentation p rank family.H}
      (application : TypeAApplicationData family presentation automorphisms semantics) :
      BranchInputs family isStrict automorphisms semantics
        (.typeA rank positive presentation)
  | rankTwo {data : SymplecticJordanData p 2 family isStrict}
      (construction : ∀ (block : family.Block) (hstrict : isStrict block),
        Nonempty (CompletedPrincipalSeedAt family block
          (automorphisms block) (semantics block) 2 data.coordinates.F
          (data.principalCarrier (by decide) block hstrict))) :
      BranchInputs family isStrict automorphisms semantics (.rankTwo data)
  | spin {rank : ℕ} {rankAtLeastThree : 3 ≤ rank}
      {data : SpinJordanData p rank family isStrict}
      (construction : ∀ (block : family.Block) (hstrict : isStrict block),
        Nonempty (PrincipalSpinInputs family block data.coordinates
          (data.principalCarrier rankAtLeastThree block hstrict)
          (automorphisms block) (semantics block))) :
      BranchInputs family isStrict automorphisms semantics
        (.spin rank rankAtLeastThree data)

namespace BranchInputs

variable {p : ℕ} {family : Definition35Family 2}
    {isStrict : family.Block → Prop}
    {automorphisms : ∀ block : family.Block,
      Definition35AutomorphismStabilizerAdapter (family.problem block)}
    {semantics : ∀ block : family.Block,
      FLZSourceSemantics (family.problem block) (automorphisms block)}
    {route : TypeBCurrentStrictRouting.RelativePairSource p family isStrict}

/-- Exhaust the actual structural cases and compute the witness on the
same selected block. The Spin supplier makes its own child-field branch
test, so an ambient nonexceptionality condition cannot remove a q3 child. -/
theorem blockWitness (inputs : BranchInputs family isStrict automorphisms semantics route)
    (definingPrime : p.Prime) (distinctPrimes : 2 ≠ p)
    (block : family.Block) (hstrict : isStrict block) :
    Nonempty (Definition35IBAWBijection (family.problem block)
      (automorphisms block) (semantics block)) := by
  cases inputs with
  | @typeA rank positive presentation application =>
    exact application.blockWitness definingPrime distinctPrimes positive block
  | rankTwo construction =>
    obtain ⟨seedInputs⟩ := construction block hstrict
    exact ⟨seedInputs.seed⟩
  | spin construction =>
    obtain ⟨principalInputs⟩ := construction block hstrict
    exact ⟨principalInputs.witness⟩

end BranchInputs

variable {p : ℕ} {scope : FLZFullHGUniverse p 2}
    {coverage : FullHGDefinition35Coverage scope}
    {strictSource : FullHGStrictQuasiIsolationAdapter coverage}
    (routing : FullHGRouting coverage strictSource)
    (blockSource : FullHGBlockSource coverage)

/-- Total construction inputs over the existing nonselective FullHG.
The index fixes the structural branch before its inputs are supplied;
neither the relative pair nor a source-strict block may be omitted. -/
structure StrictSources where
  atPair : ∀ pair : FullHG scope,
    BranchInputs (coverage.presentation pair).family (strictSource.predicate pair)
      (blockSource.automorphisms pair) (blockSource.source pair) (routing.atPair pair)

/-- Construct the complete Hypothesis 5.5(b) quantifier from the exhaustive
type-A, corrected B2 and current principal Spin constructions. -/
def completeRelativeHypothesis55StrictBlocks
    (sources : StrictSources routing blockSource) :
    FullHGRelativeHypothesis55StrictBlocks blockSource strictSource where
  iBAWBijection pair block hstrict :=
    (sources.atPair pair).blockWitness scope.definingPrime scope.distinctPrimes block hstrict

end ModularRep.PaperProofs.TypeBCurrentStrictAssembly


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
