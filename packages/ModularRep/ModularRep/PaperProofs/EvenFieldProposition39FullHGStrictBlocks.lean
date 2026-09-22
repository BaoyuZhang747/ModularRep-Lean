import ModularRep.PaperProofs.EvenFieldProposition39FullHGStrictBlockCore
import ModularRep.PaperProofs.EvenFieldProposition39OutsideOrder
import ModularRep.PaperProofs.EvenFieldProposition39Relative
import ModularRep.PaperProofs.EvenFieldProposition39SplitLowRank
import ModularRep.PaperProofs.EvenFieldProposition39Sp6CyclicFiveSeven
import ModularRep.PaperProofs.EvenFieldProposition39Sp6Three
import ModularRep.PaperProofs.EvenFieldProposition39Suzuki
import ModularRep.PaperProofs.EvenFieldProposition39TypeA

/-!
# The full `H_G` strict-block construction in Proposition 3.9

This module instantiates the checked case split in
`EvenFieldProposition39Relative` separately for every member of the
nonselective relative carrier `FullHG`.  The target predicates are fixed:
strictness is the predicate in `FullHGStrictQuasiIsolationAdapter`, the
structural case is derived by `FullHGTypeCClassificationSource.structuralCase`,
and the conclusion for a block is the literal nonemptiness of its
`Definition35IBAWBijection` type.  The shared set of blocks, fixed target,
and strict quasi-isolation source are imported from the neutral core module.
The derived router decides the outside-order branch from the literal order of
the presented group.  It consults the external classifier only when the
coefficient prime divides that order, and the classifier cannot return the
outside-order case.

`PairStrictBlockSource` contains only the source-shaped dual label,
centralisers, proper-Levi predicate, centraliser inclusions, and the
strict-label implication required by the kernel-checked centraliser
argument.  `PairSourceInputs` exposes each cited branch input separately.
The prime outside the group order branch supplies the narrow representation theoretic
`OutsideOrderSource`; Lean constructs its literal equivariant bijection.
The type A branch supplies the independently established cover-free type A
consequence on an actual SL/SU presentation, with prime, quasisimple and
finite-splitting applicability. Lean applies it on the same family and
projects the selected block. The old BAW-good composite remains a
constructor on its valid prime-to-ell-cover domain.
The split low rank branch supplies a
`SchaefferFrySplitLowRankFamilySource` indexed by the classifier's exact branch,
field exponent, and bound.  The source fixes the concrete fixed-point model,
universal prime-to-`ell` cover, and full universal central extension
certificate.  It separates the complete Definition 4.1 packet from the
implication to the Definition 3.5 relation and lets Lean apply the generic
converter before projecting the selected block.  The
`Sp6(2)` branch at three supplies one `Sp6TwoThreeSource`.  Schaeffer Fry's
theorem provides a complete Definition 4.1 packet on the covering family,
which is passed through the exact indexed Spath source and then through the
separate implication to the Definition 3.5 relation.
The `Sp6(2)` branches at five and seven supply the closed prime
`Sp6TwoCyclicFiveSevenSource`; Lean derives cyclicity of every subgroup at the
selected prime.  A first cited source supplies the complete Definition 4.1
packet on the cover, a second performs the indexed Spath passage, and a third
  supplies the implication to the Definition 3.5 relation.  In the Suzuki
branch the classifier equality carries the positive twist parameter.  The
`SpathSuzukiFamilySource` then separates the exact cover model, the
Corollary 6.3 packet, the indexed Spath passage, and the Definition 3.5
relation implication.  The legacy high rank field is indexed by a
`HighRankParameter` and the exact classifier equality, so its formal rank and
field exponent cannot change during routing.  It still supplies the
conclusion-shaped `HasDefinition35IBAW` implication after the strictness and
unipotence premises and therefore remains E2/U.  In particular, none of these
structures has an arbitrary strictness predicate or a selectable BAW-good
predicate. The type A endpoint applies its guarded independent source;
the split low rank endpoint composes the separately graded sources through
the K converter. Both then project the selected block.
The other family adapters retain their documented cited sources.  None is a
generic premise for every strictly quasi-isolated block.

Lean proves only the total construction: it converts these fixed inputs to
`Data` and `SourceInputs`, applies `strict_block_hypothesis_relative` for
each pair, and packages the resulting family as
`FullHGRelativeHypothesis55StrictBlocks`.
-/

noncomputable section

namespace ModularRep.PaperProofs.EvenFieldProposition39FullHGStrictBlocks

open scoped Pointwise
open ModularRep.ManuscriptVerification.StrictQuasiIsolation
open ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
open ModularRep.PaperProofs.EvenFieldFLZFullHG
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldProposition39OutsideOrder
open ModularRep.PaperProofs.EvenFieldProposition39Relative
open ModularRep.PaperProofs.EvenFieldProposition39SplitLowRank
open ModularRep.PaperProofs.EvenFieldProposition39Sp6CyclicFiveSeven
open ModularRep.PaperProofs.EvenFieldProposition39Sp6Three
open ModularRep.PaperProofs.EvenFieldProposition39Suzuki
open ModularRep.PaperProofs.EvenFieldProposition39TypeA

universe u

/-- The exact `Data` consumed by the checked Proposition 3.9 case split.

Its structural case, strict-block predicate, and Definition 3.5 conclusion are fixed
definitionally.  Only the intermediate unipotence predicate is supplied by
the branch source because it is the subject of one cited implication. -/
def proposition39Data {ell : ℕ}
    {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    (blockSource : FullHGBlockSource coverage)
    (strictSource : FullHGStrictQuasiIsolationAdapter coverage)
    (classification : FullHGTypeCClassificationSource scope)
    (pair : FullHG scope)
    (strictData : PairStrictBlockSource strictSource pair)
    (IsUnipotent : PairBlock coverage pair → Prop) :
    Data strictData.Dual (PairBlock coverage pair) where
  groupCase := classification.structuralCase coverage pair
  IsStrictBlock := strictSource.predicate pair
  HasIBAW := HasDefinition35IBAW blockSource pair
  IsUnipotent := IsUnipotent
  label := strictData.label
  finiteCentralizer := fun block ↦
    strictData.finiteCentralizer (strictData.label block)
  connectedCentralizer := fun block ↦
    strictData.connectedCentralizer (strictData.label block)
  IsProperLevi := strictData.IsProperLevi
  finiteCentralizer_le := fun block ↦
    strictData.finiteCentralizer_le (strictData.label block)
  connectedCentralizer_le := fun block ↦
    strictData.connectedCentralizer_le (strictData.label block)
  strictLabel := strictData.strictLabel

/-- The cited inputs for one fixed pair, indexed explicitly by the branch of
the exhaustive structural classification.

The field for a prime outside the group order is indexed by literal
nondivisibility and supplies only the narrow `OutsideOrderSource`.  The router
derives that nondivisibility proof, and the literal Definition 3.5 bijection is
constructed in the kernel. The type A field carries actual finite SL/SU
coordinates and the cover-free source, with finite-splitting coefficients.
Lean supplies `scope.definingPrime` and `scope.distinctPrimes` and projects
the same block. The split low rank field additionally fixes the concrete
model, exact cover, and full universal central extension certificate, and
requires a complete Definition 4.1 packet before using the same generic
conversion.  The `Sp6(2)` fields supply fixed sources for their whole
families.  The Suzuki field is indexed by the exact classifier equality and
supplies the staged source packet described above.  Lean projects the selected
block without using strictness in any of these cases.  The legacy high rank
branch preserves the classifier's formal parameter but remains the only field
that concludes the
fixed `HasDefinition35IBAW` predicate after the strictness and unipotence
premises.  No field asserts the generic implication that all strictly
quasi-isolated blocks have the required bijection; that total implication is
the theorem proved below. -/
structure PairSourceInputs {ell : ℕ}
    {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    (blockSource : FullHGBlockSource coverage)
    (strictSource : FullHGStrictQuasiIsolationAdapter coverage)
    (classification : FullHGTypeCClassificationSource scope)
    (pair : FullHG scope)
    (strictData : PairStrictBlockSource strictSource pair) where
  IsUnipotent : PairBlock coverage pair → Prop
  outsideOrder : ¬ ell ∣ Nat.card (coverage.presentation pair).family.H →
    ∀ block, strictSource.predicate pair block →
      OutsideOrderSource (coverage.presentation pair).family block
        (blockSource.automorphisms pair block)
        (blockSource.source pair block)
  typeA : classification.structuralCase coverage pair = .typeA →
    CoverFreeTypeAApplication
      (coverage.presentation pair).family
      (blockSource.automorphisms pair)
      (blockSource.source pair)
  bonnafeIdentity : ∀ {form : TypeCForm} {s : strictData.Dual},
    classification.structuralCase coverage pair = .typeC form →
      NotContainedInProperLevi
        (Subgroup.centralizer {s} : Set strictData.Dual)
        strictData.IsProperLevi →
      s = 1
  identitySeriesUnipotent : ∀ {form : TypeCForm}
      (block : PairBlock coverage pair),
    classification.structuralCase coverage pair = .typeC form →
      strictSource.predicate pair block →
      strictData.label block = 1 →
      IsUnipotent block
  highRankUnipotent : ∀ parameter : HighRankParameter,
    classification.structuralCase coverage pair =
        .typeC (.rankAtLeastFour parameter) →
      ∀ block, strictSource.predicate pair block →
        IsUnipotent block →
        HasDefinition35IBAW blockSource pair block
  splitLowRank : ∀ (parameter : SplitLowRankParameter)
      (hcase : classification.structuralCase coverage pair =
        .typeC (.splitLowRank parameter)),
    SchaefferFrySplitLowRankFamilySource classification pair parameter hcase
      (blockSource.automorphisms pair) (blockSource.source pair)
  sp6AtThree :
    classification.structuralCase coverage pair =
        .typeC (.splitSp6Two .three) →
      Sp6TwoThreeSource (coverage.presentation pair).family
        (blockSource.automorphisms pair) (blockSource.source pair)
  sp6AtFive :
    classification.structuralCase coverage pair =
        .typeC (.splitSp6Two .five) →
      Sp6TwoCyclicFiveSevenSource .five
        (coverage.presentation pair).family
        (blockSource.automorphisms pair) (blockSource.source pair)
  sp6AtSeven :
    classification.structuralCase coverage pair =
        .typeC (.splitSp6Two .seven) →
      Sp6TwoCyclicFiveSevenSource .seven
        (coverage.presentation pair).family
        (blockSource.automorphisms pair) (blockSource.source pair)
  suzuki : ∀ (parameter : SuzukiParameter)
      (hcase : classification.structuralCase coverage pair =
        .typeC (.simpleSuzuki parameter)),
      SpathSuzukiFamilySource classification pair parameter hcase
        (blockSource.automorphisms pair) (blockSource.source pair)

/-- Convert the explicitly indexed cited inputs for one pair to the fixed
abstract interface used by `strict_block_hypothesis_relative`. -/
theorem PairSourceInputs.toRelative {ell : ℕ}
    {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    {blockSource : FullHGBlockSource coverage}
    {strictSource : FullHGStrictQuasiIsolationAdapter coverage}
    {classification : FullHGTypeCClassificationSource scope}
    {pair : FullHG scope}
    {strictData : PairStrictBlockSource strictSource pair}
    (source : PairSourceInputs blockSource strictSource classification pair
      strictData) :
    SourceInputs (proposition39Data blockSource strictSource classification
      pair strictData source.IsUnipotent) where
  outsideOrder := fun hcase block hstrict ↦
    (source.outsideOrder
      ((classification.structuralCase_eq_primeOutsideOrder_iff
        coverage pair).mp hcase)
      block hstrict).hasDefinition35IBAWBijection
  typeA := fun hcase block _hstrict ↦
    (source.typeA hcase).blockWitness scope.definingPrime scope.distinctPrimes block
  bonnafeIdentity := source.bonnafeIdentity
  identitySeriesUnipotent := source.identitySeriesUnipotent
  highRankUnipotent := source.highRankUnipotent
  splitLowRank := fun parameter hcase block _hstrict ↦
    (source.splitLowRank parameter hcase).blockWitness block
  sp6AtThree := fun hcase block _hstrict ↦
    (source.sp6AtThree hcase).blockWitness block
  sp6AtFive := fun hcase block _hstrict ↦
    (source.sp6AtFive hcase).blockWitness block
  sp6AtSeven := fun hcase block _hstrict ↦
    (source.sp6AtSeven hcase).blockWitness block
  suzuki := fun parameter hcase block _hstrict ↦
    (source.suzuki parameter hcase).blockWitness scope.distinctPrimes block

/-- Combine Hypothesis 5.5(b) over every member of the full relative
`H_G` carrier.

The proof invokes the existing exhaustive case theorem separately for each
`pair : FullHG scope`.  Its conclusion is exactly the fixed strict-block
carrier expected by the FLZ 5.7 gate; it is not a BAW-good or iBAW endpoint
for the ambient group. -/
theorem fullHG_strictBlocks_of_proposition39 {ell : ℕ}
    {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    (blockSource : FullHGBlockSource coverage)
    (strictSource : FullHGStrictQuasiIsolationAdapter coverage)
    (classification : FullHGTypeCClassificationSource scope)
    (strictData : ∀ pair : FullHG scope,
      PairStrictBlockSource strictSource pair)
    (source : ∀ pair : FullHG scope,
      PairSourceInputs blockSource strictSource classification pair
        (strictData pair)) :
    FullHGRelativeHypothesis55StrictBlocks blockSource strictSource where
  iBAWBijection pair block hstrict :=
    strict_block_hypothesis_relative
      (proposition39Data blockSource strictSource classification pair
        (strictData pair) (source pair).IsUnipotent)
      (source pair).toRelative block hstrict

end ModularRep.PaperProofs.EvenFieldProposition39FullHGStrictBlocks


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
