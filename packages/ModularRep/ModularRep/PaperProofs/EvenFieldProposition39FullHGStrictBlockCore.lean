import ModularRep.PaperProofs.EvenFieldFLZFullHG
import ModularRep.StrictQuasiIsolation

/-!
# Blocks and strict quasi-isolation for even-field Proposition 3.9

This module contains the set of blocks, the literal Definition 3.5 target,
and the source-shaped strict quasi-isolation data shared by the legacy
Proposition 3.9 router and the universe-zero high-rank route.  It contains no
classification dispatcher and no branch conclusion.
-/

noncomputable section

namespace ModularRep.PaperProofs.EvenFieldProposition39FullHGStrictBlocks

open scoped Pointwise
open ModularRep.ManuscriptVerification.StrictQuasiIsolation
open ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
open ModularRep.PaperProofs.EvenFieldFLZFullHG
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions

universe u

/-- The actual set of blocks of one presented member of `FullHG`. -/
abbrev PairBlock {ell : ℕ}
    {scope : FLZFullHGUniverse 2 ell}
    (coverage : FullHGDefinition35Coverage scope)
    (pair : FullHG scope) :=
  (coverage.presentation pair).family.Block

/-- The fixed block conclusion required by Hypothesis 5.5(b).

The automorphism adapter and the modular-character-triple source are those
already fixed by `blockSource`; no second presentation is accepted here. -/
def HasDefinition35IBAW {ell : ℕ}
    {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    (blockSource : FullHGBlockSource coverage)
    (pair : FullHG scope) (block : PairBlock coverage pair) : Prop :=
  Nonempty (Definition35IBAWBijection
    ((coverage.presentation pair).family.problem block)
    (blockSource.automorphisms pair block)
    (blockSource.source pair block))

/-- Source-shaped strict quasi-isolation data for one fixed member of
`FullHG`.

The source predicate is not selectable: `strictLabel` starts from
`strictSource.predicate pair`.  The only semantic objects stored here are
the dual label, its finite and connected centralisers, the proper-Levi
predicate, the two centraliser inclusions, and the implication supplied by
the source definition of strict quasi-isolation. -/
structure PairStrictBlockSource {ell : ℕ}
    {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    (strictSource : FullHGStrictQuasiIsolationAdapter coverage)
    (pair : FullHG scope) where
  Dual : Type u
  [groupDual : Group Dual]
  label : PairBlock coverage pair → Dual
  finiteCentralizer : Dual → Subgroup Dual
  connectedCentralizer : Dual → Subgroup Dual
  IsProperLevi : Set Dual → Prop
  finiteCentralizer_le : ∀ s : Dual,
    finiteCentralizer s ≤ Subgroup.centralizer {s}
  connectedCentralizer_le : ∀ s : Dual,
    connectedCentralizer s ≤ Subgroup.centralizer {s}
  strictLabel : ∀ block : PairBlock coverage pair,
    strictSource.predicate pair block →
      NotContainedInProperLevi
        (((finiteCentralizer (label block) : Set Dual) *
          (connectedCentralizer (label block) : Set Dual)))
        IsProperLevi

attribute [instance] PairStrictBlockSource.groupDual

end ModularRep.PaperProofs.EvenFieldProposition39FullHGStrictBlocks


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
