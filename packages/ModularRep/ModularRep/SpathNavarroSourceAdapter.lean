import Mathlib.Algebra.Algebra.ZMod
import Mathlib.RingTheory.Algebraic.Defs
import ModularRep.BlockInduction
import ModularRep.GroupAlgebraClassSums

/-!
# Narrow source provenance for block induction

This sidecar records only the field hypothesis and catalogue provenance that
the local formulations of Navarro's Theorem 3.11 and Späth's Definition 2.1
need.  It deliberately adds no block selector, no definedness theorem, and no
version of Navarro's Theorem 4.14.

The generic kernel construction remains in `BlockInduction`; the aliases
below merely give the source-facing names to its existing central-function,
definedness, and block-induction relation.
-/

namespace ModularRep

open scoped MonoidAlgebra

noncomputable section

/-- The coefficient field provenance used by the cited modular block-theory
sources: the coefficient field is algebraic over its prime field.  This is an
ordinary field of metadata, not an instance. -/
structure SpathCoefficientField
    (p : ℕ) (k : Type*) [Field k] [CharP k p] [IsAlgClosed k]
    (hp : p.Prime) : Prop where
  algebraicOverPrimeField :
    letI : Algebra (ZMod p) k := ZMod.algebra k p
    Algebra.IsAlgebraic (ZMod p) k

/-- Source provenance attaching Navarro's Theorem 3.11 to an already fixed
primitive-block decomposition and its already fixed central character
catalogue.  The only new content is the cited coefficient field hypothesis;
the delta laws and exhaustivity remain the fields of the existing catalogue. -/
structure Navarro311CatalogueProvenance
    (p : ℕ) {k G Block : Type*}
    [Field k] [CharP k p] [IsAlgClosed k]
    [Group G] [Fintype G] [Fintype Block]
    (hp : p.Prime) {blockIdempotent : Block → k[G]}
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (catalogue : BlockCentralCharacterCatalogue blocks) : Prop where
  fieldSource : SpathCoefficientField p k hp

namespace SpathDefinition21

/-- Späth's induced central function is the existing coefficient-restriction
linear map; it is not asserted to be multiplicative here. -/
abbrev centralFunction := @inducedCentralFunction

/-- The source's "defined" condition is the existing multiplicativity
predicate for the induced central function. -/
abbrev IsDefined := @IsBlockInductionDefined

/-- The source-facing block-induction relation.  It is a relation only: this
adapter supplies no ambient-block selector. -/
abbrev InducesTo := @BlockInducesTo

end SpathDefinition21

end

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
