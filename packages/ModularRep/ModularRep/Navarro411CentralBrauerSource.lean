import ModularRep.BlockCentralBrauerImage

/-!
# Navarro (4.11) central Brauer support source

This file records, without proving, the exact external block-theoretic input
from Navarro (4.11): among p-subgroups, nonzero central Brauer restriction of
the supplied literal block idempotent is equivalent to subconjugacy into the
nominated subgroup.  The record asserts neither existence nor uniqueness of
a defect group.
-/

namespace ModularRep

open scoped MonoidAlgebra

/-- The exact Navarro (4.11) support criterion for one supplied literal block
and one nominated subgroup.  This is an E1 source interface.  It does not
supply `IsPGroup p D`; clients must provide that independently. -/
structure Navarro411CentralBrauerSource
    {p : Nat} {k G Block : Type*}
    [Field k] [CharP k p] [IsAlgClosed k]
    [Group G] [Fintype G] [Fintype Block] [Fact p.Prime]
    {blockIdempotent : Block → k[G]}
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (B : Block) (D : Subgroup G) : Prop where
  nonzero_iff_isSubconjugate :
    ∀ Q : Subgroup G, IsPGroup p Q →
      (HasNonzeroCentralBrauerRestriction blocks B Q ↔
        Q.IsSubconjugate D)

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
