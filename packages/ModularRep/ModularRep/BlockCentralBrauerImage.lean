import ModularRep.BlockDefectGroup
import ModularRep.BlockIdempotentInCenter
import ModularRep.GroupAlgebraCentralBrauerMap

/-!
# Literal block support under the central Brauer restriction

The support predicate below applies the canonical raw centralizer coefficient
restriction to the literal centred block idempotent.  For a supplied p-group
proof it is definitionally the nonzero-image predicate for the genuine
central Brauer algebra map.
-/

namespace ModularRep

open scoped MonoidAlgebra

noncomputable section

variable {p : Nat} {k G Block : Type*}
variable [Field k] [Group G] [Fintype Block]
variable {blockIdempotent : Block → k[G]}

/-- Nonzero raw central Brauer restriction of a literal centred block
idempotent.  This predicate carries no hidden or existential p-group proof. -/
def HasNonzeroCentralBrauerRestriction
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (B : Block) (P : Subgroup G) : Prop :=
  centralBrauerRestriction (k := k) P
    (blocks.blockIdempotentInCenter B) ≠ 0

variable [Finite G] [Fact p.Prime] [CharP k p]

/-- For a supplied p-group proof, raw nonzero restriction is exactly
nonzeroness under the canonical central Brauer algebra map. -/
theorem hasNonzeroCentralBrauerRestriction_iff_map_ne_zero
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (B : Block) (P : Subgroup G) (hP : IsPGroup p P) :
    HasNonzeroCentralBrauerRestriction blocks B P ↔
      centralBrauerMap (k := k) (p := p) P hP
        (blocks.blockIdempotentInCenter B) ≠ 0 :=
  Iff.rfl

/-- The subgroup `D` is maximal, by literal inclusion, in the nonzero central
Brauer support of the supplied block.  This is an intrinsic maximal-support
predicate.  Its identification with the standard published notion of a block
defect group requires the separate E1 Navarro bridge. -/
def IsMaximalCentralBrauerDefect
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (B : Block) (D : Subgroup G) : Prop :=
  IsMaximalNonzeroPSubgroup p
    (HasNonzeroCentralBrauerRestriction blocks B) D

end

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
