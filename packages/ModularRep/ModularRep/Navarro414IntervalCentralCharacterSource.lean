import ModularRep.BlockInduction
import ModularRep.CentralBrauerInterval
import ModularRep.GroupAlgebraCentralBrauerMapTo

/-!
# Navarro (4.14) interval central character source

This file records only the first central-function equality in Navarro's
Theorem (4.14).  It supplies no induced block, idempotent formula, coverage
statement, defect comparison, or First Main Theorem.
-/

namespace ModularRep

open scoped MonoidAlgebra

noncomputable section

variable {p : Nat} {k G LocalBlock : Type*}
variable [Field k] [CharP k p] [IsAlgClosed k]
variable [Group G] [Fintype G] [Fintype LocalBlock] [Fact p.Prime]
variable {P H : Subgroup G}

local instance navarro414IntervalCentralCharacterSourceHFintype : Fintype H :=
  Fintype.ofFinite H

variable {localBlockIdempotent : LocalBlock → k[H]}

/-- The exact Navarro (4.14) equality for every block in a supplied local
catalogue.  This is a one-field E1 source interface. -/
structure Navarro414IntervalCentralCharacterSource
    (I : CentralBrauerInterval (p := p) P H)
    (localBlocks : BlockIdempotentDecomposition localBlockIdempotent)
    (localCatalogue : BlockCentralCharacterCatalogue localBlocks) : Prop where
  inducedCentralFunction_eq_intervalBrauer :
    ∀ b : LocalBlock,
      inducedCentralFunction H (localCatalogue.centralCharacter b) =
        ((localCatalogue.centralCharacter b).comp
          (centralBrauerMapTo (k := k) (p := p) P H
            I.isPGroup I.centralizer_le I.le_normalizer)).toLinearMap

end

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
