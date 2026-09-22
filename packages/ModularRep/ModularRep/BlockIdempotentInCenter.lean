import ModularRep.BlockIdempotentDecomposition
import ModularRep.GroupAlgebraCentralFunctions

/-!
# Block idempotents in the group algebra centre

This file provides the low-level bridge from a complete decomposition by
primitive central idempotents to literal elements of the group algebra centre.
It is independent of block central characters and block induction.
-/

namespace ModularRep

open scoped MonoidAlgebra

noncomputable section

namespace BlockIdempotentDecomposition

variable {k G Block : Type*} [Field k] [Group G] [Fintype Block]
variable {blockIdempotent : Block → k[G]}

/-- A block idempotent regarded as an element of the centre of the group
algebra. -/
def blockIdempotentInCenter
    (blocks : BlockIdempotentDecomposition blockIdempotent) (B : Block) :
    GroupAlgebraCenter k G :=
  ⟨blockIdempotent B, by
    rw [Subalgebra.mem_center_iff]
    intro x
    exact ((blocks.complete.central B).comm x).eq.symm⟩

/-- Coercing a centred block idempotent back to the group algebra recovers
the member of the original block decomposition. -/
@[simp]
theorem blockIdempotentInCenter_coe
    (blocks : BlockIdempotentDecomposition blockIdempotent) (B : Block) :
    (blocks.blockIdempotentInCenter B : k[G]) = blockIdempotent B :=
  rfl

end BlockIdempotentDecomposition

end

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
