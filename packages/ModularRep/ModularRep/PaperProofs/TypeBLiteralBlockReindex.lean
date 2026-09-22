import ModularRep.BlockIdempotentDecomposition

/-!
# Literal primitive indexing for Type B block catalogues

A complete finite decomposition already enumerates every primitive block.
Use its proved primitive-block equivalence to retain the same decomposition
on the literal primitive carrier. No external block theorem is introduced.
-/

noncomputable section
set_option autoImplicit false
open scoped BigOperators MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBLiteralBlockReindex

universe u

variable {k X Index : Type u} [Field k] [Group X] [Fintype Index]
  {blockIdempotent : Index → k[X]}

/-- The supplied decomposition enumerates all literal primitive blocks. -/
def literalBlockFintype (D : BlockIdempotentDecomposition blockIdempotent) :
    Fintype {b : k[X] // IsPrimitiveCentralIdempotent b} :=
  Fintype.ofEquiv Index D.primitiveBlockEquiv

/-- Relabelling preserves the complete orthogonal primitive family. -/
theorem literalBlocks
    [Fintype {b : k[X] // IsPrimitiveCentralIdempotent b}]
    (D : BlockIdempotentDecomposition blockIdempotent) :
    BlockIdempotentDecomposition
      (fun b : {b : k[X] // IsPrimitiveCentralIdempotent b} => b.val) where
  complete := {
    idem := fun b => b.property.idempotent
    ortho := by
      intro b c hbc
      let e := D.primitiveBlockEquiv
      have hindex : e.symm b ≠ e.symm c := fun h => hbc (e.symm.injective h)
      have hb : blockIdempotent (e.symm b) = b.val :=
        congrArg (fun x : {b : k[X] // IsPrimitiveCentralIdempotent b} => x.val)
          (e.apply_symm_apply b)
      have hc : blockIdempotent (e.symm c) = c.val :=
        congrArg (fun x : {b : k[X] // IsPrimitiveCentralIdempotent b} => x.val)
          (e.apply_symm_apply c)
      simpa only [hb, hc] using D.complete.ortho hindex
    complete := by
      classical
      calc
        (∑ b : {b : k[X] // IsPrimitiveCentralIdempotent b}, b.val) =
            ∑ i : Index, blockIdempotent i := by
          simpa only [
            BlockIdempotentDecomposition.primitiveBlockEquiv_apply,
            BlockIdempotentDecomposition.primitiveBlockOfIndex_val] using
            (D.primitiveBlockEquiv.sum_comp
              (fun b : {b : k[X] // IsPrimitiveCentralIdempotent b} => b.val)).symm
        _ = 1 := D.complete.complete
    central := fun b => b.property.central }
  primitive := fun b => b.property

end ModularRep.PaperProofs.TypeBLiteralBlockReindex



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
