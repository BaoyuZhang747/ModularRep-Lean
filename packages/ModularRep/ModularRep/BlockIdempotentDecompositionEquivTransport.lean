import ModularRep.BlockIdempotentDecomposition

/-!
# Transport of block-idempotent decompositions along equivalences

This file contains only the formal transport of a complete primitive
central-idempotent decomposition through a ring equivalence and, in
particular, through an equivalence of the underlying groups. It does not use
block induction or any manuscript-specific source input.
-/

open scoped MonoidAlgebra

namespace ModularRep.BlockIdempotentDecomposition

/-- Transport a complete primitive central-idempotent decomposition through
a ring equivalence. -/
theorem mapRingEquiv
    {A A' Block : Type*} [Ring A] [Ring A'] [Fintype Block]
    {blockIdempotent : Block → A}
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (sigma : A ≃+* A') :
    BlockIdempotentDecomposition
      (fun B ↦ sigma (blockIdempotent B)) where
  complete := {
    idem := fun B =>
      ((blocks.primitive B).mapRingEquiv sigma).idempotent
    ortho := by
      intro B C hBC
      calc
        sigma (blockIdempotent B) * sigma (blockIdempotent C) =
            sigma (blockIdempotent B * blockIdempotent C) :=
          (sigma.map_mul _ _).symm
        _ = sigma 0 := congrArg sigma (blocks.complete.ortho hBC)
        _ = 0 := sigma.map_zero
    complete := by
      rw [← map_sum, blocks.complete.complete, map_one]
    central := fun B =>
      ((blocks.primitive B).mapRingEquiv sigma).central }
  primitive := fun B => (blocks.primitive B).mapRingEquiv sigma

/-- Transport a block-idempotent decomposition along an equivalence of the
underlying groups. -/
theorem alongMulEquiv
    {k G G' Block : Type*}
    [Field k] [Group G] [Group G'] [Fintype Block]
    {blockIdempotent : Block → k[G]}
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (e : G ≃* G') :
    BlockIdempotentDecomposition
      (fun B ↦ MonoidAlgebra.domCongr k k e (blockIdempotent B)) :=
  blocks.mapRingEquiv (MonoidAlgebra.domCongr k k e).toRingEquiv

end ModularRep.BlockIdempotentDecomposition


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
