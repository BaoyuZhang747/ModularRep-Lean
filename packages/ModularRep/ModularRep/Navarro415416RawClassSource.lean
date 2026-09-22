import Mathlib.Algebra.Group.ConjFinite
import ModularRep.BlockDefectGroup
import ModularRep.BlockIdempotentDecomposition

/-!
# Raw class-intersection source for Navarro (4.15)--(4.16)

This is the coefficient-support use-direction composite of Navarro (4.15)
and the surjectivity direction of (4.16).  It is not a verbatim
formalisation of either result and supplies neither the injective half of
(4.16), a central-element preimage, nor a block correspondence.
-/

namespace ModularRep

open scoped MonoidAlgebra

/-- The exact raw E1 input needed to lift the nonzero class coefficients of
a local block idempotent to global classes with the prescribed literal
centralizer intersection. -/
structure Navarro415416RawClassSource
    {p : Nat} {k G LocalBlock : Type*}
    [Field k] [CharP k p] [IsAlgClosed k]
    [Group G] [Fintype G] [Fintype LocalBlock] [Fact p.Prime]
    (P : Subgroup G) (hP : IsPGroup p P)
    {localBlockIdempotent :
      LocalBlock → k[defectNormalizer P]}
    (localBlocks : BlockIdempotentDecomposition localBlockIdempotent)
    (localHasDefect :
      LocalBlock → Subgroup (defectNormalizer P) → Prop) : Prop where
  localP_nonzero_coeff_has_global_intersection :
    ∀ (b : LocalBlock),
      localHasDefect b (defectSubgroupInNormalizer P) →
      ∀ ell : defectNormalizer P,
        ((localBlocks.primitiveBlockOfIndex b).1 :
            k[defectNormalizer P]).coeff ell ≠ 0 →
        ∃ g : G, ∀ x : defectNormalizer P,
          x ∈ (ConjClasses.mk ell).carrier ↔
            ((x : G) ∈ (ConjClasses.mk g).carrier ∧
              (x : G) ∈ Subgroup.centralizer (P : Set G))

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
