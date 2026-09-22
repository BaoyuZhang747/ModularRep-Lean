import ModularRep.Navarro417DefectSource

/-!
# Local defect sources used in Navarro (4.17)

This file separates standard existence of a local defect representative from
the p-core containment of Navarro (4.8).  Each external authority is a
one-field Prop-valued source.  Neither source mentions an ambient block,
block induction, the canonical copy of `P`, or an exact-defect conclusion.
-/

namespace ModularRep

open scoped MonoidAlgebra

/-- Standard existence of a defect representative for each local block.
This is an E1 foundation input and is not supplied by Navarro (4.11). -/
structure Navarro417LocalDefectExistenceSource
    {p : Nat} {k G LocalBlock : Type*}
    [Field k] [CharP k p] [IsAlgClosed k]
    [Group G] [Fintype G] [Fintype LocalBlock] [Fact p.Prime]
    (P : Subgroup G)
    {localBlockIdempotent : LocalBlock → k[defectNormalizer P]}
    (localBlocks : BlockIdempotentDecomposition localBlockIdempotent) : Prop where
  exists_representative :
    ∀ b : LocalBlock, ∃ D : Subgroup (defectNormalizer P),
      navarro417LocalHasDefect (p := p) localBlocks b D

/-- Navarro (4.8) in its literal direction `O_p(N_G(P)) ≤ D`. -/
structure Navarro408PCoreDefectSource
    {p : Nat} {k G LocalBlock : Type*}
    [Field k] [CharP k p] [IsAlgClosed k]
    [Group G] [Fintype G] [Fintype LocalBlock] [Fact p.Prime]
    (P : Subgroup G)
    {localBlockIdempotent : LocalBlock → k[defectNormalizer P]}
    (localBlocks : BlockIdempotentDecomposition localBlockIdempotent) : Prop where
  pCore_le_representative :
    ∀ {b : LocalBlock} {D : Subgroup (defectNormalizer P)},
      navarro417LocalHasDefect (p := p) localBlocks b D →
        pCore p (defectNormalizer P) ≤ D

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
