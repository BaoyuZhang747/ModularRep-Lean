import ModularRep.DefectNormalizerCarrier
import ModularRep.Navarro411CentralBrauerSource

/-!
# Defect-representative base for Navarro (4.17)

This file contains only the visible wrapper pairing the published Navarro
(4.11) support criterion with separately supplied p-group evidence for a
nominated literal defect representative, together with its local and ambient
normalizer-carrier abbreviations.

The independent defect-existence, Navarro (4.8), mapped Navarro (4.13), and
first-paragraph upper-defect inputs live in separate one-field source
interfaces.  This base contains no induction, selected block, defect
containment, exact-sector map, correspondence, or idempotent-image assertion.
-/

namespace ModularRep

open scoped MonoidAlgebra

noncomputable section

/-- A nominated literal defect representative: independent p-group evidence
paired with the exact Navarro (4.11) central Brauer support source. -/
structure Navarro411DefectRepresentative
    {p : Nat} {k X Block : Type*}
    [Field k] [CharP k p] [IsAlgClosed k]
    [Group X] [Fintype X] [Fintype Block] [Fact p.Prime]
    {blockIdempotent : Block → k[X]}
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (B : Block) (D : Subgroup X) : Prop where
  isPGroup : IsPGroup p D
  support411 : Navarro411CentralBrauerSource blocks B D

/-- The supplied local block has the displayed literal subgroup of the
normalizer as a Navarro (4.11) defect representative. -/
abbrev navarro417LocalHasDefect
    {p : Nat} {k G LocalBlock : Type*}
    [Field k] [CharP k p] [IsAlgClosed k]
    [Group G] [Fintype G] [Fintype LocalBlock] [Fact p.Prime]
    {P : Subgroup G}
    {localBlockIdempotent : LocalBlock → k[defectNormalizer P]}
    (localBlocks : BlockIdempotentDecomposition localBlockIdempotent)
    (b : LocalBlock) (D : Subgroup (defectNormalizer P)) : Prop :=
  letI : Fintype (defectNormalizer P) := Fintype.ofFinite _
  Navarro411DefectRepresentative localBlocks b D

/-- The supplied ambient block has the displayed literal ambient subgroup as
a Navarro (4.11) defect representative. -/
abbrev navarro417AmbientHasDefect
    {p : Nat} {k G AmbientBlock : Type*}
    [Field k] [CharP k p] [IsAlgClosed k]
    [Group G] [Fintype G] [Fintype AmbientBlock] [Fact p.Prime]
    {ambientBlockIdempotent : AmbientBlock → k[G]}
    (ambientBlocks : BlockIdempotentDecomposition ambientBlockIdempotent)
    (B : AmbientBlock) (D : Subgroup G) : Prop :=
  Navarro411DefectRepresentative ambientBlocks B D

end

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
