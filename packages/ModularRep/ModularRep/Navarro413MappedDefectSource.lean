import ModularRep.BlockInduction
import ModularRep.Navarro417DefectSource

/-!
# Mapped defect transport from Navarro (4.13)

This one-field E1 source records only the local-to-ambient containment from
Navarro (4.13).  A subgroup of the normalizer is compared with an ambient
subgroup only after mapping it along the normalizer subtype.  The source gives
no containment in the reverse direction and no exact-defect or correspondence
conclusion.
-/

namespace ModularRep

open scoped MonoidAlgebra

noncomputable section

local instance navarro413MappedNormalizerFintype
    {G : Type*} [Group G] [Fintype G] {P : Subgroup G} :
    Fintype (defectNormalizer P) :=
  Fintype.ofFinite _

/-- Navarro (4.13), with the local defect representative explicitly mapped
into the ambient group. -/
structure Navarro413MappedDefectSource
    {p : Nat} {k G LocalBlock AmbientBlock : Type*}
    [Field k] [CharP k p] [IsAlgClosed k]
    [Group G] [Fintype G]
    [Fintype LocalBlock] [Fintype AmbientBlock] [Fact p.Prime]
    (P : Subgroup G)
    {localBlockIdempotent : LocalBlock → k[defectNormalizer P]}
    {ambientBlockIdempotent : AmbientBlock → k[G]}
    (localBlocks : BlockIdempotentDecomposition localBlockIdempotent)
    (ambientBlocks : BlockIdempotentDecomposition ambientBlockIdempotent)
    (localCatalogue : BlockCentralCharacterCatalogue localBlocks)
    (ambientCatalogue : BlockCentralCharacterCatalogue ambientBlocks) : Prop where
  representative_maps_le_ambient_representative :
    ∀ {b : LocalBlock} {B : AmbientBlock}
      {D : Subgroup (defectNormalizer P)},
      BlockInducesTo (defectNormalizer P)
          localCatalogue ambientCatalogue b B →
      navarro417LocalHasDefect (p := p) localBlocks b D →
      ∃ E : Subgroup G,
        navarro417AmbientHasDefect (p := p) ambientBlocks B E ∧
          D.map (defectNormalizer P).subtype ≤ E

end

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
