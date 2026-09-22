import ModularRep.Navarro414IntervalCentralCharacterAdapter
import ModularRep.Navarro417DefectSource

/-!
# First-paragraph upper-defect source for Navarro (4.17)

This one-field E1 composite records exactly the upper ambient-defect witness
proved in the first paragraph of Navarro (4.17), using the min direction of
(4.4), Corollary (4.5), the first assertion of (4.14), and the surjective half
of (4.16).  Its target visibly is the block selected from the supplied (4.14)
source.  It gives neither exact defect `P` nor any correspondence conclusion.
-/

namespace ModularRep

open scoped MonoidAlgebra

noncomputable section

local instance navarro417UpperNormalizerFintype
    {G : Type*} [Group G] [Fintype G] {P : Subgroup G} :
    Fintype (defectNormalizer P) :=
  Fintype.ofFinite _

/-- The selected Phase-A block of a local block with the canonical
normalizer-carrier representative has some ambient defect representative
contained in `P`. -/
structure Navarro417FirstParagraphUpperDefectSource
    {p : Nat} {k G LocalBlock AmbientBlock : Type*}
    [Field k] [CharP k p] [IsAlgClosed k]
    [Group G] [Fintype G]
    [Fintype LocalBlock] [Fintype AmbientBlock] [Fact p.Prime]
    (P : Subgroup G) (hP : IsPGroup p P)
    {localBlockIdempotent : LocalBlock → k[defectNormalizer P]}
    {ambientBlockIdempotent : AmbientBlock → k[G]}
    (localBlocks : BlockIdempotentDecomposition localBlockIdempotent)
    (ambientBlocks : BlockIdempotentDecomposition ambientBlockIdempotent)
    (localCatalogue : BlockCentralCharacterCatalogue localBlocks)
    (S414 : Navarro414IntervalCentralCharacterSource
      (normalizerCentralBrauerInterval (p := p) hP)
      localBlocks localCatalogue)
    (ambientCatalogue : BlockCentralCharacterCatalogue ambientBlocks) : Prop where
  localP_selectedInduction_has_ambient_defect_le :
    ∀ b : LocalBlock,
      navarro417LocalHasDefect (p := p) localBlocks b
          (defectSubgroupInNormalizer P) →
      ∃ E : Subgroup G,
        navarro417AmbientHasDefect (p := p) ambientBlocks
            (navarro414InducedBlock S414 ambientCatalogue b) E ∧
          E ≤ P

end

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
