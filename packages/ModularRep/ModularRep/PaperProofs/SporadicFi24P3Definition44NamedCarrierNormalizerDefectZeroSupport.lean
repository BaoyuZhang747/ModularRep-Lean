import ModularRep.Navarro417LocalDefectSources
import ModularRep.Navarro413MappedDefectSource

/-! A normalizer block inducing to a block with trivial maximal Brauer
support can only arise from the trivial p-subgroup. The three standard
defect principles remain independent E1 inputs. No character, weight,
correspondence, or cardinality assertion is assumed here. -/

noncomputable section
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierNormalizerDefectZeroSupport
open ModularRep

local instance normalizerFintype {G : Type*} [Group G] [Fintype G]
    {P : Subgroup G} : Fintype (defectNormalizer P) := Fintype.ofFinite _

theorem subgroup_eq_bot_of_induces_to_trivial_defect
    {p : Nat} {k G LocalBlock AmbientBlock : Type*}
    [Field k] [CharP k p] [IsAlgClosed k] [Group G] [Fintype G]
    [Fintype LocalBlock] [Fintype AmbientBlock] [Fact p.Prime]
    (P : Subgroup G) (hP : IsPGroup p P)
    {localIdempotent : LocalBlock → k[defectNormalizer P]}
    {ambientIdempotent : AmbientBlock → k[G]}
    (localBlocks : BlockIdempotentDecomposition localIdempotent)
    (ambientBlocks : BlockIdempotentDecomposition ambientIdempotent)
    (localCatalogue : BlockCentralCharacterCatalogue localBlocks)
    (ambientCatalogue : BlockCentralCharacterCatalogue ambientBlocks)
    (SExists : Navarro417LocalDefectExistenceSource (p := p) P localBlocks)
    (S408 : Navarro408PCoreDefectSource (p := p) P localBlocks)
    (S413 : Navarro413MappedDefectSource (p := p) P localBlocks ambientBlocks
      localCatalogue ambientCatalogue)
    (b : LocalBlock) (B : AmbientBlock)
    (hInduces : BlockInducesTo (defectNormalizer P) localCatalogue ambientCatalogue b B)
    (hZero : IsMaximalCentralBrauerDefect (p := p) ambientBlocks B (⊥ : Subgroup G)) :
    P = ⊥ := by
  rcases SExists.exists_representative b with ⟨D, hD⟩
  have hPND : defectSubgroupInNormalizer P ≤ D :=
    (defectSubgroupInNormalizer_le_pCore hP).trans (S408.pCore_le_representative hD)
  have hPmap : P ≤ D.map (defectNormalizer P).subtype := by
    calc
      P = (defectSubgroupInNormalizer P).map (defectNormalizer P).subtype :=
        (defectSubgroupInNormalizer_map_subtype P).symm
      _ ≤ D.map (defectNormalizer P).subtype := Subgroup.map_mono hPND
  rcases S413.representative_maps_le_ambient_representative hInduces hD with
    ⟨E, hE, hDE⟩
  have hEbot : E = ⊥ :=
    (hZero.eq_of_nonzero_le E hE.isPGroup
      ((hE.support411.nonzero_iff_isSubconjugate E hE.isPGroup).mpr
        (Subgroup.IsSubconjugate.refl E)) bot_le).symm
  exact bot_unique ((hPmap.trans hDE).trans hEbot.le)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierNormalizerDefectZeroSupport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
