import ModularRep.CentralBrauerIntervalSupport
import ModularRep.DefectNormalizerSandwich
import ModularRep.Navarro411CentralBrauerAdapter
import ModularRep.Navarro413MappedDefectSource
import ModularRep.Navarro417FirstParagraphUpperDefectSource
import ModularRep.Navarro417LocalDefectSources
import ModularRep.Navarro417RestrictedInjectivity

/-!
# Exact-defect correspondence for Navarro (4.17)

This file derives the literal defect-`P` normalizer correspondence from four
independent defect sources: standard local existence, Navarro (4.8), mapped
Navarro (4.13), and the Phase-A-targeted first-paragraph upper witness.  It
also uses the independent Phase-A source from the first assertion of Navarro
(4.14) and the raw coefficient and class source from Navarro (4.15)--(4.16)
through the preceding support and restricted-injectivity layers.  The forward
and reverse defect sandwiches, coverage, injectivity, and final equivalence
are kernel deductions relative to those six inputs.

No source field in this layer states `PN ≤ D`, exact-defect preservation,
coverage, injectivity, surjectivity, an equivalence, singleton support, or a
block-idempotent image equality.
-/

namespace ModularRep

open scoped MonoidAlgebra

noncomputable section

variable {p : Nat} {k G LocalBlock AmbientBlock : Type*}
variable [Field k] [CharP k p] [IsAlgClosed k]
variable [Group G] [Fintype G]
variable [Fintype LocalBlock] [Fintype AmbientBlock] [Fact p.Prime]
variable {P : Subgroup G}

local instance : Fintype (defectNormalizer P) := Fintype.ofFinite _

variable {localBlockIdempotent :
  LocalBlock → k[defectNormalizer P]}
variable {ambientBlockIdempotent : AmbientBlock → k[G]}

/-- Local blocks with the literal normalizer-carrier defect subgroup `P`. -/
abbrev Navarro417LocalPBlocks
    (P : Subgroup G)
    {localBlockIdempotent : LocalBlock → k[defectNormalizer P]}
    (localBlocks : BlockIdempotentDecomposition localBlockIdempotent) :=
  {b : LocalBlock //
    navarro417LocalHasDefect (p := p) (P := P) localBlocks b
      (defectSubgroupInNormalizer P)}

/-- Ambient blocks with the literal ambient defect subgroup `P`. -/
abbrev Navarro417AmbientPBlocks
    (P : Subgroup G)
    (ambientBlocks : BlockIdempotentDecomposition ambientBlockIdempotent) :=
  {B : AmbientBlock //
    navarro417AmbientHasDefect (p := p) ambientBlocks B P}

/-- The selected induced block of a literal local-`P` block has literal
ambient defect `P`. -/
theorem navarro417PhaseAInductionMap_has_ambientP
    (hP : IsPGroup p P)
    (localBlocks : BlockIdempotentDecomposition localBlockIdempotent)
    (ambientBlocks : BlockIdempotentDecomposition ambientBlockIdempotent)
    (localCatalogue : BlockCentralCharacterCatalogue localBlocks)
    (S414 : Navarro414IntervalCentralCharacterSource
      (normalizerCentralBrauerInterval (p := p) hP)
      localBlocks localCatalogue)
    (ambientCatalogue : BlockCentralCharacterCatalogue ambientBlocks)
    (S413 : Navarro413MappedDefectSource P localBlocks ambientBlocks
      localCatalogue ambientCatalogue)
    (SUpper : Navarro417FirstParagraphUpperDefectSource
      P hP localBlocks ambientBlocks localCatalogue S414 ambientCatalogue)
    (b : LocalBlock)
    (hb : navarro417LocalHasDefect (p := p) (P := P) localBlocks b
      (defectSubgroupInNormalizer P)) :
    navarro417AmbientHasDefect (p := p) ambientBlocks
      (navarro417PhaseAInductionMap hP S414 ambientCatalogue b) P := by
  have hInduces :=
    navarro414InducedBlock_inducesTo S414 ambientCatalogue b
  rcases S413.representative_maps_le_ambient_representative hInduces hb with
    ⟨Eplus, hEplus, hMapPlus⟩
  have hPPlus : P ≤ Eplus := by
    rw [← defectSubgroupInNormalizer_map_subtype P]
    exact hMapPlus
  rcases SUpper.localP_selectedInduction_has_ambient_defect_le b hb with
    ⟨Eminus, hEminus, hMinusP⟩
  have hConjugate : Eplus.AreConjugate Eminus :=
    Navarro411CentralBrauerSource.areConjugate
      hEplus.isPGroup hEminus.isPGroup
      hEplus.support411 hEminus.support411
  have hPEplus : P = Eplus :=
    Subgroup.eq_of_le_of_areConjugate_of_le
      hPPlus hConjugate hMinusP
  cases hPEplus
  exact hEplus

/-- Every local block inducing to a literal ambient-`P` block itself has the
literal normalizer-carrier defect subgroup `P`. -/
theorem navarro417LocalP_of_blockInducesTo_ambientP
    (hP : IsPGroup p P)
    (localBlocks : BlockIdempotentDecomposition localBlockIdempotent)
    (ambientBlocks : BlockIdempotentDecomposition ambientBlockIdempotent)
    (localCatalogue : BlockCentralCharacterCatalogue localBlocks)
    (ambientCatalogue : BlockCentralCharacterCatalogue ambientBlocks)
    (SExists : Navarro417LocalDefectExistenceSource P localBlocks)
    (S408 : Navarro408PCoreDefectSource P localBlocks)
    (S413 : Navarro413MappedDefectSource P localBlocks ambientBlocks
      localCatalogue ambientCatalogue)
    {b : LocalBlock} {B : AmbientBlock}
    (hB : navarro417AmbientHasDefect (p := p) ambientBlocks B P)
    (hInduces :
      BlockInducesTo (defectNormalizer P) localCatalogue ambientCatalogue b B) :
    navarro417LocalHasDefect (p := p) (P := P) localBlocks b
      (defectSubgroupInNormalizer P) := by
  rcases SExists.exists_representative b with ⟨D, hD⟩
  have hPNCore :
      defectSubgroupInNormalizer P ≤ pCore p (defectNormalizer P) :=
    defectSubgroupInNormalizer_le_pCore hP
  have hPND : defectSubgroupInNormalizer P ≤ D :=
    hPNCore.trans (S408.pCore_le_representative hD)
  rcases S413.representative_maps_le_ambient_representative hInduces hD with
    ⟨E, hE, hMapE⟩
  have hConjugate : E.AreConjugate P :=
    Navarro411CentralBrauerSource.areConjugate
      hE.isPGroup hB.isPGroup hE.support411 hB.support411
  have hDPN : D = defectSubgroupInNormalizer P :=
    defectSubgroupInNormalizer_eq_of_le_map_le_conjugate
      hPND hMapE hConjugate
  cases hDPN
  exact hD

/-- The K forward map on the literal exact-defect sectors. -/
noncomputable def navarro417ExactDefectMap
    (hP : IsPGroup p P)
    (localBlocks : BlockIdempotentDecomposition localBlockIdempotent)
    (ambientBlocks : BlockIdempotentDecomposition ambientBlockIdempotent)
    (localCatalogue : BlockCentralCharacterCatalogue localBlocks)
    (S414 : Navarro414IntervalCentralCharacterSource
      (normalizerCentralBrauerInterval (p := p) hP)
      localBlocks localCatalogue)
    (ambientCatalogue : BlockCentralCharacterCatalogue ambientBlocks)
    (S413 : Navarro413MappedDefectSource P localBlocks ambientBlocks
      localCatalogue ambientCatalogue)
    (SUpper : Navarro417FirstParagraphUpperDefectSource
      P hP localBlocks ambientBlocks localCatalogue S414 ambientCatalogue) :
    Navarro417LocalPBlocks P localBlocks →
      Navarro417AmbientPBlocks P ambientBlocks :=
  fun b ↦ ⟨navarro417PhaseAInductionMap hP S414 ambientCatalogue b.1,
    navarro417PhaseAInductionMap_has_ambientP hP localBlocks ambientBlocks
      localCatalogue S414 ambientCatalogue S413 SUpper b.1 b.2⟩

/-- The Phase-A selector is injective on the literal local-`P` sector by the
separately proved range argument.  No defect-transport source is needed. -/
theorem navarro417PhaseAInductionMap_injective_on_localP
    (hP : IsPGroup p P)
    (localBlocks : BlockIdempotentDecomposition localBlockIdempotent)
    (ambientBlocks : BlockIdempotentDecomposition ambientBlockIdempotent)
    (localCatalogue : BlockCentralCharacterCatalogue localBlocks)
    (S414 : Navarro414IntervalCentralCharacterSource
      (normalizerCentralBrauerInterval (p := p) hP)
      localBlocks localCatalogue)
    (ambientCatalogue : BlockCentralCharacterCatalogue ambientBlocks)
    (S415416 : Navarro415416RawClassSource P hP localBlocks
      (navarro417LocalHasDefect (p := p) (P := P) localBlocks)) :
    Function.Injective
      (fun b : Navarro417LocalPBlocks P localBlocks ↦
        navarro417PhaseAInductionMap hP S414 ambientCatalogue b.1) := by
  intro b₁ b₂ hMap
  apply Subtype.ext
  apply navarro417PhaseAInductionMap_eq_imp_eq_of_localP_left
    hP localBlocks (navarro417LocalHasDefect (p := p) (P := P) localBlocks)
      localCatalogue S414 ambientCatalogue S415416 b₁.2
  exact hMap

/-- Every literal ambient-`P` block is hit by the exact-defect forward map. -/
theorem navarro417ExactDefectMap_surjective
    (hP : IsPGroup p P)
    (localBlocks : BlockIdempotentDecomposition localBlockIdempotent)
    (ambientBlocks : BlockIdempotentDecomposition ambientBlockIdempotent)
    (localCatalogue : BlockCentralCharacterCatalogue localBlocks)
    (S414 : Navarro414IntervalCentralCharacterSource
      (normalizerCentralBrauerInterval (p := p) hP)
      localBlocks localCatalogue)
    (ambientCatalogue : BlockCentralCharacterCatalogue ambientBlocks)
    (SExists : Navarro417LocalDefectExistenceSource P localBlocks)
    (S408 : Navarro408PCoreDefectSource P localBlocks)
    (S413 : Navarro413MappedDefectSource P localBlocks ambientBlocks
      localCatalogue ambientCatalogue)
    (SUpper : Navarro417FirstParagraphUpperDefectSource
      P hP localBlocks ambientBlocks localCatalogue S414 ambientCatalogue) :
    Function.Surjective
      (navarro417ExactDefectMap hP localBlocks ambientBlocks localCatalogue
        S414 ambientCatalogue S413 SUpper) := by
  intro B
  have hCentralizerNe :
      centralBrauerMap (k := k) (p := p) P hP
          (ambientBlocks.blockIdempotentInCenter B.1) ≠ 0 :=
    (hasNonzeroCentralBrauerRestriction_iff_map_ne_zero
      (p := p) ambientBlocks B.1 P hP).1
        (Navarro411CentralBrauerSource.nonzero_at_D
          hP B.2.support411)
  have hNormalizerNe :
      normalizerCentralBrauerMap (k := k) (p := p) P hP
          (ambientBlocks.blockIdempotentInCenter B.1) ≠ 0 := by
    change centralBrauerMapTo (k := k) (p := p) P
      (defectNormalizer P) hP
      (Subgroup.centralizer_le_normalizer (P : Set G)) le_rfl
        (ambientBlocks.blockIdempotentInCenter B.1) ≠ 0
    exact (centralBrauerMap_ne_zero_iff_mapTo_ne_zero
      (k := k) (p := p) P (defectNormalizer P) hP
      (Subgroup.centralizer_le_normalizer (P : Set G)) le_rfl
      (ambientBlocks.blockIdempotentInCenter B.1)).1 hCentralizerNe
  have hPrimitiveNe :
      centralBrauerMapToPrimitiveImage P (defectNormalizer P) hP
          (Subgroup.centralizer_le_normalizer (P : Set G)) le_rfl
          (ambientBlocks.primitiveBlockOfIndex B.1) ≠ 0 := by
    intro hZero
    apply hNormalizerNe
    apply Subtype.ext
    change ((normalizerCentralBrauerMap (k := k) (p := p) P hP
        (ambientBlocks.blockIdempotentInCenter B.1) :
        GroupAlgebraCenter k (defectNormalizer P)) :
      k[defectNormalizer P]) = 0
    rw [← navarro417PhaseAPrimitiveImage_eq_normalizerMap
      (k := k) (p := p) hP ambientBlocks B.1, hZero]
  have hSupportNonempty :
      (navarro417PhaseANormalizerSupport hP localBlocks ambientBlocks B.1).Nonempty := by
    simpa only [navarro417PhaseANormalizerSupport] using
      (centralBrauerMapToPrimitiveImage_ne_zero_iff_support_nonempty
        P (defectNormalizer P) hP
        (Subgroup.centralizer_le_normalizer (P : Set G)) le_rfl
        (ambientBlocks.primitiveBlockOfIndex B.1) localBlocks).1 hPrimitiveNe
  rcases hSupportNonempty with ⟨b, hbSupport⟩
  have hTarget :=
    (mem_navarro417PhaseANormalizerSupport_iff_inductionMap_eq
      hP localBlocks ambientBlocks localCatalogue S414 ambientCatalogue
      B.1 b).1 hbSupport
  have hInduces :=
    (blockInducesTo_iff_navarro417PhaseAInductionMap_eq
      hP S414 ambientCatalogue b B.1).2 hTarget
  have hbLocal := navarro417LocalP_of_blockInducesTo_ambientP
    hP localBlocks ambientBlocks localCatalogue ambientCatalogue
      SExists S408 S413 B.2 hInduces
  refine ⟨⟨b, hbLocal⟩, ?_⟩
  apply Subtype.ext
  exact hTarget

/-- The exact-defect forward map is bijective. -/
theorem navarro417ExactDefectMap_bijective
    (hP : IsPGroup p P)
    (localBlocks : BlockIdempotentDecomposition localBlockIdempotent)
    (ambientBlocks : BlockIdempotentDecomposition ambientBlockIdempotent)
    (localCatalogue : BlockCentralCharacterCatalogue localBlocks)
    (S414 : Navarro414IntervalCentralCharacterSource
      (normalizerCentralBrauerInterval (p := p) hP)
      localBlocks localCatalogue)
    (ambientCatalogue : BlockCentralCharacterCatalogue ambientBlocks)
    (S415416 : Navarro415416RawClassSource P hP localBlocks
      (navarro417LocalHasDefect (p := p) (P := P) localBlocks))
    (SExists : Navarro417LocalDefectExistenceSource P localBlocks)
    (S408 : Navarro408PCoreDefectSource P localBlocks)
    (S413 : Navarro413MappedDefectSource P localBlocks ambientBlocks
      localCatalogue ambientCatalogue)
    (SUpper : Navarro417FirstParagraphUpperDefectSource
      P hP localBlocks ambientBlocks localCatalogue S414 ambientCatalogue) :
    Function.Bijective
      (navarro417ExactDefectMap hP localBlocks ambientBlocks localCatalogue
        S414 ambientCatalogue S413 SUpper) := by
  constructor
  · intro b₁ b₂ hMap
    apply navarro417PhaseAInductionMap_injective_on_localP
      hP localBlocks ambientBlocks localCatalogue S414 ambientCatalogue
        S415416
    exact congrArg Subtype.val hMap
  · exact navarro417ExactDefectMap_surjective hP localBlocks ambientBlocks
      localCatalogue S414 ambientCatalogue SExists S408 S413 SUpper

/-- Navarro's exact-defect map `b ↦ b^G`, packaged as an equivalence only
after its kernel injectivity and surjectivity proofs. -/
noncomputable def navarro417ExactDefectEquiv
    (hP : IsPGroup p P)
    (localBlocks : BlockIdempotentDecomposition localBlockIdempotent)
    (ambientBlocks : BlockIdempotentDecomposition ambientBlockIdempotent)
    (localCatalogue : BlockCentralCharacterCatalogue localBlocks)
    (S414 : Navarro414IntervalCentralCharacterSource
      (normalizerCentralBrauerInterval (p := p) hP)
      localBlocks localCatalogue)
    (ambientCatalogue : BlockCentralCharacterCatalogue ambientBlocks)
    (S415416 : Navarro415416RawClassSource P hP localBlocks
      (navarro417LocalHasDefect (p := p) (P := P) localBlocks))
    (SExists : Navarro417LocalDefectExistenceSource P localBlocks)
    (S408 : Navarro408PCoreDefectSource P localBlocks)
    (S413 : Navarro413MappedDefectSource P localBlocks ambientBlocks
      localCatalogue ambientCatalogue)
    (SUpper : Navarro417FirstParagraphUpperDefectSource
      P hP localBlocks ambientBlocks localCatalogue S414 ambientCatalogue) :
    Navarro417LocalPBlocks P localBlocks ≃
      Navarro417AmbientPBlocks P ambientBlocks :=
  Equiv.ofBijective
    (navarro417ExactDefectMap hP localBlocks ambientBlocks localCatalogue
      S414 ambientCatalogue S413 SUpper)
    (navarro417ExactDefectMap_bijective hP localBlocks ambientBlocks
      localCatalogue S414 ambientCatalogue S415416 SExists S408 S413 SUpper)

end

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
