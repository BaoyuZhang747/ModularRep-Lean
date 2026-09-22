import ModularRep.CentralBrauerMapToBlockExpansion
import ModularRep.DefectNormalizerCarrier
import ModularRep.Navarro414IntervalCentralCharacterAdapter

/-!
# Phase-A normalizer support for Navarro (4.17)

This file combines the existing one-field Navarro (4.14) Phase-A source with
the kernel block-induction selector and the canonical local expansion of an
interval central Brauer image.  It identifies the support with the fibre of
the selected induction map.

There are no block-defect assumptions, range or nonvanishing claims,
injectivity, singleton-support, correspondence, equivalence, or final local
block-idempotent image conclusions in this layer.
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

/-- The ambient block selected by Phase A at the fixed normalizer endpoint. -/
noncomputable def navarro417PhaseAInductionMap
    (hP : IsPGroup p P)
    {localBlocks : BlockIdempotentDecomposition localBlockIdempotent}
    {ambientBlocks : BlockIdempotentDecomposition ambientBlockIdempotent}
    {localCatalogue : BlockCentralCharacterCatalogue localBlocks}
    (S : Navarro414IntervalCentralCharacterSource
      (normalizerCentralBrauerInterval (p := p) hP)
      localBlocks localCatalogue)
    (ambientCatalogue : BlockCentralCharacterCatalogue ambientBlocks)
    (b : LocalBlock) : AmbientBlock :=
  navarro414InducedBlock S ambientCatalogue b

/-- A local block induces to an ambient block exactly when the Phase-A
selector chooses that ambient block. -/
theorem blockInducesTo_iff_navarro417PhaseAInductionMap_eq
    (hP : IsPGroup p P)
    {localBlocks : BlockIdempotentDecomposition localBlockIdempotent}
    {ambientBlocks : BlockIdempotentDecomposition ambientBlockIdempotent}
    {localCatalogue : BlockCentralCharacterCatalogue localBlocks}
    (S : Navarro414IntervalCentralCharacterSource
      (normalizerCentralBrauerInterval (p := p) hP)
      localBlocks localCatalogue)
    (ambientCatalogue : BlockCentralCharacterCatalogue ambientBlocks)
    (b : LocalBlock) (B : AmbientBlock) :
    BlockInducesTo (defectNormalizer P) localCatalogue ambientCatalogue b B ↔
      navarro417PhaseAInductionMap hP S ambientCatalogue b = B := by
  change BlockInducesTo (defectNormalizer P) localCatalogue
      ambientCatalogue b B ↔
    navarro414InducedBlock S ambientCatalogue b = B
  constructor
  · intro hB
    exact (eq_inducedBlock_of_blockInducesTo
      (defectNormalizer P) localCatalogue ambientCatalogue b
      (S.isBlockInductionDefined b) hB).symm
  · intro hB
    rw [← hB]
    exact navarro414InducedBlock_inducesTo S ambientCatalogue b

/-- The canonical local primitive support of the normalizer central Brauer
image of one indexed ambient block. -/
noncomputable def navarro417PhaseANormalizerSupport
    (hP : IsPGroup p P)
    (localBlocks : BlockIdempotentDecomposition localBlockIdempotent)
    (ambientBlocks : BlockIdempotentDecomposition ambientBlockIdempotent)
    (B : AmbientBlock) : Finset LocalBlock :=
  centralBrauerMapToLocalSupport P (defectNormalizer P) hP
    (Subgroup.centralizer_le_normalizer (P : Set G)) le_rfl
    (ambientBlocks.primitiveBlockOfIndex B) localBlocks

set_option linter.unusedFintypeInType false in
omit [IsAlgClosed k] in
/-- For an indexed ambient block, the raw primitive-image construction is
definitionally the underlying carrier value of the canonical normalizer
central Brauer map.  This is only a carrier bridge, not a local-block
idempotent-image conclusion. -/
theorem navarro417PhaseAPrimitiveImage_eq_normalizerMap
    (hP : IsPGroup p P)
    (ambientBlocks : BlockIdempotentDecomposition ambientBlockIdempotent)
    (B : AmbientBlock) :
    centralBrauerMapToPrimitiveImage P (defectNormalizer P) hP
        (Subgroup.centralizer_le_normalizer (P : Set G)) le_rfl
        (ambientBlocks.primitiveBlockOfIndex B) =
      ((normalizerCentralBrauerMap (k := k) (p := p) P hP
          (ambientBlocks.blockIdempotentInCenter B) :
          GroupAlgebraCenter k (defectNormalizer P)) :
        k[defectNormalizer P]) := by
  rfl

/-- The canonical normalizer support contains a local block exactly when its
central character evaluates to one on the image. -/
theorem mem_navarro417PhaseANormalizerSupport_iff_character_eq_one
    (hP : IsPGroup p P)
    (localBlocks : BlockIdempotentDecomposition localBlockIdempotent)
    (ambientBlocks : BlockIdempotentDecomposition ambientBlockIdempotent)
    (localCatalogue : BlockCentralCharacterCatalogue localBlocks)
    (B : AmbientBlock) (C : LocalBlock) :
    C ∈ navarro417PhaseANormalizerSupport hP localBlocks ambientBlocks B ↔
      localCatalogue.centralCharacter C
        (normalizerCentralBrauerMap (k := k) (p := p) P hP
          (ambientBlocks.blockIdempotentInCenter B)) = 1 := by
  constructor
  · intro hC
    have hC' :
        C ∈ centralBrauerMapToLocalSupport P (defectNormalizer P) hP
          (Subgroup.centralizer_le_normalizer (P : Set G)) le_rfl
          (ambientBlocks.primitiveBlockOfIndex B) localBlocks := by
      simpa only [navarro417PhaseANormalizerSupport] using hC
    have hMulRaw :=
      (mem_centralBrauerMapToLocalSupport_iff_mul_eq_self
        P (defectNormalizer P) hP
        (Subgroup.centralizer_le_normalizer (P : Set G)) le_rfl
        (ambientBlocks.primitiveBlockOfIndex B) localBlocks C).1 hC'
    have hMulCenter :
        localBlocks.blockIdempotentInCenter C *
            normalizerCentralBrauerMap (k := k) (p := p) P hP
              (ambientBlocks.blockIdempotentInCenter B) =
          localBlocks.blockIdempotentInCenter C := by
      apply Subtype.ext
      change localBlockIdempotent C *
          ((normalizerCentralBrauerMap (k := k) (p := p) P hP
              (ambientBlocks.blockIdempotentInCenter B) :
              GroupAlgebraCenter k (defectNormalizer P)) :
            k[defectNormalizer P]) = localBlockIdempotent C
      rw [← navarro417PhaseAPrimitiveImage_eq_normalizerMap
        (k := k) (p := p) hP ambientBlocks B]
      exact hMulRaw
    have hEval := congrArg (localCatalogue.centralCharacter C) hMulCenter
    simpa using hEval
  · intro hValue
    by_contra hNotMem
    have hMulRawZero :
        localBlockIdempotent C *
            centralBrauerMapToPrimitiveImage P (defectNormalizer P) hP
              (Subgroup.centralizer_le_normalizer (P : Set G)) le_rfl
              (ambientBlocks.primitiveBlockOfIndex B) = 0 := by
      by_contra hNe
      apply hNotMem
      change C ∈ centralBrauerMapToLocalSupport P (defectNormalizer P) hP
        (Subgroup.centralizer_le_normalizer (P : Set G)) le_rfl
        (ambientBlocks.primitiveBlockOfIndex B) localBlocks
      exact (mem_centralBrauerMapToLocalSupport
        P (defectNormalizer P) hP
        (Subgroup.centralizer_le_normalizer (P : Set G)) le_rfl
        (ambientBlocks.primitiveBlockOfIndex B) localBlocks C).2 hNe
    have hMulCenterZero :
        localBlocks.blockIdempotentInCenter C *
            normalizerCentralBrauerMap (k := k) (p := p) P hP
              (ambientBlocks.blockIdempotentInCenter B) = 0 := by
      apply Subtype.ext
      change localBlockIdempotent C *
          ((normalizerCentralBrauerMap (k := k) (p := p) P hP
              (ambientBlocks.blockIdempotentInCenter B) :
              GroupAlgebraCenter k (defectNormalizer P)) :
            k[defectNormalizer P]) = 0
      rw [← navarro417PhaseAPrimitiveImage_eq_normalizerMap
        (k := k) (p := p) hP ambientBlocks B]
      exact hMulRawZero
    have hEval := congrArg (localCatalogue.centralCharacter C) hMulCenterZero
    have hImpossible : (1 : k) = 0 := by
      simp [hValue] at hEval
    exact one_ne_zero hImpossible

private theorem navarro417PhaseACentralCharacter_apply
    (hP : IsPGroup p P)
    {localBlocks : BlockIdempotentDecomposition localBlockIdempotent}
    {ambientBlocks : BlockIdempotentDecomposition ambientBlockIdempotent}
    {localCatalogue : BlockCentralCharacterCatalogue localBlocks}
    (S : Navarro414IntervalCentralCharacterSource
      (normalizerCentralBrauerInterval (p := p) hP)
      localBlocks localCatalogue)
    (ambientCatalogue : BlockCentralCharacterCatalogue ambientBlocks)
    (B : AmbientBlock) (C : LocalBlock) :
    ambientCatalogue.centralCharacter
        (navarro417PhaseAInductionMap hP S ambientCatalogue C)
        (ambientBlocks.blockIdempotentInCenter B) =
      localCatalogue.centralCharacter C
        (normalizerCentralBrauerMap (k := k) (p := p) P hP
          (ambientBlocks.blockIdempotentInCenter B)) := by
  have hCharacter := congrArg
    (fun lambda : GroupAlgebraCenter k G →ₐ[k] k ↦
      lambda (ambientBlocks.blockIdempotentInCenter B))
    (navarro414InducedBlock_centralCharacter S ambientCatalogue C)
  change ambientCatalogue.centralCharacter
      (navarro417PhaseAInductionMap hP S ambientCatalogue C)
        (ambientBlocks.blockIdempotentInCenter B) =
    localCatalogue.centralCharacter C
      (normalizerCentralBrauerMap (k := k) (p := p) P hP
        (ambientBlocks.blockIdempotentInCenter B))
  exact hCharacter

/-- The canonical normalizer support is exactly the fibre of the Phase-A
selected induction map. -/
theorem mem_navarro417PhaseANormalizerSupport_iff_inductionMap_eq
    (hP : IsPGroup p P)
    (localBlocks : BlockIdempotentDecomposition localBlockIdempotent)
    (ambientBlocks : BlockIdempotentDecomposition ambientBlockIdempotent)
    (localCatalogue : BlockCentralCharacterCatalogue localBlocks)
    (S : Navarro414IntervalCentralCharacterSource
      (normalizerCentralBrauerInterval (p := p) hP)
      localBlocks localCatalogue)
    (ambientCatalogue : BlockCentralCharacterCatalogue ambientBlocks)
    (B : AmbientBlock) (C : LocalBlock) :
    C ∈ navarro417PhaseANormalizerSupport hP localBlocks ambientBlocks B ↔
      navarro417PhaseAInductionMap hP S ambientCatalogue C = B := by
  constructor
  · intro hC
    have hValue :=
      (mem_navarro417PhaseANormalizerSupport_iff_character_eq_one
        hP localBlocks ambientBlocks localCatalogue B C).1 hC
    by_contra hNe
    have hEval := navarro417PhaseACentralCharacter_apply
      hP S ambientCatalogue B C
    have hOne :
        ambientCatalogue.centralCharacter
            (navarro417PhaseAInductionMap hP S ambientCatalogue C)
            (ambientBlocks.blockIdempotentInCenter B) = 1 :=
      hEval.trans hValue
    have hZero := ambientCatalogue.centralCharacter_other hNe
    exact one_ne_zero (hOne.symm.trans hZero)
  · intro hTarget
    apply (mem_navarro417PhaseANormalizerSupport_iff_character_eq_one
      hP localBlocks ambientBlocks localCatalogue B C).2
    have hEval := navarro417PhaseACentralCharacter_apply
      hP S ambientCatalogue B C
    calc
      localCatalogue.centralCharacter C
          (normalizerCentralBrauerMap (k := k) (p := p) P hP
            (ambientBlocks.blockIdempotentInCenter B)) =
        ambientCatalogue.centralCharacter
          (navarro417PhaseAInductionMap hP S ambientCatalogue C)
          (ambientBlocks.blockIdempotentInCenter B) := hEval.symm
      _ = ambientCatalogue.centralCharacter B
          (ambientBlocks.blockIdempotentInCenter B) := by rw [hTarget]
      _ = 1 := ambientCatalogue.centralCharacter_own B

end

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
