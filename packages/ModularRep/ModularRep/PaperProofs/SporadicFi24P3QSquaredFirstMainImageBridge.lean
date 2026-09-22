import ModularRep.Navarro417ExactDefectAdapter
import ModularRep.Navarro417RestrictedInjectivity
import ModularRep.PaperProofs.SporadicFi24P3QSquaredAmbientUniqueness

/-!
# First Main image for the generic `Fi'_{24}` `Q = 3^2` packet

This module connects the already aligned literal normaliser block to the
named nonprincipal ambient block.  The forward half of the split Navarro
(4.17) construction first gives exact ambient defect `Q` for the block
selected in Phase A.  The two independent ambient exclusions then identify
that selected block with the nonprincipal block.  The Phase-A selector
equivalence gives block induction as a kernel consequence.

The final central Brauer idempotent formula is kept separate.  It additionally
requires the raw Navarro (4.15)--(4.16) class-sum source used by restricted
injectivity.  That source is not needed for the image equality or for block
induction.

All declarations remain generic in `X`, `Q`, and the literal operations.  No
concrete Fischer carrier, transcript row, table-position match, four-row
coverage, outer action, cancellation, BAW, or iBAW assertion is introduced.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3QSquaredFirstMainImageBridge

open scoped MonoidAlgebra

open ModularRep
open ModularRep.CharacterWeight
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual
open ModularRep.PaperProofs.SporadicFi24P3QSquaredCarrierAlignment

universe u

variable {k K X : Type u}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

local instance primeThreeFact : Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

local instance fi24QSquaredFirstMainImageBridgeNormalizerFintype
    {Q : Subgroup X} : Fintype (defectNormalizer Q) :=
  Fintype.ofFinite _

/-! ## Source-type abbreviations on the common literal carrier -/

/-- The Navarro (4.14) source for the fixed-`Q` normaliser catalogue. -/
abbrev PhaseASource
    (R : LiteralCarrierAdapter
      (p := 3) (k := k) (K := K) (X := X))
    (Q : Subgroup X)
    (table :
      SporadicFi24P3QSquaredLocalTableSource.Source Q
        (R.1.operations.toLocalNormalizerBlockOperations Q)) : Prop :=
  let O := R.1.operations
  let localData := O.inflatedNormalizerBlockData Q
  letI : Fintype (InflatedNormalizerBlock (k := k) Q) :=
    localData.fintypeBlock
  Navarro414IntervalCentralCharacterSource
    (normalizerCentralBrauerInterval (p := 3)
      table.q_radical.isPGroup)
    localData.blocks localData.catalogue

/-- The mapped Navarro (4.13) source on the common local and ambient
catalogues. -/
abbrev MappedDefectSource
    (R : LiteralCarrierAdapter
      (p := 3) (k := k) (K := K) (X := X))
    (Q : Subgroup X) : Prop :=
  let O := R.1.operations
  let localData := O.inflatedNormalizerBlockData Q
  letI : Fintype (InflatedNormalizerBlock (k := k) Q) :=
    localData.fintypeBlock
  letI : Fintype (ActualBlock (k := k) (X := X)) :=
    O.ambientBlockData.fintypeBlock
  Navarro413MappedDefectSource Q localData.blocks
    O.ambientBlockData.blocks localData.catalogue
      O.ambientBlockData.catalogue

/-- The first-paragraph upper-defect source for the block selected by the
supplied Navarro (4.14) source. -/
abbrev UpperDefectSource
    (R : LiteralCarrierAdapter
      (p := 3) (k := k) (K := K) (X := X))
    (Q : Subgroup X)
    (table :
      SporadicFi24P3QSquaredLocalTableSource.Source Q
        (R.1.operations.toLocalNormalizerBlockOperations Q))
    (S414 : PhaseASource R Q table) : Prop :=
  let O := R.1.operations
  let localData := O.inflatedNormalizerBlockData Q
  letI : Fintype (InflatedNormalizerBlock (k := k) Q) :=
    localData.fintypeBlock
  letI : Fintype (ActualBlock (k := k) (X := X)) :=
    O.ambientBlockData.fintypeBlock
  Navarro417FirstParagraphUpperDefectSource Q table.q_radical.isPGroup
    localData.blocks
    O.ambientBlockData.blocks localData.catalogue S414
      O.ambientBlockData.catalogue

/-- The independent raw Navarro (4.15)--(4.16) source needed only for the
central Brauer idempotent formula. -/
abbrev RawClassSource
    (R : LiteralCarrierAdapter
      (p := 3) (k := k) (K := K) (X := X))
    (Q : Subgroup X)
    (table :
      SporadicFi24P3QSquaredLocalTableSource.Source Q
        (R.1.operations.toLocalNormalizerBlockOperations Q)) : Prop :=
  let O := R.1.operations
  let localData := O.inflatedNormalizerBlockData Q
  letI : Fintype (InflatedNormalizerBlock (k := k) Q) :=
    localData.fintypeBlock
  Navarro415416RawClassSource Q table.q_radical.isPGroup localData.blocks
    (navarro417LocalHasDefect (p := 3) (P := Q) localData.blocks)

/-! ## Kernel consequences -/

/-- The Phase-A image of the table normaliser block is the named nonprincipal
ambient block.  The sole local premise is Navarro (4.11) support; exact local
defect follows from it and the radicality already stored by `table`.  The image
is then identified by the split forward theorem and the two independent
exact-`Q` exclusions. -/
theorem phaseAInductionMap_tableNormalizerBlock_eq_nonprincipal
    (R : LiteralCarrierAdapter
      (p := 3) (k := k) (K := K) (X := X))
    (three : Fi24ThreeBlockSource (k := k) (X := X))
    (Q : Subgroup X)
    (table :
      SporadicFi24P3QSquaredLocalTableSource.Source Q
        (R.1.operations.toLocalNormalizerBlockOperations Q))
    (hLocalSupport : LocalSupport411 R Q table.normalizerBlock)
    (U : SporadicFi24P3QSquaredAmbientUniqueness.Source R three Q)
    (S414 : PhaseASource R Q table)
    (S413 : MappedDefectSource R Q)
    (SUpper : UpperDefectSource R Q table S414) :
    let O := R.1.operations
    let localData := O.inflatedNormalizerBlockData Q
    letI : Fintype (InflatedNormalizerBlock (k := k) Q) :=
      localData.fintypeBlock
    letI : Fintype (ActualBlock (k := k) (X := X)) :=
      O.ambientBlockData.fintypeBlock
    navarro417PhaseAInductionMap table.q_radical.isPGroup S414
        O.ambientBlockData.catalogue
        table.normalizerBlock =
      three.nonprincipalBlock := by
  dsimp only
  let O := R.1.operations
  let localData := O.inflatedNormalizerBlockData Q
  let _ : Fintype (InflatedNormalizerBlock (k := k) Q) :=
    localData.fintypeBlock
  let _ : Fintype (ActualBlock (k := k) (X := X)) :=
    O.ambientBlockData.fintypeBlock
  let hQ : IsPGroup 3 Q := table.q_radical.isPGroup
  have hLocal :
      navarro417LocalHasDefect (p := 3) (P := Q) localData.blocks
        table.normalizerBlock (defectSubgroupInNormalizer Q) := by
    refine ⟨defectSubgroupInNormalizer_isPGroup hQ, ?_⟩
    simpa only [LocalSupport411] using hLocalSupport
  have hAmbient :
      navarro417AmbientHasDefect (p := 3) O.ambientBlockData.blocks
        (navarro417PhaseAInductionMap hQ S414
          O.ambientBlockData.catalogue table.normalizerBlock) Q :=
    navarro417PhaseAInductionMap_has_ambientP hQ localData.blocks
      O.ambientBlockData.blocks localData.catalogue S414
        O.ambientBlockData.catalogue S413 SUpper table.normalizerBlock hLocal
  apply U.eq_nonprincipal_of_ambientHasDefect
  simpa only [AmbientHasDefect] using hAmbient

/-- The aligned table normaliser block induces to the named nonprincipal
ambient block.  This is the selector characterisation applied to the image
equality above, not an additional source field. -/
theorem tableNormalizerBlock_inducesTo_nonprincipal
    (R : LiteralCarrierAdapter
      (p := 3) (k := k) (K := K) (X := X))
    (three : Fi24ThreeBlockSource (k := k) (X := X))
    (Q : Subgroup X)
    (table :
      SporadicFi24P3QSquaredLocalTableSource.Source Q
        (R.1.operations.toLocalNormalizerBlockOperations Q))
    (hLocalSupport : LocalSupport411 R Q table.normalizerBlock)
    (U : SporadicFi24P3QSquaredAmbientUniqueness.Source R three Q)
    (S414 : PhaseASource R Q table)
    (S413 : MappedDefectSource R Q)
    (SUpper : UpperDefectSource R Q table S414) :
    let O := R.1.operations
    let localData := O.inflatedNormalizerBlockData Q
    letI : Fintype (InflatedNormalizerBlock (k := k) Q) :=
      localData.fintypeBlock
    letI : Fintype (ActualBlock (k := k) (X := X)) :=
      O.ambientBlockData.fintypeBlock
    BlockInducesTo (defectNormalizer Q) localData.catalogue
      O.ambientBlockData.catalogue table.normalizerBlock
        three.nonprincipalBlock := by
  dsimp only
  let O := R.1.operations
  let localData := O.inflatedNormalizerBlockData Q
  let _ : Fintype (InflatedNormalizerBlock (k := k) Q) :=
    localData.fintypeBlock
  let _ : Fintype (ActualBlock (k := k) (X := X)) :=
    O.ambientBlockData.fintypeBlock
  let hQ : IsPGroup 3 Q := table.q_radical.isPGroup
  apply (blockInducesTo_iff_navarro417PhaseAInductionMap_eq
    hQ S414 O.ambientBlockData.catalogue table.normalizerBlock
      three.nonprincipalBlock).2
  exact phaseAInductionMap_tableNormalizerBlock_eq_nonprincipal
    R three Q table hLocalSupport U S414 S413 SUpper

/-- The normaliser central Brauer image of the named nonprincipal block
idempotent is the aligned local block idempotent.  Unlike the image and
block-induction theorems, this conclusion requires the independent raw
Navarro (4.15)--(4.16) class-sum source. -/
theorem normalizerCentralBrauerMap_nonprincipalBlockIdempotent_eq
    (R : LiteralCarrierAdapter
      (p := 3) (k := k) (K := K) (X := X))
    (three : Fi24ThreeBlockSource (k := k) (X := X))
    (Q : Subgroup X)
    (table :
      SporadicFi24P3QSquaredLocalTableSource.Source Q
        (R.1.operations.toLocalNormalizerBlockOperations Q))
    (hLocalSupport : LocalSupport411 R Q table.normalizerBlock)
    (U : SporadicFi24P3QSquaredAmbientUniqueness.Source R three Q)
    (S414 : PhaseASource R Q table)
    (S413 : MappedDefectSource R Q)
    (SUpper : UpperDefectSource R Q table S414)
    (S415416 : RawClassSource R Q table) :
    let O := R.1.operations
    let localData := O.inflatedNormalizerBlockData Q
    letI : Fintype (InflatedNormalizerBlock (k := k) Q) :=
      localData.fintypeBlock
    letI : Fintype (ActualBlock (k := k) (X := X)) :=
      O.ambientBlockData.fintypeBlock
    normalizerCentralBrauerMap (k := k) (p := 3) Q
        table.q_radical.isPGroup
        (O.ambientBlockData.blocks.blockIdempotentInCenter
          three.nonprincipalBlock) =
      localData.blocks.blockIdempotentInCenter table.normalizerBlock := by
  dsimp only
  let O := R.1.operations
  let localData := O.inflatedNormalizerBlockData Q
  let _ : Fintype (InflatedNormalizerBlock (k := k) Q) :=
    localData.fintypeBlock
  let _ : Fintype (ActualBlock (k := k) (X := X)) :=
    O.ambientBlockData.fintypeBlock
  let hQ : IsPGroup 3 Q := table.q_radical.isPGroup
  have hLocal :
      navarro417LocalHasDefect (p := 3) (P := Q) localData.blocks
        table.normalizerBlock (defectSubgroupInNormalizer Q) := by
    refine ⟨defectSubgroupInNormalizer_isPGroup hQ, ?_⟩
    simpa only [LocalSupport411] using hLocalSupport
  have hSelected :=
    normalizerCentralBrauerMap_selectedBlockIdempotent_eq
      hQ localData.blocks
        (navarro417LocalHasDefect (p := 3) (P := Q) localData.blocks)
        O.ambientBlockData.blocks localData.catalogue S414
        O.ambientBlockData.catalogue S415416 table.normalizerBlock hLocal
  have hImage :=
    phaseAInductionMap_tableNormalizerBlock_eq_nonprincipal
      R three Q table hLocalSupport U S414 S413 SUpper
  rw [← hImage]
  exact hSelected

end ModularRep.PaperProofs.SporadicFi24P3QSquaredFirstMainImageBridge


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
