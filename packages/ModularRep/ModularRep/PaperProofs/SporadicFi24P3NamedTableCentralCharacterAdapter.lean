import ModularRep.DefectNormalizerCarrier
import ModularRep.Navarro414IntervalCentralCharacterAdapter
import ModularRep.PaperProofs.SporadicFi24P3QSquaredLocalTableSource
import ModularRep.PaperProofs.SporadicFi24LiteralCarrierBase

/-!
# The named-table central character test for the Fischer prime-three block

This module isolates the logical use of the `CentralCharacter`/`SameBlock`
calculation.  Navarro's interval theorem supplies definedness of block
induction and identifies the induced central function with the exact interval
composite.  A separate one-field source identifies only that lower-level
interval composite with the central character of a separately supplied target
block.  The latter equality remains a U binding supported by E1/E2/E3
evidence; identifying that target with a concrete Fischer block is outside
this module.

No constituent-support assertion, First Main correspondence, weight,
equivariance, BAW, or iBAW conclusion occurs in this module.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3NamedTableCentralCharacterAdapter

open scoped MonoidAlgebra

open ModularRep
open ModularRep.CharacterWeight
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual

universe u

variable {k K X : Type u}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

local instance primeThreeFact : Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

local instance namedTableNormalizerFintype {Q : Subgroup X} :
    Fintype (defectNormalizer Q) :=
  Fintype.ofFinite _

/-- The Navarro (4.14) source for the fixed normaliser catalogue. -/
abbrev PhaseASource
    (R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := X))
    (Q : Subgroup X)
    (table : SporadicFi24P3QSquaredLocalTableSource.Source Q
      (R.1.operations.toLocalNormalizerBlockOperations Q)) : Prop :=
  let O := R.1.operations
  let localData := O.inflatedNormalizerBlockData Q
  letI : Fintype (InflatedNormalizerBlock (k := k) Q) :=
    localData.fintypeBlock
  Navarro414IntervalCentralCharacterSource
    (normalizerCentralBrauerInterval (p := 3) table.q_radical.isPGroup)
    localData.blocks localData.catalogue

/-- The one remaining named-table binding.  Its intended evidence combines
the published central character identities with a separately supplied target
block and the pinned GAP/CTblLib singleton block allocation.  Its sole field
equates the exact Navarro interval composite with the target block's central
character.  It contains no `inducedCentralFunction`, definedness,
`BlockInducesTo`, or character/fibre-surjectivity premise, and therefore
cannot prove block induction without the independent Navarro (4.14) source. -/
structure Fi24P3NamedTableIntervalCentralCharacterMatch
    (R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := X))
    (targetBlock : ActualBlock (k := k) (X := X))
    (Q : Subgroup X)
    (table : SporadicFi24P3QSquaredLocalTableSource.Source Q
      (R.1.operations.toLocalNormalizerBlockOperations Q)) : Prop where
  intervalComposite_toLinearMap_eq_target :
    let O := R.1.operations
    let localData := O.inflatedNormalizerBlockData Q
    let I :=
      normalizerCentralBrauerInterval (p := 3) table.q_radical.isPGroup
    letI : Fintype (InflatedNormalizerBlock (k := k) Q) :=
      localData.fintypeBlock
    letI : Fintype (ActualBlock (k := k) (X := X)) :=
      O.ambientBlockData.fintypeBlock
    ((localData.catalogue.centralCharacter table.normalizerBlock).comp
      (centralBrauerMapTo (k := k) (p := 3) Q (defectNormalizer Q)
        I.isPGroup I.centralizer_le I.le_normalizer)).toLinearMap =
      (O.ambientBlockData.catalogue.centralCharacter
        targetBlock).toLinearMap

/-- Navarro (4.14) gives both definedness and the bridge from the induced
central function to the interval composite.  The separate named-table source
then identifies that composite with the supplied target block's central
character. -/
theorem tableNormalizerBlock_inducesTo_target
    (R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := X))
    (targetBlock : ActualBlock (k := k) (X := X))
    (Q : Subgroup X)
    (table : SporadicFi24P3QSquaredLocalTableSource.Source Q
      (R.1.operations.toLocalNormalizerBlockOperations Q))
    (S414 : PhaseASource R Q table)
    (M : Fi24P3NamedTableIntervalCentralCharacterMatch
      R targetBlock Q table) :
    let O := R.1.operations
    let localData := O.inflatedNormalizerBlockData Q
    letI : Fintype (InflatedNormalizerBlock (k := k) Q) :=
      localData.fintypeBlock
    letI : Fintype (ActualBlock (k := k) (X := X)) :=
      O.ambientBlockData.fintypeBlock
    BlockInducesTo (defectNormalizer Q) localData.catalogue
      O.ambientBlockData.catalogue table.normalizerBlock
        targetBlock := by
  dsimp only
  let O := R.1.operations
  let localData := O.inflatedNormalizerBlockData Q
  let I :=
    normalizerCentralBrauerInterval (p := 3) table.q_radical.isPGroup
  let _ : Fintype (InflatedNormalizerBlock (k := k) Q) :=
    localData.fintypeBlock
  let _ : Fintype (ActualBlock (k := k) (X := X)) :=
    O.ambientBlockData.fintypeBlock
  refine ⟨S414.isBlockInductionDefined table.normalizerBlock, ?_⟩
  apply AlgHom.ext
  intro z
  change inducedCentralFunction (defectNormalizer Q)
      (localData.catalogue.centralCharacter table.normalizerBlock) z =
    O.ambientBlockData.catalogue.centralCharacter
      targetBlock z
  calc
    inducedCentralFunction (defectNormalizer Q)
        (localData.catalogue.centralCharacter table.normalizerBlock) z =
      ((localData.catalogue.centralCharacter table.normalizerBlock).comp
        (centralBrauerMapTo (k := k) (p := 3) Q (defectNormalizer Q)
          I.isPGroup I.centralizer_le I.le_normalizer)).toLinearMap z :=
      LinearMap.congr_fun
        (S414.inducedCentralFunction_eq_intervalBrauer
          table.normalizerBlock) z
    _ = O.ambientBlockData.catalogue.centralCharacter
        targetBlock z :=
      LinearMap.congr_fun M.intervalComposite_toLinearMap_eq_target z

end ModularRep.PaperProofs.SporadicFi24P3NamedTableCentralCharacterAdapter


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
