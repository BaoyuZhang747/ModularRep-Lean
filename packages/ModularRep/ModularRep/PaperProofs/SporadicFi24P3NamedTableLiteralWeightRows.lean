import ModularRep.PaperProofs.SporadicFi24P3NamedTableCentralCharacterAdapter
import ModularRep.PaperProofs.CharacterWeightRepresentativeFibre

/-!
# Literal weights carried by the four named Fi'24 rows at three

This experimental module makes a one-way connection from the generic
four-row local table to the character-weight conjugacy class carrier.  A
radical subgroup and a defect-zero quotient character determine a weight
class; the named central character adapter then places that class in a separately
supplied target block.  Injectivity of the four ordinary rows gives
injectivity of the four resulting literal weights.

There is no converse or coverage statement.  In particular, this module does
not prove that the target weight fibre has cardinality four, compute fixed
points of an outer involution, construct a block-fibre equivalence, or supply
an An--Dietrich, BAW, or iBAW conclusion.  The imported table source retains
its exact fifteen fields, and the interval match retains its sole lower-level
central character equality.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3NamedTableLiteralWeightRows

open ModularRep
open ModularRep.CharacterWeight
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24P3QSquaredLocalTableSource
open ModularRep.PaperProofs.SporadicFi24P3NamedTableCentralCharacterAdapter

universe u

variable {k K X : Type u}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

variable (R :
  LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := X))

/-- The literal radical-subgroup carrier determined by the table's supplied
radicality witness. -/
def tableRadical
    (Q : Subgroup X)
    (table : Source Q
      (R.1.operations.toLocalNormalizerBlockOperations Q)) :
    CharacterWeight.RadicalSubgroup (p := 3) (G := X) :=
  ⟨Q, table.q_radical⟩

/-- The local defect-zero character carried by one supplied table row. -/
def tableLocalDZ
    (Q : Subgroup X)
    (table : Source Q
      (R.1.operations.toLocalNormalizerBlockOperations Q))
    (r : P3QSquaredTableRow) :
    CharacterWeight.LocalDefectZeroCharacter
      (K := K) (tableRadical R Q table) :=
  ⟨table.ordinary r, table.ordinary_defectZero r⟩

/-- The literal global character-weight conjugacy class carried by one
supplied table row.  Its radical class is represented by `Q`; no block or
coverage assertion is part of the definition. -/
def tableRowWeight
    (Q : Subgroup X)
    (table : Source Q
      (R.1.operations.toLocalNormalizerBlockOperations Q))
    (r : P3QSquaredTableRow) :
    WeightClass (p := 3) (K := K) (X := X) :=
  (CharacterWeight.localDefectZeroEquivWeightRadicalFibre
    (K := K) Nat.prime_three (tableRadical R Q table)
    (tableLocalDZ R Q table r)).1

/-- Every supplied row gives a literal weight in the target block selected by
the independent interval central character match.  This is one-way block
membership, not an exhaustivity statement. -/
theorem tableRowWeight_block
    (targetBlock : ActualBlock (k := k) (X := X))
    (Q : Subgroup X)
    (table : Source Q
      (R.1.operations.toLocalNormalizerBlockOperations Q))
    (S414 : PhaseASource R Q table)
    (M : Fi24P3NamedTableIntervalCentralCharacterMatch
      R targetBlock Q table)
    (r : P3QSquaredTableRow) :
    R.1.weightBlock (tableRowWeight R Q table r) = targetBlock := by
  let O := R.1.operations
  let localData := O.inflatedNormalizerBlockData Q
  let _ : Fintype (InflatedNormalizerBlock (k := k) Q) :=
    localData.fintypeBlock
  let _ : Fintype (ActualBlock (k := k) (X := X)) :=
    O.ambientBlockData.fintypeBlock
  have hLocalBlock :
      O.inflateToNormalizer Q
          (O.localCharacterBlock Q (table.ordinary r)
            (table.ordinary_defectZero r)) =
        table.normalizerBlock := by
    calc
      O.inflateToNormalizer Q
          (O.localCharacterBlock Q (table.ordinary r)
            (table.ordinary_defectZero r)) =
          O.inflateToNormalizer Q (table.quotientBlock r) := by
        apply congrArg (O.inflateToNormalizer Q)
        simpa [O,
          CharacterWeight.LocalBlockInductionOperations.toLocalNormalizerBlockOperations] using
          table.quotientBlock_of_ordinary r
      _ = table.normalizerBlock := by
        simpa [O,
          CharacterWeight.LocalBlockInductionOperations.toLocalNormalizerBlockOperations] using
          table.inflated_quotientBlock r
  have hInduces :
      BlockInducesTo (defectNormalizer Q) localData.catalogue
        O.ambientBlockData.catalogue table.normalizerBlock targetBlock := by
    simpa [O, localData] using
      tableNormalizerBlock_inducesTo_target
        R targetBlock Q table S414 M
  have hAttachedInduces :
      BlockInducesTo (defectNormalizer Q) localData.catalogue
        O.ambientBlockData.catalogue
        (O.inflateToNormalizer Q
          (O.localCharacterBlock Q (table.ordinary r)
            (table.ordinary_defectZero r))) targetBlock := by
    rw [hLocalBlock]
    exact hInduces
  rw [tableRowWeight,
    CharacterWeight.localDefectZeroEquivWeightRadicalFibre_apply_val,
    CharacterWeight.LocalBlockInductionSource.weightBlock_mk]
  change
    inducedBlock (defectNormalizer Q) localData.catalogue
        O.ambientBlockData.catalogue
        (O.inflateToNormalizer Q
          (O.localCharacterBlock Q (table.ordinary r)
            (table.ordinary_defectZero r)))
        (O.blockInductionDefined
          (CharacterWeight.characterWeightAt Nat.prime_three
            (tableRadical R Q table) (tableLocalDZ R Q table r))) =
      targetBlock
  exact (eq_inducedBlock_of_blockInducesTo
    (defectNormalizer Q) localData.catalogue O.ambientBlockData.catalogue
    (O.inflateToNormalizer Q
      (O.localCharacterBlock Q (table.ordinary r)
        (table.ordinary_defectZero r)))
    (O.blockInductionDefined
      (CharacterWeight.characterWeightAt Nat.prime_three
        (tableRadical R Q table) (tableLocalDZ R Q table r)))
    hAttachedInduces).symm

/-- Distinct supplied table rows give distinct global weight conjugacy classes.  Since
`P3QSquaredTableRow` has exactly four constructors, this is the promised set
of four distinct weight classes, without an assertion that it exhausts a block
fibre. -/
theorem tableRowWeight_injective
    (Q : Subgroup X)
    (table : Source Q
      (R.1.operations.toLocalNormalizerBlockOperations Q)) :
    Function.Injective (tableRowWeight R Q table) := by
  intro r s hrs
  let E := CharacterWeight.localDefectZeroEquivWeightRadicalFibre
    (K := K) Nat.prime_three (tableRadical R Q table)
  have hImages :
      E (tableLocalDZ R Q table r) =
        E (tableLocalDZ R Q table s) := by
    apply Subtype.ext
    exact hrs
  have hLocalDZ :
      tableLocalDZ R Q table r = tableLocalDZ R Q table s :=
    E.injective hImages
  apply table.ordinary_injective
  exact congrArg Subtype.val hLocalDZ

end ModularRep.PaperProofs.SporadicFi24P3NamedTableLiteralWeightRows


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
