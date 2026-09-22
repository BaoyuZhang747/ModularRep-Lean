import ModularRep.PaperProofs.ComputationTranscriptAdditionalBindings
import ModularRep.PaperProofs.SporadicFi24P3NamedTableCentralCharacterTranscript
import ModularRep.PaperProofs.SporadicFi24P3NamedTableLiteralWeightRows
import ModularRep.PaperProofs.SporadicFi24P3ThreeBlockSourceFromSources

/-!
# The `Fi'_{24}` positive-radical block calculation from narrow sources

The checked `fi24p3` transcript records four defect-zero quotient rows whose
inflations occur in local table block position two.  The checked `fi24blocks`
transcript records 32 returned table-compatible fusion entries and the single
assignment pattern `[2, 2, 2, 2, 2, 2]` for the six ordinary rows of that
local block.  These are numerical named-table statements: neither transcript
constructs the literal normaliser inclusion, a class fusion for that
inclusion, or primitive block idempotents.

This file therefore keeps the two semantic identifications separate.  The
existing `Fi24P3BlockIndexBinding` identifies the nonprincipal source role
with one block in a complete literal block catalogue.  The existing
`Fi24P3NamedTableIntervalCentralCharacterMatch` is the remaining one-field
binding from the named-table central character calculation to that literal
block.  Navarro (4.14), retained independently in `PhaseASource`, then proves
block induction.  The local table source proves that every one of the four
named rows attaches to the common normaliser block, and Lean consequently
proves block preservation for the four corresponding literal weights.

The numerical transcript checks below do not discharge the semantic
central character binding.  Conversely, the source contract contains no
`BlockInducesTo` field, character--weight equivalence, row or radical
coverage, character triple, extension, BAW, or iBAW assertion.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3PositiveQBlockInductionFromSources

open ModularRep
open ModularRep.CharacterWeight
open ModularRep.PaperProofs.ComputationTranscriptAdditionalBindings
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24P3NamedTableCentralCharacterAdapter
open ModularRep.PaperProofs.SporadicFi24P3NamedTableCentralCharacterTranscript
open ModularRep.PaperProofs.SporadicFi24P3NamedTableLiteralWeightRows
open ModularRep.PaperProofs.SporadicFi24P3QSquaredLocalTableSource
open ModularRep.PaperProofs.SporadicFi24P3ThreeBlockSourceFromSources
open ModularRep.PaperProofs.SporadicFi24SelectedOuterInvolutionCarrier

universe u

variable {k K X BlockIndex : Type u}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X] [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}

/-! ## Kernel checks of the two named-table transcripts -/

/-- The four typed row labels have exactly the six numerical coordinates
printed by `fi24p3.out`.  This checks labels only; it does not identify the
typed ordinary characters in a `Source` with CTblLib rows. -/
theorem namedRows_are_localTranscriptRows :
    [printedRow .r23, printedRow .r24, printedRow .r51, printedRow .r52] =
      fi24ThreeLocalTableCertificateFromTranscript := by
  rw [fi24ThreeLocalTableCertificate_exact]
  decide

/-- Every assignment vector retained in the `fi24blocks.out` pattern list is
the constant ambient-position-two vector.  The transcript describes that
list as the set of patterns over all returned fusion entries; interpreting
this membership as a fact about literal class fusions remains external. -/
theorem everyRecordedAssignmentPattern_eq_positionTwo
    {pattern : List Nat}
    (hpattern : pattern ∈ assignmentPatternsFromTranscript) :
    pattern = [2, 2, 2, 2, 2, 2] := by
  rw [assignmentPatterns_exact] at hpattern
  simpa using hpattern

/-- The packet records 32 returned entries and only the position-two
assignment pattern.  It does not assert that the entries are distinct. -/
theorem returnedFusionTranscript_exact :
    possibleFusionCountFromTranscript = 32 ∧
      assignmentPatternsFromTranscript = [[2, 2, 2, 2, 2, 2]] :=
  ⟨possibleFusionCount_exact, assignmentPatterns_exact⟩

/-! ## Literal catalogue target and the exact residual source -/

/-- The literal primitive block attached by the complete catalogue binding
to the ACOU nonprincipal role.  The role binding, rather than the numeral
`2` by itself, supplies the mathematical meaning of this target. -/
noncomputable def literalB1
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (catalogue : Fi24P3BlockIndexBinding BlockIndex) :
    ActualBlock (k := k) (X := X) :=
  catalogue.literalBlockEquiv blocks .nonprincipal

/-- Exact conclusion-free inputs for the positive-radical block calculation.

`table` is the literal local-table carrier package; its row labels still need
the external table-to-carrier interpretation documented in that source.
`navarro414` is the first central-function equality in Navarro (4.14).
`allReturnedFusions_positionTwo` is the sole remaining E1/E2/E3/U semantic bridge:
it identifies the exact interval composite for the common literal local block
with the central character of the role-bound literal `B1`.  It is not a block
induction, weight membership, or coverage premise. -/
structure Source
    (R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := X))
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (catalogue : Fi24P3BlockIndexBinding BlockIndex)
    (Q : Subgroup X)
    (table : SporadicFi24P3QSquaredLocalTableSource.Source Q
      (R.1.operations.toLocalNormalizerBlockOperations Q)) where
  navarro414 : PhaseASource R Q table
  /-- The literal ambient block represented by CTblLib position two. -/
  positionTwoBlock : ActualBlock (k := k) (X := X)
  /-- The exact semantic reading of the fusion-independent position-two
  assignment.  This is the residual table/fusion/inclusion/splitting-system
  binding; the numerical transcript alone does not construct this value. -/
  allReturnedFusions_positionTwo :
    Fi24P3NamedTableIntervalCentralCharacterMatch
      R positionTwoBlock Q table
  /-- The independent complete-catalogue identification of ambient table
  position two with the ACOU nonprincipal role. -/
  positionTwo_eq_literalB1 : positionTwoBlock = literalB1 blocks catalogue

namespace Source

variable
  {R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := X)}
  {blocks : BlockIdempotentDecomposition blockIdempotent}
  {catalogue : Fi24P3BlockIndexBinding BlockIndex}
  {Q : Subgroup X}
  {table : SporadicFi24P3QSquaredLocalTableSource.Source Q
    (R.1.operations.toLocalNormalizerBlockOperations Q)}

/-- Compose the fusion-independent named-table allocation with the separate
position-to-role catalogue binding.  The result is still only the lower
central character equality, not a block-induction assertion. -/
theorem centralCharacterBinding_literalB1
    (S : Source R blocks catalogue Q table) :
    Fi24P3NamedTableIntervalCentralCharacterMatch
      R (literalB1 blocks catalogue) Q table := by
  rw [← S.positionTwo_eq_literalB1]
  exact S.allReturnedFusions_positionTwo

/-- Each of the four supplied defect-zero quotient characters attaches, after
inflation, to the common literal normaliser block `b`.  This is the exact
local block-membership deduction needed by the weight construction; it does
not say that the four rows exhaust the local block. -/
theorem inflatedCharacterBlock_eq_common
    (r : P3QSquaredTableRow) :
    R.1.operations.inflateToNormalizer Q
        (R.1.operations.localCharacterBlock Q (table.ordinary r)
          (table.ordinary_defectZero r)) =
      table.normalizerBlock := by
  let O := R.1.operations
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

/-- Navarro (4.14) and the one-field central character binding prove that the
common literal normaliser block induces to the role-bound literal `B1`.
This is a kernel consequence, not a field of `Source`. -/
theorem commonBlock_inducesTo_literalB1
    (S : Source R blocks catalogue Q table) :
    let O := R.1.operations
    let localData := O.inflatedNormalizerBlockData Q
    letI : Fintype (InflatedNormalizerBlock (k := k) Q) :=
      localData.fintypeBlock
    letI : Fintype (ActualBlock (k := k) (X := X)) :=
      O.ambientBlockData.fintypeBlock
    BlockInducesTo (defectNormalizer Q) localData.catalogue
      O.ambientBlockData.catalogue table.normalizerBlock
        (literalB1 blocks catalogue) := by
  exact tableNormalizerBlock_inducesTo_target
    R (literalB1 blocks catalogue) Q table S.navarro414
      S.centralCharacterBinding_literalB1

/-- The four named positive-radical weights preserve the literal block:
each weight determined by one of the supplied defect-zero local characters
belongs to the role-bound nonprincipal block `B1`.

The quantifier ranges only over the four constructors of
`P3QSquaredTableRow`; no converse or global radical-support statement is
claimed. -/
theorem namedTableRowWeight_block_literalB1
    (S : Source R blocks catalogue Q table)
    (r : P3QSquaredTableRow) :
    R.1.weightBlock (tableRowWeight R Q table r) =
      literalB1 blocks catalogue := by
  exact tableRowWeight_block R (literalB1 blocks catalogue) Q table
    S.navarro414 S.centralCharacterBinding_literalB1 r

/-- The role-bound literal `B1` is definitionally the nonprincipal block in
the three-block source constructed from the same catalogue binding.  The
selected outer involution and its action binding affect the action fields of
that source, not this block identity. -/
theorem literalB1_eq_constructedNonprincipal
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (Involution : SelectedOuterInvolutionCarrier X)
    (BlockBinding : Fi24P3BlockIndexBinding BlockIndex)
    (BlockAction : Fi24P3SelectedOuterBlockActionBinding
      blocks Involution BlockBinding) :
    literalB1 blocks BlockBinding =
      (fi24ThreeBlockSourceOfBindings
        blocks Involution BlockBinding BlockAction).nonprincipalBlock := by
  rfl

/-- Downstream form of the residual central character match, with exactly the
nonprincipal block used by the source-facing three-block composite.  Its proof
uses only the two lower semantic bindings stored in `S` and the definitional
catalogue reindexing above. -/
theorem centralCharacterMatch_constructedNonprincipal
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (Involution : SelectedOuterInvolutionCarrier X)
    (BlockBinding : Fi24P3BlockIndexBinding BlockIndex)
    (BlockAction : Fi24P3SelectedOuterBlockActionBinding
      blocks Involution BlockBinding)
    {R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := X)}
    {Q : Subgroup X}
    (table : SporadicFi24P3QSquaredLocalTableSource.Source Q
      (R.1.operations.toLocalNormalizerBlockOperations Q))
    (S : Source R blocks BlockBinding Q table) :
    Fi24P3NamedTableIntervalCentralCharacterMatch R
      (fi24ThreeBlockSourceOfBindings
        blocks Involution BlockBinding BlockAction).nonprincipalBlock
      Q table := by
  rw [← literalB1_eq_constructedNonprincipal
    blocks Involution BlockBinding BlockAction]
  exact S.centralCharacterBinding_literalB1

/-- The common normaliser block induces to the exact nonprincipal block used
by the source-facing three-block construction. -/
theorem commonBlock_inducesTo_constructedNonprincipal
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (Involution : SelectedOuterInvolutionCarrier X)
    (BlockBinding : Fi24P3BlockIndexBinding BlockIndex)
    (BlockAction : Fi24P3SelectedOuterBlockActionBinding
      blocks Involution BlockBinding)
    {R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := X)}
    {Q : Subgroup X}
    (table : SporadicFi24P3QSquaredLocalTableSource.Source Q
      (R.1.operations.toLocalNormalizerBlockOperations Q))
    (S : Source R blocks BlockBinding Q table) :
    let O := R.1.operations
    let localData := O.inflatedNormalizerBlockData Q
    letI : Fintype (InflatedNormalizerBlock (k := k) Q) :=
      localData.fintypeBlock
    letI : Fintype (ActualBlock (k := k) (X := X)) :=
      O.ambientBlockData.fintypeBlock
    BlockInducesTo (defectNormalizer Q) localData.catalogue
      O.ambientBlockData.catalogue table.normalizerBlock
        (fi24ThreeBlockSourceOfBindings
          blocks Involution BlockBinding BlockAction).nonprincipalBlock := by
  dsimp only
  rw [← literalB1_eq_constructedNonprincipal
    blocks Involution BlockBinding BlockAction]
  exact S.commonBlock_inducesTo_literalB1

/-- Final narrow block-preservation form: each of the four named local rows
gives a literal weight in the exact nonprincipal block used downstream. -/
theorem namedTableRowWeight_block_constructedNonprincipal
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (Involution : SelectedOuterInvolutionCarrier X)
    (BlockBinding : Fi24P3BlockIndexBinding BlockIndex)
    (BlockAction : Fi24P3SelectedOuterBlockActionBinding
      blocks Involution BlockBinding)
    {R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := X)}
    {Q : Subgroup X}
    (table : SporadicFi24P3QSquaredLocalTableSource.Source Q
      (R.1.operations.toLocalNormalizerBlockOperations Q))
    (S : Source R blocks BlockBinding Q table)
    (r : P3QSquaredTableRow) :
    R.1.weightBlock (tableRowWeight R Q table r) =
      (fi24ThreeBlockSourceOfBindings
        blocks Involution BlockBinding BlockAction).nonprincipalBlock := by
  rw [← literalB1_eq_constructedNonprincipal
    blocks Involution BlockBinding BlockAction]
  exact S.namedTableRowWeight_block_literalB1 r

end Source

end ModularRep.PaperProofs.SporadicFi24P3PositiveQBlockInductionFromSources


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
