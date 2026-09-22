import ModularRep.PaperProofs.ComputationTranscriptActual
import ModularRep.PaperProofs.ComputationTranscriptAdditionalBindings

/-!
# Transcript-bound exceptional computation certificate

The finite exceptional-type-`B` arithmetic and transcript comparisons were
originally exposed as independent theorems.  This module instead states a
selected collection of finite conclusions directly on the literal values
emitted by the transcript elaborator.  It does not claim to reproduce every
field of `ExceptionalQ3OutputCertificate.Certificate`.

The kernel checks the stated arithmetic on those literal values.  The custom
elaborator's extraction of the values from the embedded files is a build-tool
trust boundary.  This module also does not certify GAP or CTblLib,
completeness of the searches, or the semantic identification of printed
labels with blocks, characters, or weights.
-/

namespace ModularRep.PaperProofs.ComputationTranscriptBoundCertificate

open ModularRep.ComputationTranscriptElab
open ModularRep.ManuscriptVerification.ExceptionalQ3OutputCertificate
open ModularRep.PaperProofs.ComputationTranscriptActual
open ModularRep.PaperProofs.ComputationTranscriptAdditionalBindings
open Formalisation.ComputationArithmetic

/-- Equalities between the emitted exceptional computation values and the
typed data on which the older finite certificate operates. -/
structure TranscriptEvidence where
  actionLists :
    q3BlockActionFromTranscript =
        [.B1, .B2, .B3, .B4, .B5, .B6, .B7, .B8, .B9].map
          (fun block => blockPosition (blockOuterAction block)) ∧
      q3BrauerActionFromTranscript =
        allBrauerLabels.map (fun label => (brauerOuterAction label).position)
  blockRows :
    q3BlockRowsFromTranscript =
        q3BlocksInTranscriptOrder.map q3BlockProjection ∧
      q3BlockRowsFromTranscript.map
          (fun row => (row.blockIndex, row.brauerLabels.length, row.sectorCode)) =
        q3BlocksInTranscriptOrder.map fun block =>
          (blockPosition block, q3BrauerCount block,
            q3SectorCode (q3Sector block))
  blockTwo :
    q3BlockTwoDefectExponentFromTranscript = blockTwoRecord.defectExponent ∧
      q3BlockTwoDefectOrderFromTranscript = blockTwoRecord.defectOrder ∧
      q3BlockTwoOrdinaryCountFromTranscript =
        blockTwoRecord.ordinaryCharacterCount ∧
      q3BlockTwoBrauerCountFromTranscript =
        blockTwoRecord.brauerCharacterCount ∧
      q3BlockTwoOrdinaryLabelsFromTranscript = blockTwoRecord.ordinaryLabels ∧
      q3BlockTwoBrauerLabelsFromTranscript =
        blockTwoRecord.brauerLabels.map BrauerLabel.position ∧
      q3BlockTwoOrdinaryDegreesFromTranscript =
        blockTwoRecord.ordinaryDegrees ∧
      q3BlockTwoHeightsFromTranscript = blockTwoRecord.heights ∧
      q3BlockTwoDecompositionFromTranscript =
        blockTwoRecord.decompositionMatrix ∧
      q3BlockTwoCartanFromTranscript = blockTwoRecord.cartanMatrix ∧
      q3BlockTwoCentralRatiosFromTranscript = blockTwoRecord.centralRatios ∧
      q3BlockTwoOuterImageFromTranscript =
        blockTwoRecord.outerBrauerImage.map BrauerLabel.position
  radicalSummary :
    q3RadicalClassCountFromTranscript = radicalClassContributions.length ∧
      q3RadicalSectorTotalsFromTranscript =
        [radicalSectorTotal .trivial, radicalSectorTotal .faithfulOne,
          radicalSectorTotal .faithfulTwo] ∧
      q3RadicalOrderContributionsFromTranscript =
        q3RadicalContributions.map fun row =>
          [row.subgroupOrder, row.trivial, row.faithfulOne, row.faithfulTwo]
  radicalRows :
    q3RadicalRowsFromTranscript =
      radicalClassContributions.map q3RadicalProjection
  radicalSearchBookkeeping :
    q3RadicalSearchBookkeepingFromTranscript =
      q3RadicalSearchBookkeepingCertificate
  radicalRepresentativeIndices :
    q3GRadicalRepresentativeIndicesDerivedFromTranscript =
        gRadicalRepresentativeIndices ∧
      q3GRadicalRepresentativeIndicesDerivedFromTranscript =
        q3RadicalRowsFromTranscript.map
          RadicalRowProjection.pSubgroupClassIndex
  localRows :
    q3LocalPrincipalWeightCountFromTranscript = localPrincipalWeightRecords.length ∧
      [q3Order128LocalRecordFromTranscript,
          q3Order256LocalRecordFromTranscript] =
        localPrincipalWeightRecords.map (fun row =>
          [row.centricClassCount, row.sRadicalRepresentativeCount,
            row.hRadicalRepresentativeCount, row.hNormalizerOrder,
            row.hCentralizerOrder, row.subgroupCentreOrder,
            row.weightQuotientOrder]) ∧
      [q3Order128DefectZeroDegreesFromTranscript,
          q3Order256DefectZeroDegreesFromTranscript] =
        localPrincipalWeightRecords.map
          LocalPrincipalWeightRecord.defectZeroDegrees
  principalCounts :
    q3SimplePrincipalBrauerCountsFromTranscript =
      [q3PrincipalIrreducibleRestrictions +
          2 * q3PrincipalSplitRestrictions,
        q3PrincipalHBrauerCount, q3PrincipalIrreducibleRestrictions,
        q3PrincipalSplitRestrictions]
  principalRestrictionRows :
    principalBrauerRestrictionPositionsFromTranscript =
      principalBrauerRestrictionRows.map
        (fun row => row.map SimplePrincipalBrauerLabel.position)

/-- Brauer-character totals in the three central sectors, calculated directly
from the nine parsed block rows. -/
def blockSectorTotalsFromTranscript : List Nat :=
  [0, 1, 2].map fun sector =>
    (q3BlockRowsFromTranscript.filter fun row => row.sectorCode = sector).map
      (fun row => row.brauerLabels.length) |>.sum

/-- Weight totals in the three central sectors, calculated directly from the
twelve parsed radical rows. -/
def radicalSectorTotalsDerivedFromRows : List Nat :=
  [(q3RadicalRowsFromTranscript.map fun row => row.trivialLabels.length).sum,
   (q3RadicalRowsFromTranscript.map fun row => row.faithfulOneLabels.length).sum,
   (q3RadicalRowsFromTranscript.map fun row => row.faithfulTwoLabels.length).sum]

/-- Lookup in the parsed `P_RADICAL` rows.  The default row can occur only
outside the parsed index set; the certificate below proves that it is not used
by a printed fusion row. -/
def lookupParsedPRadicalRowIn (index : Nat) :
    List PRadicalRowProjection -> PRadicalRowProjection
  | [] => ⟨0, 0, 0⟩
  | row :: rows =>
      if row.pSubgroupClassIndex = index then row
      else lookupParsedPRadicalRowIn index rows

def lookupParsedPRadicalRow (index : Nat) : PRadicalRowProjection :=
  lookupParsedPRadicalRowIn index
    q3RadicalSearchBookkeepingFromTranscript.pRadicalRows

/-- Finite conclusions stated on the values parsed from the archived output
files themselves.  Unlike the earlier packaging, these fields do not merely
place an independently proved certificate next to transcript equalities. -/
structure BoundCertificate extends TranscriptEvidence where
  blockRowCount : q3BlockRowsFromTranscript.length = 9
  blockBrauerCount :
    (q3BlockRowsFromTranscript.map fun row => row.brauerLabels.length).sum = 33
  blockSectorTotals : blockSectorTotalsFromTranscript = [17, 8, 8]
  blockTwoDimensions :
    q3BlockTwoDefectOrderFromTranscript =
        2 ^ q3BlockTwoDefectExponentFromTranscript ∧
      q3BlockTwoOrdinaryLabelsFromTranscript.length =
        q3BlockTwoOrdinaryCountFromTranscript ∧
      q3BlockTwoOrdinaryDegreesFromTranscript.length =
        q3BlockTwoOrdinaryCountFromTranscript ∧
      q3BlockTwoHeightsFromTranscript.length =
        q3BlockTwoOrdinaryCountFromTranscript ∧
      q3BlockTwoDecompositionFromTranscript.length =
        q3BlockTwoOrdinaryCountFromTranscript ∧
      (∀ row ∈ q3BlockTwoDecompositionFromTranscript,
        row.length = q3BlockTwoBrauerCountFromTranscript) ∧
      q3BlockTwoBrauerLabelsFromTranscript.length =
        q3BlockTwoBrauerCountFromTranscript
  blockTwoCartan :
    q3BlockTwoCartanFromTranscript =
      listMatrixGramTwo q3BlockTwoDecompositionFromTranscript
  blockTwoHeightDistribution :
    q3BlockTwoHeightsFromTranscript.count 0 = 4 ∧
      q3BlockTwoHeightsFromTranscript.count 1 = 1
  blockTwoOuterImage :
    q3BlockTwoOuterImageFromTranscript = q3BlockTwoBrauerLabelsFromTranscript
  blockTwoCentralRatios : q3BlockTwoCentralRatiosFromTranscript = [1, 1, 1]
  subgroupDistributionTotal :
    (q3RadicalSearchBookkeepingFromTranscript.subgroupOrderDistribution.map
      SubgroupOrderMultiplicityProjection.multiplicity).sum = 3021
  pRadicalRowCount :
    q3RadicalSearchBookkeepingFromTranscript.pRadicalRows.length = 26
  fusionRowCount :
    q3RadicalSearchBookkeepingFromTranscript.fusionRows.length = 14
  fusionRowsPreserveOrders :
    ∀ fusion ∈ q3RadicalSearchBookkeepingFromTranscript.fusionRows,
      let source := lookupParsedPRadicalRow fusion.sourcePClassIndex
      let target := lookupParsedPRadicalRow fusion.targetPClassIndex
      source.pSubgroupClassIndex = fusion.sourcePClassIndex ∧
        target.pSubgroupClassIndex = fusion.targetPClassIndex ∧
        source.subgroupOrder = target.subgroupOrder ∧
        source.normalizerOrder = target.normalizerOrder
  fusionTargetsAreRetained :
    ∀ fusion ∈ q3RadicalSearchBookkeepingFromTranscript.fusionRows,
      fusion.targetPClassIndex ∈
        q3GRadicalRepresentativeIndicesDerivedFromTranscript
  fusionPartition :
    ((q3RadicalSearchBookkeepingFromTranscript.fusionRows.map
        GFusionRowProjection.sourcePClassIndex) ++
      q3GRadicalRepresentativeIndicesDerivedFromTranscript).Nodup ∧
    (((q3RadicalSearchBookkeepingFromTranscript.fusionRows.map
        GFusionRowProjection.sourcePClassIndex) ++
      q3GRadicalRepresentativeIndicesDerivedFromTranscript).toFinset =
        (q3RadicalSearchBookkeepingFromTranscript.pRadicalRows.map
          PRadicalRowProjection.pSubgroupClassIndex).toFinset)
  radicalRowCount : q3RadicalRowsFromTranscript.length = 12
  radicalQuotientArithmetic :
    ∀ row ∈ q3RadicalRowsFromTranscript,
      row.subgroupOrder * row.weightQuotientOrder = row.normalizerOrder
  radicalSectorTotalsFromRows :
    radicalSectorTotalsDerivedFromRows = [17, 8, 8]
  radicalPrintedSectorTotals :
    q3RadicalSectorTotalsFromTranscript = [17, 8, 8]
  sectorAgreement :
    blockSectorTotalsFromTranscript = radicalSectorTotalsDerivedFromRows
  localRowsExact :
    q3LocalPrincipalWeightCountFromTranscript = 2 ∧
      [q3Order128LocalRecordFromTranscript,
        q3Order256LocalRecordFromTranscript] =
        [[53, 1, 1, 27648, 8, 8, 216],
          [15, 3, 1, 9216, 8, 8, 36]] ∧
      [q3Order128DefectZeroDegreesFromTranscript,
        q3Order256DefectZeroDegreesFromTranscript] = [[8], [4]]
  localArithmetic :
    q3Order128LocalRecordFromTranscript.getD 2 0 = 1 ∧
      q3Order256LocalRecordFromTranscript.getD 2 0 = 1 ∧
      q3Order128LocalRecordFromTranscript.getD 4 0 =
        q3Order128LocalRecordFromTranscript.getD 5 0 ∧
      q3Order256LocalRecordFromTranscript.getD 4 0 =
        q3Order256LocalRecordFromTranscript.getD 5 0 ∧
      8 ∣ q3Order128LocalRecordFromTranscript.getD 6 0 ∧
      Odd (q3Order128LocalRecordFromTranscript.getD 6 0 / 8) ∧
      4 ∣ q3Order256LocalRecordFromTranscript.getD 6 0 ∧
      Odd (q3Order256LocalRecordFromTranscript.getD 6 0 / 4)
  principalCountsExact :
    q3SimplePrincipalBrauerCountsFromTranscript = [12, 10, 8, 2]
  principalRestrictionRowsExact :
    principalBrauerRestrictionPositionsFromTranscript =
      [[1], [2], [3], [4], [5, 6], [7], [8], [9], [10], [11, 12]]
  principalRestrictionPartition :
    principalBrauerRestrictionPositionsFromTranscript.flatten =
      [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
  principalRestrictionShape :
    (principalBrauerRestrictionPositionsFromTranscript.map List.length).count 1 = 8 ∧
      (principalBrauerRestrictionPositionsFromTranscript.map List.length).count 2 = 2

theorem exceptionalQ3TranscriptBoundCertificate : BoundCertificate where
  actionLists := q3_action_lists_are_the_transcript_lists
  blockRows := q3_block_rows_are_the_transcript_rows
  blockTwo := q3_block_two_record_is_the_transcript_record
  radicalSummary := q3_radical_summary_is_the_transcript_summary
  radicalRows := q3_radical_rows_are_the_transcript_rows
  radicalSearchBookkeeping :=
    q3_radical_search_bookkeeping_is_the_transcript_bookkeeping
  radicalRepresentativeIndices :=
    q3_g_radical_representative_indices_are_transcript_derived
  localRows := q3_local_weight_records_are_the_transcript_records
  principalCounts := q3_simple_principal_brauer_counts_exact
  principalRestrictionRows :=
    principalBrauerRestrictionRows_are_the_transcript_rows
  blockRowCount := by decide
  blockBrauerCount := by decide
  blockSectorTotals := by decide
  blockTwoDimensions := by decide
  blockTwoCartan := by decide
  blockTwoHeightDistribution := by decide
  blockTwoOuterImage := by decide
  blockTwoCentralRatios := by decide
  subgroupDistributionTotal := by decide
  pRadicalRowCount := by decide
  fusionRowCount := by decide
  fusionRowsPreserveOrders := by decide
  fusionTargetsAreRetained := by decide
  fusionPartition := by decide
  radicalRowCount := by decide
  radicalQuotientArithmetic := by decide
  radicalSectorTotalsFromRows := by decide
  radicalPrintedSectorTotals := by decide
  sectorAgreement := by decide
  localRowsExact := by decide
  localArithmetic := by decide
  principalCountsExact := by decide
  principalRestrictionRowsExact := by decide
  principalRestrictionPartition := by decide
  principalRestrictionShape := by decide

end ModularRep.PaperProofs.ComputationTranscriptBoundCertificate


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
