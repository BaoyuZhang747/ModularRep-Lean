import ModularRep.ComputationTranscriptElab
import ModularRep.ComputationTranscriptSnapshots
import ModularRep.ExceptionalQ3OutputCertificate
import ModularRep.PaperProofs.SporadicProposition57ComputationRelative

/-!
# Literal certificates emitted from the transcript build inputs

The build layer embeds the current output files under the project root and the
`output_*` elaborators emit ordinary numerals, lists, matrices, and selected
record projections.  The kernel checks the equalities below over those emitted
terms.  It does not check the file-to-string operation or the elaborator's
string parsing.  `ComputationTranscriptSnapshots` ensures that both transcript
consumers use one shared embedded string per file.

This does not certify GAP, CTblLib, AtlasRep, or completeness of a search.
Those are still E3 inputs.  The mathematical identification of the tables,
permutation groups, and printed labels remains U.  The connection from the
current root output files to the emitted literals is audited build provenance.
The pure Lean parser in
`ComputationTranscriptPure` is kernel visible, but this module does not use it
to discharge provenance for the structured `U_BLOCK`, `G_RADICAL`, or raw
search records.
-/

namespace ModularRep.PaperProofs.ComputationTranscriptActual

open ModularRep.ComputationTranscriptElab
open ModularRep.ComputationTranscriptSnapshots
open ModularRep.ManuscriptVerification.ExceptionalQ3OutputCertificate
open ModularRep.PaperProofs.SporadicProposition57ComputationRelative
open Formalisation.ComputationArithmetic

/-! ## Baby Monster and Monster -/

def babyRegularClassCountFromTranscript : Nat := output_nat
  babyTranscript
  "REGULAR_POSITIONS_COUNT"

def babyBrauerBlockRanksFromTranscript : List Nat :=
  [output_nat
      babyTranscript
      "BLOCK_1_RANK_RANKMAT",
   output_nat
      babyTranscript
      "BLOCK_2_RANK_RANKMAT"]

theorem baby_transcript_counts_exact :
    babyRegularClassCountFromTranscript = 27 ∧
      babyBrauerBlockRanksFromTranscript = [25, 2] ∧
      babyBrauerBlockRanksFromTranscript.sum =
        babyRegularClassCountFromTranscript := by
  decide

def monsterRegularClassCountFromTranscript : Nat := output_nat
  monsterTranscript
  "TWO_REGULAR_CLASS_COUNT"

def monsterBlockDefectsFromTranscript : List Nat := output_nat_list
  monsterTranscript
  "BLOCK_DEFECT_EXPONENTS"

def monsterOrdinaryBlockCountsFromTranscript : List Nat := output_nat_list
  monsterTranscript
  "ORDINARY_kB_COUNTS"

def monsterDefectZeroLabelsFromTranscript : List Nat := output_nat_list
  monsterTranscript
  "DEFECT_ZERO_LABELS"

theorem monster_transcript_counts_exact :
    monsterRegularClassCountFromTranscript = monsterTwoRegularClassCount ∧
      monsterBlockDefectsFromTranscript = monsterTwoDefects ∧
      monsterOrdinaryBlockCountsFromTranscript = monsterTwoOrdinaryCounts ∧
      monsterDefectZeroLabelsFromTranscript = [2, 3, 5] := by
  decide

/-! ## `Fi'_24` at five and the principal rows at two -/

def fi24FiveBrauerTrivialRowsFromTranscript : List SignatureRow :=
  [(1,
      output_line_nat
        fi24BlocksTranscript
        "BLOCK label=P5 p=5 id=1 " "l",
      output_line_nat
        fi24BlocksTranscript
        "BLOCK label=P5 p=5 id=1 " "fixed"),
   (2,
      output_line_nat
        fi24BlocksTranscript
        "BLOCK label=P5 p=5 id=2 " "l",
      output_line_nat
        fi24BlocksTranscript
        "BLOCK label=P5 p=5 id=2 " "fixed"),
   (3,
      output_line_nat
        fi24BlocksTranscript
        "BLOCK label=P5 p=5 id=3 " "l",
      output_line_nat
        fi24BlocksTranscript
        "BLOCK label=P5 p=5 id=3 " "fixed")]

def fi24FiveWeightTrivialRowsFromTranscript : List SignatureRow :=
  [(1,
      output_line_nat
        fi24WeightsTranscript
        "SIMPLE_BLOCK id=1 " "total",
      output_line_nat
        fi24WeightsTranscript
        "SIMPLE_BLOCK id=1 " "fixed"),
   (2,
      output_line_nat
        fi24WeightsTranscript
        "SIMPLE_BLOCK id=2 " "total",
      output_line_nat
        fi24WeightsTranscript
        "SIMPLE_BLOCK id=2 " "fixed"),
   (3,
      output_line_nat
        fi24WeightsTranscript
        "SIMPLE_BLOCK id=3 " "total",
      output_line_nat
        fi24WeightsTranscript
        "SIMPLE_BLOCK id=3 " "fixed")]

theorem fi24_five_trivial_rows_are_the_transcript_rows :
    fi24FiveBrauerTrivialRowsFromTranscript = fi24FiveBrauerTrivialRows ∧
      fi24FiveWeightTrivialRowsFromTranscript = fi24FiveWeightTrivialRows := by
  decide

def fi24FiveBrauerCoverRowsFromTranscript : List CountRow :=
  [(1, output_line_nat
      fi24BlocksTranscript
      "BLOCK label=P5 p=5 id=1 " "l"),
   (2, output_line_nat
      fi24BlocksTranscript
      "BLOCK label=P5 p=5 id=2 " "l"),
   (3, output_line_nat
      fi24BlocksTranscript
      "BLOCK label=P5 p=5 id=3 " "l"),
   (45, output_line_nat
      fi24BlocksTranscript
      "BLOCK label=P5 p=5 id=45 " "l"),
   (46, output_line_nat
      fi24BlocksTranscript
      "BLOCK label=P5 p=5 id=46 " "l"),
   (47, output_line_nat
      fi24BlocksTranscript
      "BLOCK label=P5 p=5 id=47 " "l"),
   (48, output_line_nat
      fi24BlocksTranscript
      "BLOCK label=P5 p=5 id=48 " "l")]

def fi24FiveWeightCoverRowsFromTranscript : List CountRow :=
  [(1, output_line_nat
      fi24WeightsTranscript
      "COVER_BLOCK id=1 " "total"),
   (2, output_line_nat
      fi24WeightsTranscript
      "COVER_BLOCK id=2 " "total"),
   (3, output_line_nat
      fi24WeightsTranscript
      "COVER_BLOCK id=3 " "total"),
   (45, output_line_nat
      fi24WeightsTranscript
      "COVER_BLOCK id=45 " "total"),
   (46, output_line_nat
      fi24WeightsTranscript
      "COVER_BLOCK id=46 " "total"),
   (47, output_line_nat
      fi24WeightsTranscript
      "COVER_BLOCK id=47 " "total"),
   (48, output_line_nat
      fi24WeightsTranscript
      "COVER_BLOCK id=48 " "total")]

theorem fi24_five_cover_rows_are_the_transcript_rows :
    fi24FiveBrauerCoverRowsFromTranscript = fi24FiveBrauerCoverRows ∧
      fi24FiveWeightCoverRowsFromTranscript = fi24FiveWeightCoverRows := by
  decide

def fi24TwoSelectedRowsFromTranscript : List (Nat × Nat × Nat) :=
  [(output_line_nat
      fi24BlocksTranscript
      "BLOCK label=P2 p=2 id=1 " "l",
    output_line_nat
      fi24BlocksTranscript
      "BLOCK label=P2 p=2 id=1 " "fixed",
    output_line_nat
      fi24BlocksTranscript
      "BLOCK label=P2 p=2 id=1 " "free2"),
   (output_line_nat
      fi24BlocksTranscript
      "BLOCK label=P2 p=2 id=2 " "l",
    output_line_nat
      fi24BlocksTranscript
      "BLOCK label=P2 p=2 id=2 " "fixed",
    output_line_nat
      fi24BlocksTranscript
      "BLOCK label=P2 p=2 id=2 " "free2"),
   (output_line_nat
      fi24BlocksTranscript
      "BLOCK label=P2 p=2 id=3 " "l",
    output_line_nat
      fi24BlocksTranscript
      "BLOCK label=P2 p=2 id=3 " "fixed",
    output_line_nat
      fi24BlocksTranscript
      "BLOCK label=P2 p=2 id=3 " "free2")]

theorem fi24_two_selected_rows_exact :
    fi24TwoSelectedRowsFromTranscript = [(33, 25, 4), (3, 1, 1), (3, 3, 0)] := by
  decide

/-! ## `2.Sp6(2)` at three -/

def sp6OrdinaryRanksFromTranscript : List Nat := output_nat_list
  sp6Transcript
  "ORDINARY_RESTRICTION_RANKS"

def sp6BrauerRanksFromTranscript : List Nat := output_nat_list
  sp6Transcript
  "BRAUER_RANKS"

def sp6WeightCountsFromTranscript : List Nat := output_nat_list
  sp6Transcript
  "WEIGHT_COUNTS_BY_BLOCK"

theorem sp6_three_blockwise_counts_are_the_transcript_counts :
    sp6OrdinaryRanksFromTranscript = sp6BlockwiseCounts ∧
      sp6BrauerRanksFromTranscript = sp6BlockwiseCounts ∧
      sp6WeightCountsFromTranscript = sp6BlockwiseCounts := by
  decide

/-! ## Exceptional `3.O7(3)` outputs -/

def q3BlockActionFromTranscript : List Nat := output_nat_list
  o7BlocksTranscript
  "U_BLOCK_OUTER_ACTION_LIST"

def q3BrauerActionFromTranscript : List Nat := output_nat_list
  o7BlocksTranscript
  "U_BRAUER_OUTER_ACTION_LIST_RAW"

theorem q3_action_lists_are_the_transcript_lists :
    q3BlockActionFromTranscript =
        [.B1, .B2, .B3, .B4, .B5, .B6, .B7, .B8, .B9].map
          (fun block => blockPosition (blockOuterAction block)) ∧
      q3BrauerActionFromTranscript =
        allBrauerLabels.map (fun label => (brauerOuterAction label).position) := by
  constructor
  · rw [blockOuterActionList_exact]
    rfl
  · rw [brauerOuterActionList_exact]
    rfl

def q3BlockRowsFromTranscript : List BlockRowProjection :=
  output_u_block_rows o7BlocksTranscript

def q3SectorCode : Q3Sector → Nat
  | .trivial => 0
  | .faithfulOne => 1
  | .faithfulTwo => 2

def q3BlocksInTranscriptOrder : List Q3Block :=
  [.B1, .B2, .B3, .B4, .B5, .B6, .B7, .B8, .B9]

def q3BlockProjection (block : Q3Block) : BlockRowProjection where
  blockIndex := blockPosition block
  defectExponent := (blockRecord block).defectExponent
  brauerLabels := (blockRecord block).brauerLabels.map BrauerLabel.position
  sectorCode := q3SectorCode (blockRecord block).sector

/-- The nine multiline block records, including their exact central-ratio
sector encodings, are the records used by the finite certificate.  The second
equality directly checks the resulting Brauer counts and sector values against
`q3BrauerCount` and `q3Sector`. -/
theorem q3_block_rows_are_the_transcript_rows :
    q3BlockRowsFromTranscript =
        q3BlocksInTranscriptOrder.map q3BlockProjection ∧
      q3BlockRowsFromTranscript.map
          (fun row => (row.blockIndex, row.brauerLabels.length, row.sectorCode)) =
        q3BlocksInTranscriptOrder.map fun block =>
          (blockPosition block, q3BrauerCount block,
            q3SectorCode (q3Sector block)) := by
  decide

def q3BlockTwoOrdinaryLabelsFromTranscript : List Nat := output_nat_list
  o7BlockTwoTranscript
  "B2_ORDINARY_LABELS"

def q3BlockTwoDefectExponentFromTranscript : Nat := output_nat
  o7BlockTwoTranscript
  "B2_DEFECT_EXPONENT"

def q3BlockTwoDefectOrderFromTranscript : Nat := output_nat
  o7BlockTwoTranscript
  "B2_DEFECT_ORDER"

def q3BlockTwoOrdinaryCountFromTranscript : Nat := output_nat
  o7BlockTwoTranscript
  "B2_K"

def q3BlockTwoBrauerCountFromTranscript : Nat := output_nat
  o7BlockTwoTranscript
  "B2_L"

def q3BlockTwoBrauerLabelsFromTranscript : List Nat := output_nat_list
  o7BlockTwoTranscript
  "B2_IBR_LABELS"

def q3BlockTwoHeightsFromTranscript : List Nat := output_nat_list
  o7BlockTwoTranscript
  "B2_HEIGHTS"

def q3BlockTwoOrdinaryDegreesFromTranscript : List Nat := output_nat_list
  o7BlockTwoTranscript
  "B2_ORDINARY_DEGREES"

def q3BlockTwoDecompositionFromTranscript : List (List Nat) := output_nat_matrix
  o7BlockTwoTranscript
  "B2_DECOMPOSITION"

def q3BlockTwoCartanFromTranscript : List (List Nat) := output_nat_matrix
  o7BlockTwoTranscript
  "B2_CARTAN"

def q3BlockTwoCentralRatiosFromTranscript : List Nat := output_nat_list
  o7BlockTwoTranscript
  "B2_CENTRAL_RATIOS"

def q3BlockTwoOuterImageFromTranscript : List Nat := output_nat_list
  o7BlockTwoTranscript
  "B2_OUTER_IBR_IMAGE"

theorem q3_block_two_record_is_the_transcript_record :
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
        blockTwoRecord.outerBrauerImage.map BrauerLabel.position := by
  decide

def q3RadicalClassCountFromTranscript : Nat := output_nat
  o7RadicalTranscript
  "G_RADICAL_CLASS_COUNT"

def q3RadicalSearchBookkeepingFromTranscript :
    RadicalSearchBookkeepingProjection :=
  output_radical_search_bookkeeping o7RadicalTranscript

def q3SubgroupOrderMultiplicityProjection
    (row : SubgroupOrderMultiplicity) : SubgroupOrderMultiplicityProjection where
  subgroupOrder := row.subgroupOrder
  multiplicity := row.multiplicity

def q3PRadicalProjection
    (row : PRadicalRepresentative) : PRadicalRowProjection where
  pSubgroupClassIndex := row.pSubgroupClassIndex
  subgroupOrder := row.subgroupOrder
  normalizerOrder := row.normalizerOrder

def q3GFusionProjection (row : GFusionRecord) : GFusionRowProjection where
  sourcePClassIndex := row.sourcePClassIndex
  targetPClassIndex := row.targetPClassIndex

def q3RadicalSearchBookkeepingCertificate :
    RadicalSearchBookkeepingProjection where
  subgroupClassCountInSylow := radicalSearchSummary.subgroupClassCountInSylow
  subgroupOrderDistribution :=
    pSubgroupOrderDistribution.map q3SubgroupOrderMultiplicityProjection
  pRadicalRows := pRadicalRepresentatives.map q3PRadicalProjection
  pRadicalRepresentativeCount :=
    radicalSearchSummary.pRadicalRepresentativeCount
  fusionRows := gFusionRecords.map q3GFusionProjection
  gRadicalClassCount := radicalSearchSummary.gRadicalClassCount

/-- The complete numerical search and fusion bookkeeping preceding the
twelve `G_RADICAL` records is exactly the bookkeeping used by the finite
certificate.  This comparison does not certify that the GAP enumeration was
mathematically exhaustive. -/
theorem q3_radical_search_bookkeeping_is_the_transcript_bookkeeping :
    q3RadicalSearchBookkeepingFromTranscript =
      q3RadicalSearchBookkeepingCertificate := by
  decide

/-- Fieldwise form of the preceding equality.  In particular, the three
printed counts are linked both to the detailed certificate and to the compact
search record used by the manuscript arithmetic module. -/
theorem q3_radical_search_fields_are_the_typed_certificate_fields :
    q3RadicalSearchBookkeepingFromTranscript.subgroupClassCountInSylow =
        radicalSearchSummary.subgroupClassCountInSylow ∧
      q3RadicalSearchBookkeepingFromTranscript.subgroupClassCountInSylow =
        q3RadicalSearchData.tested ∧
      q3RadicalSearchBookkeepingFromTranscript.subgroupOrderDistribution =
        pSubgroupOrderDistribution.map
          q3SubgroupOrderMultiplicityProjection ∧
      q3RadicalSearchBookkeepingFromTranscript.pRadicalRows =
        pRadicalRepresentatives.map q3PRadicalProjection ∧
      q3RadicalSearchBookkeepingFromTranscript.pRadicalRepresentativeCount =
        radicalSearchSummary.pRadicalRepresentativeCount ∧
      q3RadicalSearchBookkeepingFromTranscript.pRadicalRepresentativeCount =
        q3RadicalSearchData.rawRadicalRepresentatives ∧
      q3RadicalSearchBookkeepingFromTranscript.fusionRows =
        gFusionRecords.map q3GFusionProjection ∧
      q3RadicalSearchBookkeepingFromTranscript.gRadicalClassCount =
        radicalSearchSummary.gRadicalClassCount ∧
      q3RadicalSearchBookkeepingFromTranscript.gRadicalClassCount =
        q3RadicalSearchData.fusedClasses := by
  rw [q3_radical_search_bookkeeping_is_the_transcript_bookkeeping]
  decide

def q3RadicalSectorTotalsFromTranscript : List Nat := output_nat_list
  o7RadicalTranscript
  "TOTAL_WEIGHT_COUNTS_[Z1,OMEGA,OMEGA2]"

def q3RadicalOrderContributionsFromTranscript : List (List Nat) := output_nat_matrix
  o7RadicalTranscript
  "ORDER_CONTRIBUTIONS_[QSIZE,Z1,OMEGA,OMEGA2]"

theorem q3_radical_summary_is_the_transcript_summary :
    q3RadicalClassCountFromTranscript = radicalClassContributions.length ∧
      q3RadicalSectorTotalsFromTranscript =
        [radicalSectorTotal .trivial, radicalSectorTotal .faithfulOne,
          radicalSectorTotal .faithfulTwo] ∧
      q3RadicalOrderContributionsFromTranscript =
        q3RadicalContributions.map fun row =>
          [row.subgroupOrder, row.trivial, row.faithfulOne, row.faithfulTwo] := by
  decide

def q3RadicalRowsFromTranscript : List RadicalRowProjection :=
  output_g_radical_rows o7RadicalTranscript

def q3RadicalProjection
    (row : RadicalClassContribution) : RadicalRowProjection where
  pSubgroupClassIndex := row.pSubgroupClassIndex
  subgroupOrder := row.subgroupOrder
  normalizerOrder := row.normalizerOrder
  weightQuotientOrder := row.weightQuotientOrder
  trivialLabels := row.trivialLabels
  faithfulOneLabels := row.faithfulOneLabels
  faithfulTwoLabels := row.faithfulTwoLabels

/-- All numerical and defect-zero label fields of the twelve multiline
`G_RADICAL` records are exactly those used by the finite certificate. -/
theorem q3_radical_rows_are_the_transcript_rows :
    q3RadicalRowsFromTranscript =
      radicalClassContributions.map q3RadicalProjection := by
  decide

def q3GRadicalRepresentativeIndicesDerivedFromTranscript : List Nat :=
  let fusionSources :=
    q3RadicalSearchBookkeepingFromTranscript.fusionRows.map
      GFusionRowProjection.sourcePClassIndex
  q3RadicalSearchBookkeepingFromTranscript.pRadicalRows.map
      PRadicalRowProjection.pSubgroupClassIndex |>.filter
    (fun index => !fusionSources.contains index)

/-- Removing the fourteen printed fusion sources from the 26 printed
`P_RADICAL` indices gives the twelve retained indices.  They agree both with
the certificate's retained list and with the indices on the printed
`G_RADICAL` records. -/
theorem q3_g_radical_representative_indices_are_transcript_derived :
    q3GRadicalRepresentativeIndicesDerivedFromTranscript =
        gRadicalRepresentativeIndices ∧
      q3GRadicalRepresentativeIndicesDerivedFromTranscript =
        q3RadicalRowsFromTranscript.map
          RadicalRowProjection.pSubgroupClassIndex := by
  decide

def q3LocalPrincipalWeightCountFromTranscript : Nat := output_nat
  o7WeightsTranscript
  "LOCAL_PRINCIPAL_H_WEIGHT_COUNT"

def q3Order128LocalRecordFromTranscript : List Nat :=
  [output_nat
      o7WeightsTranscript
      "P_CENTRIC_ORDER128_COUNT",
   output_nat
      o7WeightsTranscript
      "P_CENTRIC_ORDER128_S_RADICAL_COUNT",
   output_nat
      o7WeightsTranscript
      "P_CENTRIC_ORDER128_H_RADICAL_COUNT",
   output_nat
      o7WeightsTranscript
      "ORDER128_NH",
   output_nat
      o7WeightsTranscript
      "ORDER128_CH",
   output_nat
      o7WeightsTranscript
      "ORDER128_ZQ",
   output_nat
      o7WeightsTranscript
      "ORDER128_WEIGHT_QUOTIENT"]

def q3Order256LocalRecordFromTranscript : List Nat :=
  [output_nat
      o7WeightsTranscript
      "P_CENTRIC_ORDER256_COUNT",
   output_nat
      o7WeightsTranscript
      "P_CENTRIC_ORDER256_S_RADICAL_COUNT",
   output_nat
      o7WeightsTranscript
      "P_CENTRIC_ORDER256_H_RADICAL_COUNT",
   output_nat
      o7WeightsTranscript
      "ORDER256_NH",
   output_nat
      o7WeightsTranscript
      "ORDER256_CH",
   output_nat
      o7WeightsTranscript
      "ORDER256_ZQ",
   output_nat
      o7WeightsTranscript
      "ORDER256_WEIGHT_QUOTIENT"]

def q3Order128DefectZeroDegreesFromTranscript : List Nat := output_nat_list
  o7WeightsTranscript
  "ORDER128_DEFECT_ZERO_DEGREES"

def q3Order256DefectZeroDegreesFromTranscript : List Nat := output_nat_list
  o7WeightsTranscript
  "ORDER256_DEFECT_ZERO_DEGREES"

/-- The numerical fields and defect-zero degree lists of the order `128` and
`256` records are the corresponding projections of
`localPrincipalWeightRecords`.  The field names encode the two subgroup
orders.  The printed structure strings remain external transcript fields and
are neither compared here nor given a group-theoretic interpretation by this
certificate. -/
theorem q3_local_weight_records_are_the_transcript_records :
    q3LocalPrincipalWeightCountFromTranscript = localPrincipalWeightRecords.length ∧
      [q3Order128LocalRecordFromTranscript,
          q3Order256LocalRecordFromTranscript] =
        (localPrincipalWeightRecords.map fun row =>
          [row.centricClassCount, row.sRadicalRepresentativeCount,
            row.hRadicalRepresentativeCount, row.hNormalizerOrder,
            row.hCentralizerOrder, row.subgroupCentreOrder,
            row.weightQuotientOrder]) ∧
      [q3Order128DefectZeroDegreesFromTranscript,
          q3Order256DefectZeroDegreesFromTranscript] =
        localPrincipalWeightRecords.map
          LocalPrincipalWeightRecord.defectZeroDegrees := by
  decide

def q3SimplePrincipalBrauerCountsFromTranscript : List Nat :=
  [output_nat
      o7BrauerTranscript
      "S_B0_BRAUER_COUNT",
   output_nat
      o7BrauerTranscript
      "H_B0_BRAUER_COUNT",
   output_nat
      o7BrauerTranscript
      "TABLE_DECOMPOSITION_FIXED_SINGLETONS",
   output_nat
      o7BrauerTranscript
      "TABLE_DECOMPOSITION_TWO_CONSTITUENT_ROWS"]

theorem q3_simple_principal_brauer_counts_exact :
    q3SimplePrincipalBrauerCountsFromTranscript =
      [q3PrincipalIrreducibleRestrictions +
          2 * q3PrincipalSplitRestrictions,
        q3PrincipalHBrauerCount, q3PrincipalIrreducibleRestrictions,
        q3PrincipalSplitRestrictions] := by
  decide

end ModularRep.PaperProofs.ComputationTranscriptActual


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
