import Formalisation.ComputationArithmetic
import Formalisation.C2Cancellation
import Mathlib.Tactic

/-!
# Exact finite certificate for the exceptional `q = 3` outputs

This file records the finite data transcribed from `o7blocks.out`,
`o7block2.out`, `o7brauer.out`, `o7weights.out`, and `o7radical.out`, and proves the ensuing
finite partition, involution, compatibility, and counting statements.

The scope is deliberately syntactic and finite.  In particular, the
certificate does **not** prove that the constants were transcribed correctly,
that the table or permutation representation is the group `3.O7(3)`, that
GAP or its packages are correct, or that the reported block and radical
enumerations are complete.  Those claims remain the explicit E3 boundaries
listed in `unresolvedE3Boundaries`.

The transcribed triple-cover Brauer labels carry a certified finite
involution with eight fixed points and two transpositions.  The weight transcript records
only the two relevant local classes.  It does not record the externally
cited total of ten classes or the covering rule that turns those classes into
the asserted action.  Consequently the final principal-action equivalence is
proved only from an explicit external weight-action census.
-/

namespace ModularRep.ManuscriptVerification.ExceptionalQ3OutputCertificate

open Formalisation.C2Cancellation
open Formalisation.ComputationArithmetic

set_option maxRecDepth 100000

/-! ## Explicit external boundary -/

/-- Claims intentionally not discharged by this output certificate. -/
inductive E3ExternalBoundary where
  | outputTranscription
  | identificationWithTripleCover
  | gapCorrectness
  | enumerationCompleteness
  | principalWeightActionRealisation
  | restrictionLabelAlignment
  deriving DecidableEq, Repr

instance : Fintype E3ExternalBoundary := derive_fintype% E3ExternalBoundary

/-- All six selected semantic claims remain outside the finite certificate. -/
def unresolvedE3Boundaries : Finset E3ExternalBoundary := Finset.univ

theorem unresolvedE3Boundaries_card : unresolvedE3Boundaries.card = 6 := by
  decide

/-! ## Exact block and Brauer-label data -/

/-- The 33 Brauer-character positions printed by `o7blocks.out`.
Constructors use the one-based CTblLib positions. -/
inductive BrauerLabel where
  | L1 | L2 | L3 | L4 | L5 | L6 | L7 | L8 | L9 | L10 | L11
  | L12 | L13 | L14 | L15 | L16 | L17 | L18 | L19 | L20 | L21
  | L22 | L23 | L24 | L25 | L26 | L27 | L28 | L29 | L30 | L31
  | L32 | L33
  deriving DecidableEq, Repr

instance : Fintype BrauerLabel := derive_fintype% BrauerLabel

/-- Recover the printed one-based position of a Brauer label. -/
def BrauerLabel.position : BrauerLabel → ℕ
  | .L1 => 1
  | .L2 => 2
  | .L3 => 3
  | .L4 => 4
  | .L5 => 5
  | .L6 => 6
  | .L7 => 7
  | .L8 => 8
  | .L9 => 9
  | .L10 => 10
  | .L11 => 11
  | .L12 => 12
  | .L13 => 13
  | .L14 => 14
  | .L15 => 15
  | .L16 => 16
  | .L17 => 17
  | .L18 => 18
  | .L19 => 19
  | .L20 => 20
  | .L21 => 21
  | .L22 => 22
  | .L23 => 23
  | .L24 => 24
  | .L25 => 25
  | .L26 => 26
  | .L27 => 27
  | .L28 => 28
  | .L29 => 29
  | .L30 => 30
  | .L31 => 31
  | .L32 => 32
  | .L33 => 33

def allBrauerLabels : List BrauerLabel :=
  [.L1, .L2, .L3, .L4, .L5, .L6, .L7, .L8, .L9, .L10, .L11,
   .L12, .L13, .L14, .L15, .L16, .L17, .L18, .L19, .L20, .L21,
   .L22, .L23, .L24, .L25, .L26, .L27, .L28, .L29, .L30, .L31,
   .L32, .L33]

theorem allBrauerLabels_exact :
    allBrauerLabels.Nodup ∧ allBrauerLabels.toFinset = Finset.univ := by
  decide

/-- The fields used in the manuscript block table, recorded without any
claim that the printed table has the asserted group-theoretic meaning. -/
structure BlockRecord where
  block : Q3Block
  defectExponent : ℕ
  brauerLabels : List BrauerLabel
  sector : Q3Sector
  deriving DecidableEq, Repr

def blockRecord : Q3Block → BlockRecord
  | .B1 => ⟨.B1, 9,
      [.L1, .L2, .L3, .L4, .L5, .L6, .L7, .L8, .L9, .L10, .L11, .L12],
      .trivial⟩
  | .B2 => ⟨.B2, 3, [.L13, .L14], .trivial⟩
  | .B3 => ⟨.B3, 1, [.L15], .trivial⟩
  | .B4 => ⟨.B4, 0, [.L16], .trivial⟩
  | .B5 => ⟨.B5, 0, [.L17], .trivial⟩
  | .B6 => ⟨.B6, 9, [.L18, .L20, .L24, .L26, .L28, .L30], .faithfulOne⟩
  | .B7 => ⟨.B7, 9, [.L19, .L21, .L25, .L27, .L29, .L31], .faithfulTwo⟩
  | .B8 => ⟨.B8, 3, [.L22, .L32], .faithfulOne⟩
  | .B9 => ⟨.B9, 3, [.L23, .L33], .faithfulTwo⟩

def blockRecords : List BlockRecord :=
  [blockRecord .B1, blockRecord .B2, blockRecord .B3,
   blockRecord .B4, blockRecord .B5, blockRecord .B6,
   blockRecord .B7, blockRecord .B8, blockRecord .B9]

/-- The exact block fibre of each printed Brauer position. -/
def blockOfBrauerLabel : BrauerLabel → Q3Block
  | .L1 | .L2 | .L3 | .L4 | .L5 | .L6
  | .L7 | .L8 | .L9 | .L10 | .L11 | .L12 => .B1
  | .L13 | .L14 => .B2
  | .L15 => .B3
  | .L16 => .B4
  | .L17 => .B5
  | .L18 | .L20 | .L24 | .L26 | .L28 | .L30 => .B6
  | .L19 | .L21 | .L25 | .L27 | .L29 | .L31 => .B7
  | .L22 | .L32 => .B8
  | .L23 | .L33 => .B9

theorem blockRecords_exactly_nine : blockRecords.length = 9 := by
  decide

theorem blockRecords_cover_blocks_once :
    (blockRecords.map BlockRecord.block).Nodup ∧
      (blockRecords.map BlockRecord.block).toFinset = Finset.univ := by
  decide

/-- The nine record fibres are a disjoint and exhaustive partition of all
33 printed Brauer labels. -/
theorem blockRecords_partition_allBrauerLabels :
    (blockRecords.flatMap BlockRecord.brauerLabels).Nodup ∧
      (blockRecords.flatMap BlockRecord.brauerLabels).toFinset = Finset.univ := by
  decide

theorem brauerLabel_mem_blockRecord_iff (label : BrauerLabel) (block : Q3Block) :
    label ∈ (blockRecord block).brauerLabels ↔ blockOfBrauerLabel label = block := by
  cases label <;> cases block <;> decide

theorem blockRecord_brauerCount (block : Q3Block) :
    (blockRecord block).brauerLabels.length = q3BrauerCount block := by
  cases block <;> decide

theorem blockRecord_sector (block : Q3Block) :
    (blockRecord block).sector = q3Sector block := by
  cases block <;> rfl

/-! ## Exact `o7block2.out` data -/

/-- The finite block-two record printed by `o7block2.out`.  As elsewhere in
this file, the record has no group-theoretic meaning until the transcript and
table identifications have been supplied externally. -/
structure BlockTwoRecord where
  defectExponent : ℕ
  defectOrder : ℕ
  ordinaryCharacterCount : ℕ
  brauerCharacterCount : ℕ
  ordinaryLabels : List ℕ
  brauerLabels : List BrauerLabel
  ordinaryDegrees : List ℕ
  heights : List ℕ
  decompositionMatrix : List (List ℕ)
  cartanMatrix : List (List ℕ)
  centralRatios : List ℕ
  outerBrauerImage : List BrauerLabel
  deriving DecidableEq, Repr

def blockTwoRecord : BlockTwoRecord where
  defectExponent := 3
  defectOrder := 8
  ordinaryCharacterCount := 5
  brauerCharacterCount := 2
  ordinaryLabels := [36, 37, 47, 52, 53]
  brauerLabels := [.L13, .L14]
  ordinaryDegrees := [5824, 5824, 11648, 17472, 17472]
  heights := [0, 0, 1, 0, 0]
  decompositionMatrix := [[1, 0], [1, 0], [0, 1], [1, 1], [1, 1]]
  cartanMatrix := [[4, 2], [2, 3]]
  centralRatios := [1, 1, 1]
  outerBrauerImage := [.L13, .L14]

theorem blockTwoRecord_internal_dimensions :
    blockTwoRecord.defectOrder = 2 ^ blockTwoRecord.defectExponent ∧
      blockTwoRecord.ordinaryLabels.length =
        blockTwoRecord.ordinaryCharacterCount ∧
      blockTwoRecord.ordinaryDegrees.length =
        blockTwoRecord.ordinaryCharacterCount ∧
      blockTwoRecord.heights.length = blockTwoRecord.ordinaryCharacterCount ∧
      blockTwoRecord.decompositionMatrix.length =
        blockTwoRecord.ordinaryCharacterCount ∧
      (∀ row ∈ blockTwoRecord.decompositionMatrix,
        row.length = blockTwoRecord.brauerCharacterCount) ∧
      blockTwoRecord.brauerLabels.length =
        blockTwoRecord.brauerCharacterCount := by
  decide

theorem blockTwoRecord_matches_blockRecord :
    blockTwoRecord.defectExponent = (blockRecord .B2).defectExponent ∧
      blockTwoRecord.brauerLabels = (blockRecord .B2).brauerLabels := by
  decide

theorem blockTwoRecord_heightDistribution :
    blockTwoRecord.heights.count 0 = 4 ∧
      blockTwoRecord.heights.count 1 = 1 := by
  decide

def listMatrixGramEntry (matrix : List (List ℕ)) (i j : ℕ) : ℕ :=
  (matrix.map fun row => row.getD i 0 * row.getD j 0).sum

def listMatrixGramTwo (matrix : List (List ℕ)) : List (List ℕ) :=
  [[listMatrixGramEntry matrix 0 0, listMatrixGramEntry matrix 0 1],
   [listMatrixGramEntry matrix 1 0, listMatrixGramEntry matrix 1 1]]

/-- The printed Cartan matrix is the Gram matrix `D^T D` of the transcribed
decomposition matrix. -/
theorem blockTwoRecord_cartan_eq_gram :
    blockTwoRecord.cartanMatrix =
      listMatrixGramTwo blockTwoRecord.decompositionMatrix := by
  decide

/-- The printed block involution `(B6 B7)(B8 B9)`. -/
def blockOuterAction : Equiv.Perm Q3Block := q3OuterBlockAction

def blockPosition : Q3Block → ℕ
  | .B1 => 1
  | .B2 => 2
  | .B3 => 3
  | .B4 => 4
  | .B5 => 5
  | .B6 => 6
  | .B7 => 7
  | .B8 => 8
  | .B9 => 9

theorem blockOuterActionList_exact :
    ([.B1, .B2, .B3, .B4, .B5, .B6, .B7, .B8, .B9].map
      (fun block => blockPosition (blockOuterAction block))) =
        [1, 2, 3, 4, 5, 7, 6, 9, 8] := by
  decide

theorem blockOuterAction_involutive : Function.Involutive blockOuterAction :=
  q3_outer_block_action_involutive

/-- The exact Brauer-label involution printed in `o7blocks.out`. -/
def brauerOuterAction : Equiv.Perm BrauerLabel where
  toFun
    | .L5 => .L6
    | .L6 => .L5
    | .L11 => .L12
    | .L12 => .L11
    | .L18 => .L19
    | .L19 => .L18
    | .L20 => .L21
    | .L21 => .L20
    | .L22 => .L23
    | .L23 => .L22
    | .L24 => .L25
    | .L25 => .L24
    | .L26 => .L27
    | .L27 => .L26
    | .L28 => .L29
    | .L29 => .L28
    | .L30 => .L31
    | .L31 => .L30
    | .L32 => .L33
    | .L33 => .L32
    | label => label
  invFun
    | .L5 => .L6
    | .L6 => .L5
    | .L11 => .L12
    | .L12 => .L11
    | .L18 => .L19
    | .L19 => .L18
    | .L20 => .L21
    | .L21 => .L20
    | .L22 => .L23
    | .L23 => .L22
    | .L24 => .L25
    | .L25 => .L24
    | .L26 => .L27
    | .L27 => .L26
    | .L28 => .L29
    | .L29 => .L28
    | .L30 => .L31
    | .L31 => .L30
    | .L32 => .L33
    | .L33 => .L32
    | label => label
  left_inv label := by cases label <;> rfl
  right_inv label := by cases label <;> rfl

theorem brauerOuterActionList_exact :
    (allBrauerLabels.map (fun label => (brauerOuterAction label).position)) =
      [1, 2, 3, 4, 6, 5, 7, 8, 9, 10, 12, 11, 13, 14, 15, 16, 17,
       19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30, 33, 32] := by
  decide

theorem brauerOuterAction_involutive : Function.Involutive brauerOuterAction := by
  intro label
  cases label <;> rfl

theorem blockTwoRecord_outerBrauerImage_exact :
    blockTwoRecord.outerBrauerImage =
      blockTwoRecord.brauerLabels.map brauerOuterAction := by
  decide

/-- The induced exchange of the two faithful central character sectors. -/
def sectorOuterAction : Equiv.Perm Q3Sector where
  toFun
    | .trivial => .trivial
    | .faithfulOne => .faithfulTwo
    | .faithfulTwo => .faithfulOne
  invFun
    | .trivial => .trivial
    | .faithfulOne => .faithfulTwo
    | .faithfulTwo => .faithfulOne
  left_inv sector := by cases sector <;> rfl
  right_inv sector := by cases sector <;> rfl

theorem sectorOuterAction_involutive : Function.Involutive sectorOuterAction := by
  intro sector
  cases sector <;> rfl

/-- The printed Brauer involution maps every block fibre onto the fibre of
the printed image block. -/
theorem brauer_block_action_compatible (label : BrauerLabel) :
    blockOfBrauerLabel (brauerOuterAction label) =
      blockOuterAction (blockOfBrauerLabel label) := by
  cases label <;> rfl

theorem block_sector_action_compatible (block : Q3Block) :
    (blockRecord (blockOuterAction block)).sector =
      sectorOuterAction (blockRecord block).sector := by
  cases block <;> rfl

theorem brauer_sector_action_compatible (label : BrauerLabel) :
    (blockRecord (blockOfBrauerLabel (brauerOuterAction label))).sector =
      sectorOuterAction (blockRecord (blockOfBrauerLabel label)).sector := by
  rw [brauer_block_action_compatible, block_sector_action_compatible]

theorem blockFibres_action_compatible (block : Q3Block) :
    ((blockRecord block).brauerLabels.map brauerOuterAction).toFinset =
      (blockRecord (blockOuterAction block)).brauerLabels.toFinset := by
  cases block <;> decide

/-! ## Raw radical-search and fusion data -/

structure SubgroupOrderMultiplicity where
  subgroupOrder : ℕ
  multiplicity : ℕ
  deriving DecidableEq, Repr

def pSubgroupOrderDistribution : List SubgroupOrderMultiplicity :=
  [⟨1, 1⟩, ⟨2, 28⟩, ⟨4, 230⟩, ⟨8, 720⟩, ⟨16, 999⟩,
   ⟨32, 673⟩, ⟨64, 279⟩, ⟨128, 75⟩, ⟨256, 15⟩, ⟨512, 1⟩]

theorem pSubgroupOrderDistribution_total :
    (pSubgroupOrderDistribution.map
      SubgroupOrderMultiplicity.multiplicity).sum = 3021 := by
  decide

/-- One raw `P_RADICAL` row.  Here `P` is the Sylow subgroup used by the GAP
search, so the index is a conjugacy class index inside `P`, not a Sylow-class
index in the ambient group. -/
structure PRadicalRepresentative where
  pSubgroupClassIndex : ℕ
  subgroupOrder : ℕ
  normalizerOrder : ℕ
  deriving DecidableEq, Repr

def pRadicalRepresentatives : List PRadicalRepresentative :=
  [⟨1, 1, 13756055040⟩,
   ⟨3, 2, 39191040⟩, ⟨16, 2, 39191040⟩, ⟨29, 2, 39191040⟩,
   ⟨36, 4, 51840⟩, ⟨47, 4, 622080⟩, ⟨94, 4, 51840⟩,
   ⟨98, 4, 51840⟩, ⟨110, 4, 622080⟩, ⟨116, 4, 51840⟩,
   ⟨132, 4, 622080⟩, ⟨190, 4, 622080⟩, ⟨192, 4, 622080⟩,
   ⟨211, 4, 622080⟩, ⟨242, 4, 51840⟩,
   ⟨337, 8, 17280⟩, ⟨720, 8, 17280⟩, ⟨787, 8, 17280⟩,
   ⟨960, 8, 17280⟩, ⟨2101, 32, 69120⟩, ⟨2676, 64, 483840⟩,
   ⟨2946, 128, 41472⟩, ⟨3007, 256, 4608⟩,
   ⟨3017, 256, 4608⟩, ⟨3019, 256, 13824⟩,
   ⟨3021, 512, 1536⟩]

theorem pRadicalRepresentatives_exactly_twentySix :
    pRadicalRepresentatives.length = 26 := by
  decide

theorem pRadicalRepresentativeIndices_nodup :
    (pRadicalRepresentatives.map
      PRadicalRepresentative.pSubgroupClassIndex).Nodup := by
  decide

/-- Lookup in the finite `P_RADICAL` transcript.  The zero row is used only
outside the printed index set; the consistency theorems below also certify
that every index they query is present. -/
def lookupPRadicalRepresentativeIn (index : ℕ) :
    List PRadicalRepresentative → PRadicalRepresentative
  | [] => ⟨0, 0, 0⟩
  | row :: rows =>
      if row.pSubgroupClassIndex = index then row
      else lookupPRadicalRepresentativeIn index rows

def pRadicalRepresentativeAt (index : ℕ) : PRadicalRepresentative :=
  lookupPRadicalRepresentativeIn index pRadicalRepresentatives

structure GFusionRecord where
  sourcePClassIndex : ℕ
  targetPClassIndex : ℕ
  deriving DecidableEq, Repr

def gFusionRecords : List GFusionRecord :=
  [⟨16, 3⟩, ⟨29, 3⟩, ⟨94, 36⟩, ⟨98, 36⟩, ⟨110, 47⟩,
   ⟨116, 36⟩, ⟨132, 47⟩, ⟨190, 47⟩, ⟨192, 47⟩,
   ⟨211, 47⟩, ⟨242, 36⟩, ⟨720, 337⟩, ⟨787, 337⟩,
   ⟨960, 337⟩]

def gRadicalRepresentativeIndices : List ℕ :=
  [1, 3, 36, 47, 337, 2101, 2676, 2946, 3007, 3017, 3019, 3021]

theorem gFusionRecords_exactly_fourteen : gFusionRecords.length = 14 := by
  decide

theorem gFusionSources_nodup :
    (gFusionRecords.map GFusionRecord.sourcePClassIndex).Nodup := by
  decide

theorem gFusionTargets_are_representatives :
    ∀ row ∈ gFusionRecords,
      row.targetPClassIndex ∈ gRadicalRepresentativeIndices := by
  decide

/-- Every printed fusion source and target has the same subgroup order and
normaliser order in the raw radical transcript. -/
theorem gFusion_source_target_orders_agree :
    ∀ row ∈ gFusionRecords,
      let source := pRadicalRepresentativeAt row.sourcePClassIndex
      let target := pRadicalRepresentativeAt row.targetPClassIndex
      source.pSubgroupClassIndex = row.sourcePClassIndex ∧
        target.pSubgroupClassIndex = row.targetPClassIndex ∧
        source.subgroupOrder = target.subgroupOrder ∧
        source.normalizerOrder = target.normalizerOrder := by
  decide

/-- The fourteen fused sources and twelve retained representatives form a
disjoint exhaustive partition of the 26 printed `P_RADICAL` indices.  This
checks the transcript's finite bookkeeping, not the mathematical correctness
of the fusion calculation. -/
theorem gFusion_partition_pRadicalIndices :
    ((gFusionRecords.map GFusionRecord.sourcePClassIndex) ++
      gRadicalRepresentativeIndices).Nodup ∧
    (((gFusionRecords.map GFusionRecord.sourcePClassIndex) ++
      gRadicalRepresentativeIndices).toFinset =
        (pRadicalRepresentatives.map
          PRadicalRepresentative.pSubgroupClassIndex).toFinset) := by
  decide

/-! ## Twelve fused radical-class rows -/

/-- One `G_RADICAL` output row.  The two structure fields are retained as
literal printed strings; no group identification is inferred from them. -/
structure RadicalClassContribution where
  pSubgroupClassIndex : ℕ
  subgroupOrder : ℕ
  subgroupStructure : String
  normalizerOrder : ℕ
  weightQuotientOrder : ℕ
  weightQuotientStructure : String
  trivialLabels : List ℕ
  faithfulOneLabels : List ℕ
  faithfulTwoLabels : List ℕ
  deriving DecidableEq, Repr

def RadicalClassContribution.labels
    (row : RadicalClassContribution) : Q3Sector → List ℕ
  | .trivial => row.trivialLabels
  | .faithfulOne => row.faithfulOneLabels
  | .faithfulTwo => row.faithfulTwoLabels

def RadicalClassContribution.count
    (row : RadicalClassContribution) (sector : Q3Sector) : ℕ :=
  (row.labels sector).length

def radicalClassContributions : List RadicalClassContribution :=
  [ { pSubgroupClassIndex := 1
      subgroupOrder := 1
      subgroupStructure := "1"
      normalizerOrder := 13756055040
      weightQuotientOrder := 13756055040
      weightQuotientStructure := "3.O7(3)"
      trivialLabels := [54, 55]
      faithfulOneLabels := []
      faithfulTwoLabels := [] },
    { pSubgroupClassIndex := 3
      subgroupOrder := 2
      subgroupStructure := "C2"
      normalizerOrder := 39191040
      weightQuotientOrder := 19595520
      weightQuotientStructure := "(C3 . PSU(4,3)) : C2"
      trivialLabels := [92]
      faithfulOneLabels := []
      faithfulTwoLabels := [] },
    { pSubgroupClassIndex := 36
      subgroupOrder := 4
      subgroupStructure := "C2 x C2"
      normalizerOrder := 51840
      weightQuotientOrder := 12960
      weightQuotientStructure := "C3 x S3 x S6"
      trivialLabels := [97]
      faithfulOneLabels := [98]
      faithfulTwoLabels := [99] },
    { pSubgroupClassIndex := 47
      subgroupOrder := 4
      subgroupStructure := "C2 x C2"
      normalizerOrder := 622080
      weightQuotientOrder := 155520
      weightQuotientStructure := "C3 x (O(5,3) : C2)"
      trivialLabels := []
      faithfulOneLabels := []
      faithfulTwoLabels := [] },
    { pSubgroupClassIndex := 337
      subgroupOrder := 8
      subgroupStructure := "D8"
      normalizerOrder := 17280
      weightQuotientOrder := 2160
      weightQuotientStructure := "C3 x S6"
      trivialLabels := [31]
      faithfulOneLabels := [33]
      faithfulTwoLabels := [32] },
    { pSubgroupClassIndex := 2101
      subgroupOrder := 32
      subgroupStructure := "C2 x C2 x C2 x C2 x C2"
      normalizerOrder := 69120
      weightQuotientOrder := 2160
      weightQuotientStructure := "C3 x S6"
      trivialLabels := [31]
      faithfulOneLabels := [32]
      faithfulTwoLabels := [33] },
    { pSubgroupClassIndex := 2676
      subgroupOrder := 64
      subgroupStructure := "C2 x C2 x C2 x C2 x C2 x C2"
      normalizerOrder := 483840
      weightQuotientOrder := 7560
      weightQuotientStructure := "C3 . A7"
      trivialLabels := []
      faithfulOneLabels := [19, 20]
      faithfulTwoLabels := [21, 22] },
    { pSubgroupClassIndex := 2946
      subgroupOrder := 128
      subgroupStructure := "C2 x C2 x ((C2 x C2 x C2) : (C2 x C2))"
      normalizerOrder := 41472
      weightQuotientOrder := 324
      weightQuotientStructure := "(((C3 x C3) : C3) : C2) x S3"
      trivialLabels := [13, 16, 17, 18]
      faithfulOneLabels := []
      faithfulTwoLabels := [] },
    { pSubgroupClassIndex := 3007
      subgroupOrder := 256
      subgroupStructure := "((C2 x ((C2 x C2 x C2 x C2) : C2)) : C2) : C2"
      normalizerOrder := 4608
      weightQuotientOrder := 18
      weightQuotientStructure := "C3 x S3"
      trivialLabels := [7]
      faithfulOneLabels := [9]
      faithfulTwoLabels := [8] },
    { pSubgroupClassIndex := 3017
      subgroupOrder := 256
      subgroupStructure := "(C2 x (((C2 x C2 x C2 x C2) : C2) : C2)) : C2"
      normalizerOrder := 4608
      weightQuotientOrder := 18
      weightQuotientStructure := "C3 x S3"
      trivialLabels := [7]
      faithfulOneLabels := [8]
      faithfulTwoLabels := [9] },
    { pSubgroupClassIndex := 3019
      subgroupOrder := 256
      subgroupStructure := "C2 x C2 x (((C2 x C2 x C2 x C2) : C2) : C2)"
      normalizerOrder := 13824
      weightQuotientOrder := 54
      weightQuotientStructure := "((C3 x C3) : C3) : C2"
      trivialLabels := [3, 4, 5, 6]
      faithfulOneLabels := []
      faithfulTwoLabels := [] },
    { pSubgroupClassIndex := 3021
      subgroupOrder := 512
      subgroupStructure := "((C2 x (((C8 : C2) : C2) : C2)) : C2) : C2"
      normalizerOrder := 1536
      weightQuotientOrder := 3
      weightQuotientStructure := "C3"
      trivialLabels := [1]
      faithfulOneLabels := [3]
      faithfulTwoLabels := [2] } ]

theorem radicalClassContributions_exactly_twelve :
    radicalClassContributions.length = 12 := by
  decide

theorem radicalClassIndices_nodup :
    (radicalClassContributions.map
      RadicalClassContribution.pSubgroupClassIndex).Nodup := by
  decide

theorem radicalClassIndices_exact :
    radicalClassContributions.map
      RadicalClassContribution.pSubgroupClassIndex =
        [1, 3, 36, 47, 337, 2101, 2676, 2946, 3007, 3017, 3019, 3021] := by
  decide

/-- Each retained `G_RADICAL` row has the subgroup and normaliser orders of
the raw `P_RADICAL` row with the same printed index. -/
theorem radicalClasses_match_raw_orders :
    ∀ row ∈ radicalClassContributions,
      let raw := pRadicalRepresentativeAt row.pSubgroupClassIndex
      raw.pSubgroupClassIndex = row.pSubgroupClassIndex ∧
        raw.subgroupOrder = row.subgroupOrder ∧
        raw.normalizerOrder = row.normalizerOrder := by
  decide

/-- Each printed quotient order satisfies `|Q| * wsize = nsize`. -/
theorem radicalClass_quotientOrder_arithmetic :
    ∀ row ∈ radicalClassContributions,
      row.subgroupOrder * row.weightQuotientOrder = row.normalizerOrder := by
  decide

def radicalSectorTotal (sector : Q3Sector) : ℕ :=
  (radicalClassContributions.map fun row => row.count sector).sum

theorem radicalSectorTotals_exact :
    radicalSectorTotal .trivial = 17 ∧
      radicalSectorTotal .faithfulOne = 8 ∧
      radicalSectorTotal .faithfulTwo = 8 := by
  decide

/-- Re-aggregate the twelve class rows in the order used by the transcript's
nine `ORDER_CONTRIBUTIONS` rows. -/
def radicalContributionOrders : List ℕ := [512, 256, 128, 64, 32, 8, 4, 2, 1]

def radicalContributionAtOrder (order : ℕ) : Q3RadicalContribution where
  subgroupOrder := order
  trivial := ((radicalClassContributions.filter
    (fun row => row.subgroupOrder = order)).map
      (fun row => row.count .trivial)).sum
  faithfulOne := ((radicalClassContributions.filter
    (fun row => row.subgroupOrder = order)).map
      (fun row => row.count .faithfulOne)).sum
  faithfulTwo := ((radicalClassContributions.filter
    (fun row => row.subgroupOrder = order)).map
      (fun row => row.count .faithfulTwo)).sum

def radicalOrderContributionsFromClasses : List Q3RadicalContribution :=
  radicalContributionOrders.map radicalContributionAtOrder

theorem radicalClasses_aggregate_to_orderContributions :
    radicalOrderContributionsFromClasses = q3RadicalContributions := by
  decide

def blockBrauerSectorTotal (sector : Q3Sector) : ℕ :=
  ((blockRecords.filter (fun row => row.sector = sector)).map
    (fun row => row.brauerLabels.length)).sum

theorem blockBrauerSectorTotals_exact :
    blockBrauerSectorTotal .trivial = 17 ∧
      blockBrauerSectorTotal .faithfulOne = 8 ∧
      blockBrauerSectorTotal .faithfulTwo = 8 := by
  decide

/-- This is only equality of the two finite output totals; it does not assert
the Alperin weight conjecture or identify either list with mathematical
objects outside the transcripts. -/
theorem radical_and_block_sectorTotals_agree (sector : Q3Sector) :
    radicalSectorTotal sector = blockBrauerSectorTotal sector := by
  cases sector <;> decide

/-! ## The two local records printed by `o7weights.out` -/

/-- One of the two subgroup-order records used by the local principal-weight
output.  The structure description is retained as a literal string and has
no certified semantic interpretation here. -/
structure LocalPrincipalWeightRecord where
  subgroupOrder : ℕ
  centricClassCount : ℕ
  sRadicalRepresentativeCount : ℕ
  hRadicalRepresentativeCount : ℕ
  hNormalizerOrder : ℕ
  hCentralizerOrder : ℕ
  subgroupCentreOrder : ℕ
  weightQuotientOrder : ℕ
  weightQuotientStructure : String
  defectZeroDegrees : List ℕ
  deriving DecidableEq, Repr

def localPrincipalWeightRecords : List LocalPrincipalWeightRecord :=
  [ { subgroupOrder := 128
      centricClassCount := 53
      sRadicalRepresentativeCount := 1
      hRadicalRepresentativeCount := 1
      hNormalizerOrder := 27648
      hCentralizerOrder := 8
      subgroupCentreOrder := 8
      weightQuotientOrder := 216
      weightQuotientStructure := "S3 x S3 x S3"
      defectZeroDegrees := [8] },
    { subgroupOrder := 256
      centricClassCount := 15
      sRadicalRepresentativeCount := 3
      hRadicalRepresentativeCount := 1
      hNormalizerOrder := 9216
      hCentralizerOrder := 8
      subgroupCentreOrder := 8
      weightQuotientOrder := 36
      weightQuotientStructure := "S3 x S3"
      defectZeroDegrees := [4] } ]

theorem localPrincipalWeightRecords_exactly_two :
    localPrincipalWeightRecords.length = 2 := by
  decide

theorem localPrincipalWeightRecords_quotientArithmetic :
    ∀ row ∈ localPrincipalWeightRecords,
      row.subgroupOrder * row.weightQuotientOrder = row.hNormalizerOrder := by
  decide

theorem localPrincipalWeightRecords_centralizer_eq_centre :
    ∀ row ∈ localPrincipalWeightRecords,
      row.hCentralizerOrder = row.subgroupCentreOrder := by
  decide

theorem localPrincipalWeightRecords_one_hRadicalRepresentative_each :
    ∀ row ∈ localPrincipalWeightRecords,
      row.hRadicalRepresentativeCount = 1 := by
  decide

theorem localPrincipalWeightRecords_search_counts :
    localPrincipalWeightRecords.map
      (fun row => (row.centricClassCount,
        row.sRadicalRepresentativeCount)) = [(53, 1), (15, 3)] := by
  decide

theorem localPrincipalWeightRecords_one_defectZeroDegree_each :
    ∀ row ∈ localPrincipalWeightRecords, row.defectZeroDegrees.length = 1 := by
  decide

theorem localPrincipalWeightRecords_defectZeroDegree_total :
    (localPrincipalWeightRecords.map
      (fun row => row.defectZeroDegrees.length)).sum = 2 := by
  decide

/-- For each printed defect-zero degree, division removes the full `2`-part
of the printed quotient order. -/
theorem localPrincipalWeightRecords_defectZero_fullTwoPart :
    ∀ row ∈ localPrincipalWeightRecords,
      ∀ degree ∈ row.defectZeroDegrees,
        degree ∣ row.weightQuotientOrder ∧
          Odd (row.weightQuotientOrder / degree) ∧
          (degree = 4 ∨ degree = 8) := by
  decide

/-- The search and fusion counts are recorded, but the equality with the
length of the explicit list is not a completeness proof. -/
structure RadicalSearchSummary where
  subgroupClassCountInSylow : ℕ
  pRadicalRepresentativeCount : ℕ
  gRadicalClassCount : ℕ
  deriving DecidableEq, Repr

def radicalSearchSummary : RadicalSearchSummary where
  subgroupClassCountInSylow := 3021
  pRadicalRepresentativeCount := 26
  gRadicalClassCount := 12

theorem radicalRows_match_reported_fusedCount :
    radicalClassContributions.length = radicalSearchSummary.gRadicalClassCount := by
  decide

/-! ## Principal restriction rows and the cover involution -/

/-- The twelve Brauer positions of the simple-group table used by
`o7brauer.out`.  This is deliberately a different type from `BrauerLabel`:
aligning these positions with the triple-cover labels is an external semantic
bridge, not a consequence of equal printed integers. -/
inductive SimplePrincipalBrauerLabel where
  | L1 | L2 | L3 | L4 | L5 | L6 | L7 | L8 | L9 | L10 | L11 | L12
  deriving DecidableEq, Repr

instance : Fintype SimplePrincipalBrauerLabel :=
  derive_fintype% SimplePrincipalBrauerLabel

def allSimplePrincipalBrauerLabels : List SimplePrincipalBrauerLabel :=
  [.L1, .L2, .L3, .L4, .L5, .L6, .L7, .L8, .L9, .L10, .L11, .L12]

/-- The ten rows printed by `o7brauer.out`, retained on their own label type. -/
def principalBrauerRestrictionRows : List (List SimplePrincipalBrauerLabel) :=
  [[.L1], [.L2], [.L3], [.L4], [.L5, .L6], [.L7], [.L8], [.L9],
   [.L10], [.L11, .L12]]

theorem principalBrauerRestrictionRows_partition :
    principalBrauerRestrictionRows.flatten =
      allSimplePrincipalBrauerLabels := by
  rfl

theorem principalBrauerRestrictionRows_shape :
    (principalBrauerRestrictionRows.map List.length).count 1 = 8 ∧
      (principalBrauerRestrictionRows.map List.length).count 2 = 2 := by
  decide

/-- The formal permutation that fixes each singleton restriction row and
swaps the two entries in each two-element row.  Identifying this permutation
with the `H/S` action uses modular Clifford theory and is external to this
certificate. -/
def simplePrincipalOuterAction : Equiv.Perm SimplePrincipalBrauerLabel where
  toFun
    | .L5 => .L6
    | .L6 => .L5
    | .L11 => .L12
    | .L12 => .L11
    | label => label
  invFun
    | .L5 => .L6
    | .L6 => .L5
    | .L11 => .L12
    | .L12 => .L11
    | label => label
  left_inv label := by cases label <;> rfl
  right_inv label := by cases label <;> rfl

theorem principalBrauerRestrictionRows_action_stable :
    ∀ row ∈ principalBrauerRestrictionRows,
      (row.map simplePrincipalOuterAction).toFinset = row.toFinset := by
  decide

theorem simplePrincipalOuterAction_involutive :
    Function.Involutive simplePrincipalOuterAction := by
  intro label
  cases label <;> rfl

theorem simplePrincipal_action_signature :
    (Fintype.card SimplePrincipalBrauerLabel,
      Fintype.card (Function.fixedPoints simplePrincipalOuterAction)) =
        (12, 8) := by
  decide

abbrev PrincipalBrauerLabel :=
  { label : BrauerLabel // blockOfBrauerLabel label = .B1 }

theorem brauerOuterAction_preserves_principal (label : PrincipalBrauerLabel) :
    blockOfBrauerLabel (brauerOuterAction label.1) = .B1 := by
  rw [brauer_block_action_compatible, label.2]
  rfl

/-- The transcribed permutation on the twelve principal triple-cover labels. -/
def principalBrauerOuterAction : Equiv.Perm PrincipalBrauerLabel where
  toFun label :=
    ⟨brauerOuterAction label.1, brauerOuterAction_preserves_principal label⟩
  invFun label :=
    ⟨brauerOuterAction label.1, brauerOuterAction_preserves_principal label⟩
  left_inv label := by
    apply Subtype.ext
    exact brauerOuterAction_involutive label.1
  right_inv label := by
    apply Subtype.ext
    exact brauerOuterAction_involutive label.1

theorem principalBrauerOuterAction_involutive :
    Function.Involutive principalBrauerOuterAction := by
  intro label
  apply Subtype.ext
  exact brauerOuterAction_involutive label.1

theorem principalBrauerLabel_card : Fintype.card PrincipalBrauerLabel = 12 := by
  decide

theorem principalBrauer_fixed_card :
    Fintype.card (Function.fixedPoints principalBrauerOuterAction) = 8 := by
  decide

/-- The finite signature of the transcribed principal triple-cover label
permutation: twelve labels, of which eight are fixed. -/
theorem principalBrauer_action_signature :
    (Fintype.card PrincipalBrauerLabel,
      Fintype.card (Function.fixedPoints principalBrauerOuterAction)) = (12, 8) := by
  exact Prod.ext principalBrauerLabel_card principalBrauer_fixed_card

/-- The missing semantic bridge between the simple-table positions in
`o7brauer.out` and the principal triple-cover positions in `o7blocks.out`.
No such bridge is constructed by this finite certificate. -/
structure PrincipalRestrictionAlignmentInput where
  labelEquiv : SimplePrincipalBrauerLabel ≃ PrincipalBrauerLabel
  intertwines : ∀ label,
    labelEquiv (simplePrincipalOuterAction label) =
      principalBrauerOuterAction (labelEquiv label)

/-- Additional weight-side information needed to obtain the manuscript's
principal `C2`-set equivalence.  This is an explicit external input because
the archived weight output itself prints only the two local classes. -/
structure ExternalPrincipalWeightActionInput
    (WeightLabel : Type*) [Fintype WeightLabel] [DecidableEq WeightLabel]
    (weightAction : Equiv.Perm WeightLabel) : Prop where
  involutive : Function.Involutive weightAction
  card_eq : Fintype.card WeightLabel = 12
  fixed_card_eq :
    Fintype.card (Function.fixedPoints weightAction) = 8

/-- Once the missing weight census is supplied explicitly, the classification
of finite involutions constructs an equivariant equivalence from the
simple-table restriction labels. -/
theorem exists_simplePrincipalC2Set_equivalence_of_external_weight_input
    {WeightLabel : Type*} [Fintype WeightLabel] [DecidableEq WeightLabel]
    (weightAction : Equiv.Perm WeightLabel)
    (input : ExternalPrincipalWeightActionInput WeightLabel weightAction) :
    ∃ equivalence : SimplePrincipalBrauerLabel ≃ WeightLabel,
      ∀ label, equivalence (simplePrincipalOuterAction label) =
        weightAction (equivalence label) := by
  apply exists_equivariantEquiv_of_card_eq_of_fixed_card_eq
    simplePrincipalOuterAction weightAction
    simplePrincipalOuterAction_involutive input.involutive
  · have hcard : Fintype.card SimplePrincipalBrauerLabel = 12 := by decide
    exact hcard.trans input.card_eq.symm
  · have hfixed :
        Fintype.card (Function.fixedPoints simplePrincipalOuterAction) = 8 := by
      decide
    exact hfixed.trans input.fixed_card_eq.symm

/-- The manuscript-facing finite conclusion after separately supplying the
central-cover alignment between the two table label sets. -/
theorem exists_principalC2Set_equivalence_of_external_weight_input
    {WeightLabel : Type*} [Fintype WeightLabel] [DecidableEq WeightLabel]
    (weightAction : Equiv.Perm WeightLabel)
    (input : ExternalPrincipalWeightActionInput WeightLabel weightAction)
    (alignment : PrincipalRestrictionAlignmentInput) :
    ∃ equivalence : PrincipalBrauerLabel ≃ WeightLabel,
      ∀ label, equivalence (principalBrauerOuterAction label) =
        weightAction (equivalence label) := by
  obtain ⟨simpleEquiv, simpleEquivariant⟩ :=
    exists_simplePrincipalC2Set_equivalence_of_external_weight_input
      weightAction input
  let equivalence : PrincipalBrauerLabel ≃ WeightLabel :=
    alignment.labelEquiv.symm.trans simpleEquiv
  refine ⟨equivalence, ?_⟩
  intro label
  have alignmentSymm :
      alignment.labelEquiv.symm (principalBrauerOuterAction label) =
        simplePrincipalOuterAction (alignment.labelEquiv.symm label) := by
    apply alignment.labelEquiv.injective
    rw [alignment.labelEquiv.apply_symm_apply,
      alignment.intertwines, alignment.labelEquiv.apply_symm_apply]
  change simpleEquiv
      (alignment.labelEquiv.symm (principalBrauerOuterAction label)) =
    weightAction (simpleEquiv (alignment.labelEquiv.symm label))
  rw [alignmentSymm, simpleEquivariant]

/-! ## The combined finite certificate -/

/-- The strongest finite certificate combined from the transcribed
constants in this file.  Its fields intentionally stop before the E3
boundaries above and before identification with actual weight classes. -/
structure Certificate : Prop where
  nineBlockRecords : blockRecords.length = 9
  blockCounts : ∀ block,
    (blockRecord block).brauerLabels.length = q3BrauerCount block
  allBrauerLabelsPartition :
    (blockRecords.flatMap BlockRecord.brauerLabels).Nodup ∧
      (blockRecords.flatMap BlockRecord.brauerLabels).toFinset = Finset.univ
  blockInvolution : Function.Involutive blockOuterAction
  blockActionList :
    ([.B1, .B2, .B3, .B4, .B5, .B6, .B7, .B8, .B9].map
      (fun block => blockPosition (blockOuterAction block))) =
        [1, 2, 3, 4, 5, 7, 6, 9, 8]
  brauerInvolution : Function.Involutive brauerOuterAction
  brauerActionList :
    (allBrauerLabels.map (fun label => (brauerOuterAction label).position)) =
      [1, 2, 3, 4, 6, 5, 7, 8, 9, 10, 12, 11, 13, 14, 15, 16, 17,
       19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30, 33, 32]
  blockFibreEquivariance : ∀ label,
    blockOfBrauerLabel (brauerOuterAction label) =
      blockOuterAction (blockOfBrauerLabel label)
  blockTwoInternalDimensions :
    blockTwoRecord.defectOrder = 2 ^ blockTwoRecord.defectExponent ∧
      blockTwoRecord.ordinaryLabels.length =
        blockTwoRecord.ordinaryCharacterCount ∧
      blockTwoRecord.ordinaryDegrees.length =
        blockTwoRecord.ordinaryCharacterCount ∧
      blockTwoRecord.heights.length = blockTwoRecord.ordinaryCharacterCount ∧
      blockTwoRecord.decompositionMatrix.length =
        blockTwoRecord.ordinaryCharacterCount ∧
      (∀ row ∈ blockTwoRecord.decompositionMatrix,
        row.length = blockTwoRecord.brauerCharacterCount) ∧
      blockTwoRecord.brauerLabels.length =
        blockTwoRecord.brauerCharacterCount
  blockTwoMatchesBlockRecord :
    blockTwoRecord.defectExponent = (blockRecord .B2).defectExponent ∧
      blockTwoRecord.brauerLabels = (blockRecord .B2).brauerLabels
  blockTwoHeightDistribution :
    blockTwoRecord.heights.count 0 = 4 ∧
      blockTwoRecord.heights.count 1 = 1
  blockTwoCartanIsGram :
    blockTwoRecord.cartanMatrix =
      listMatrixGramTwo blockTwoRecord.decompositionMatrix
  blockTwoOuterBrauerImage :
    blockTwoRecord.outerBrauerImage =
      blockTwoRecord.brauerLabels.map brauerOuterAction
  rawPSubgroupDistributionTotal :
    (pSubgroupOrderDistribution.map
      SubgroupOrderMultiplicity.multiplicity).sum = 3021
  twentySixPRadicalRepresentatives : pRadicalRepresentatives.length = 26
  fourteenFusionRows : gFusionRecords.length = 14
  fusionTargetsAreRepresentatives :
    ∀ row ∈ gFusionRecords,
      row.targetPClassIndex ∈ gRadicalRepresentativeIndices
  fusionOrdersAgree :
    ∀ row ∈ gFusionRecords,
      let source := pRadicalRepresentativeAt row.sourcePClassIndex
      let target := pRadicalRepresentativeAt row.targetPClassIndex
      source.pSubgroupClassIndex = row.sourcePClassIndex ∧
        target.pSubgroupClassIndex = row.targetPClassIndex ∧
        source.subgroupOrder = target.subgroupOrder ∧
        source.normalizerOrder = target.normalizerOrder
  fusionPartition :
    ((gFusionRecords.map GFusionRecord.sourcePClassIndex) ++
      gRadicalRepresentativeIndices).Nodup ∧
    (((gFusionRecords.map GFusionRecord.sourcePClassIndex) ++
      gRadicalRepresentativeIndices).toFinset =
        (pRadicalRepresentatives.map
          PRadicalRepresentative.pSubgroupClassIndex).toFinset)
  twelveRadicalClasses : radicalClassContributions.length = 12
  radicalClassIndices :
    radicalClassContributions.map
      RadicalClassContribution.pSubgroupClassIndex =
        [1, 3, 36, 47, 337, 2101, 2676, 2946, 3007, 3017, 3019, 3021]
  radicalClassesMatchRawOrders :
    ∀ row ∈ radicalClassContributions,
      let raw := pRadicalRepresentativeAt row.pSubgroupClassIndex
      raw.pSubgroupClassIndex = row.pSubgroupClassIndex ∧
        raw.subgroupOrder = row.subgroupOrder ∧
        raw.normalizerOrder = row.normalizerOrder
  radicalClassAggregation :
    radicalOrderContributionsFromClasses = q3RadicalContributions
  radicalQuotientArithmetic :
    ∀ row ∈ radicalClassContributions,
      row.subgroupOrder * row.weightQuotientOrder = row.normalizerOrder
  radicalTotals :
    radicalSectorTotal .trivial = 17 ∧
      radicalSectorTotal .faithfulOne = 8 ∧
      radicalSectorTotal .faithfulTwo = 8
  sectorAgreement : ∀ sector,
    radicalSectorTotal sector = blockBrauerSectorTotal sector
  twoLocalWeightRecords : localPrincipalWeightRecords.length = 2
  localQuotientArithmetic :
    ∀ row ∈ localPrincipalWeightRecords,
      row.subgroupOrder * row.weightQuotientOrder = row.hNormalizerOrder
  localCentralizerEqualsCentre :
    ∀ row ∈ localPrincipalWeightRecords,
      row.hCentralizerOrder = row.subgroupCentreOrder
  oneHRadicalRepresentativeEach :
    ∀ row ∈ localPrincipalWeightRecords,
      row.hRadicalRepresentativeCount = 1
  localSearchCounts :
    localPrincipalWeightRecords.map
      (fun row => (row.centricClassCount,
        row.sRadicalRepresentativeCount)) = [(53, 1), (15, 3)]
  oneDefectZeroDegreeEach :
    ∀ row ∈ localPrincipalWeightRecords, row.defectZeroDegrees.length = 1
  localDefectZeroDegreeTotal :
    (localPrincipalWeightRecords.map
      (fun row => row.defectZeroDegrees.length)).sum = 2
  localDefectZeroFullTwoPart :
    ∀ row ∈ localPrincipalWeightRecords,
      ∀ degree ∈ row.defectZeroDegrees,
        degree ∣ row.weightQuotientOrder ∧
          Odd (row.weightQuotientOrder / degree) ∧
          (degree = 4 ∨ degree = 8)
  principalRestrictionPartition :
    principalBrauerRestrictionRows.flatten = allSimplePrincipalBrauerLabels
  principalRestrictionShape :
    (principalBrauerRestrictionRows.map List.length).count 1 = 8 ∧
      (principalBrauerRestrictionRows.map List.length).count 2 = 2
  principalRestrictionAction :
    ∀ row ∈ principalBrauerRestrictionRows,
      (row.map simplePrincipalOuterAction).toFinset = row.toFinset
  simplePrincipalSignature :
    (Fintype.card SimplePrincipalBrauerLabel,
      Fintype.card (Function.fixedPoints simplePrincipalOuterAction)) = (12, 8)
  principalBrauerSignature :
    (Fintype.card PrincipalBrauerLabel,
      Fintype.card (Function.fixedPoints principalBrauerOuterAction)) = (12, 8)

theorem exceptionalQ3OutputCertificate : Certificate where
  nineBlockRecords := blockRecords_exactly_nine
  blockCounts := blockRecord_brauerCount
  allBrauerLabelsPartition := blockRecords_partition_allBrauerLabels
  blockInvolution := blockOuterAction_involutive
  blockActionList := blockOuterActionList_exact
  brauerInvolution := brauerOuterAction_involutive
  brauerActionList := brauerOuterActionList_exact
  blockFibreEquivariance := brauer_block_action_compatible
  blockTwoInternalDimensions := blockTwoRecord_internal_dimensions
  blockTwoMatchesBlockRecord := blockTwoRecord_matches_blockRecord
  blockTwoHeightDistribution := blockTwoRecord_heightDistribution
  blockTwoCartanIsGram := blockTwoRecord_cartan_eq_gram
  blockTwoOuterBrauerImage := blockTwoRecord_outerBrauerImage_exact
  rawPSubgroupDistributionTotal := pSubgroupOrderDistribution_total
  twentySixPRadicalRepresentatives :=
    pRadicalRepresentatives_exactly_twentySix
  fourteenFusionRows := gFusionRecords_exactly_fourteen
  fusionTargetsAreRepresentatives := gFusionTargets_are_representatives
  fusionOrdersAgree := gFusion_source_target_orders_agree
  fusionPartition := gFusion_partition_pRadicalIndices
  twelveRadicalClasses := radicalClassContributions_exactly_twelve
  radicalClassIndices := radicalClassIndices_exact
  radicalClassesMatchRawOrders := radicalClasses_match_raw_orders
  radicalClassAggregation := radicalClasses_aggregate_to_orderContributions
  radicalQuotientArithmetic := radicalClass_quotientOrder_arithmetic
  radicalTotals := radicalSectorTotals_exact
  sectorAgreement := radical_and_block_sectorTotals_agree
  twoLocalWeightRecords := localPrincipalWeightRecords_exactly_two
  localQuotientArithmetic := localPrincipalWeightRecords_quotientArithmetic
  localCentralizerEqualsCentre :=
    localPrincipalWeightRecords_centralizer_eq_centre
  oneHRadicalRepresentativeEach :=
    localPrincipalWeightRecords_one_hRadicalRepresentative_each
  localSearchCounts := localPrincipalWeightRecords_search_counts
  oneDefectZeroDegreeEach :=
    localPrincipalWeightRecords_one_defectZeroDegree_each
  localDefectZeroDegreeTotal :=
    localPrincipalWeightRecords_defectZeroDegree_total
  localDefectZeroFullTwoPart :=
    localPrincipalWeightRecords_defectZero_fullTwoPart
  principalRestrictionPartition := principalBrauerRestrictionRows_partition
  principalRestrictionShape := principalBrauerRestrictionRows_shape
  principalRestrictionAction := principalBrauerRestrictionRows_action_stable
  simplePrincipalSignature := simplePrincipal_action_signature
  principalBrauerSignature := principalBrauer_action_signature

end ModularRep.ManuscriptVerification.ExceptionalQ3OutputCertificate


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
