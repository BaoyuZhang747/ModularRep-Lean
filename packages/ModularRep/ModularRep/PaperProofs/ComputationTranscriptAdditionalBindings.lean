import ModularRep.ComputationTranscriptElab
import ModularRep.ComputationTranscriptSnapshots
import ModularRep.ExceptionalQ3OutputCertificate
import ModularRep.PaperProofs.SporadicProposition57ComputationRelative

/-!
# Further literal bindings to the computation transcripts

This module connects four further groups of build-time parser outputs to the
typed finite constants used by the computation certificates.  The build layer
embeds the current root output files and emits ordinary numeral expressions.
The equalities below are checked by the Lean kernel over those emitted terms.
The file-to-string operation and the elaborator's parsing remain audited build
provenance.  Both transcript consumers use the shared strings in
`ComputationTranscriptSnapshots`.  The pure Lean parser in
`ComputationTranscriptPure` does not currently discharge these bindings.

The statements do not certify GAP, the identification of a table or
permutation group, completeness of a computation, or the representation
theoretic interpretation of a printed position.  In particular, they do not
provide the external alignment between the simple-group positions in
`o7brauer.out` and the triple-cover positions in `o7blocks.out`.
-/

namespace ModularRep.PaperProofs.ComputationTranscriptAdditionalBindings

open ModularRep.ComputationTranscriptElab
open ModularRep.ComputationTranscriptSnapshots
open ModularRep.ManuscriptVerification.ExceptionalQ3OutputCertificate
open ModularRep.PaperProofs.SporadicProposition57ComputationRelative
open Formalisation.ComputationArithmetic

/-! ## The ten principal restriction rows for `Omega_7(3)` -/

/-- The one-based position printed for a simple-group principal-block Brauer
label.  This projection deliberately stays on the simple-table label type. -/
def SimplePrincipalBrauerLabel.position : SimplePrincipalBrauerLabel -> Nat
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

/-- All ten nested lists are read independently from their named transcript
fields.  The outer row partition and every inner row boundary are retained. -/
def principalBrauerRestrictionPositionsFromTranscript : List (List Nat) :=
  [output_nat_list o7BrauerTranscript "H_B0_RESTRICTION_H1",
   output_nat_list o7BrauerTranscript "H_B0_RESTRICTION_H2",
   output_nat_list o7BrauerTranscript "H_B0_RESTRICTION_H3",
   output_nat_list o7BrauerTranscript "H_B0_RESTRICTION_H4",
   output_nat_list o7BrauerTranscript "H_B0_RESTRICTION_H5",
   output_nat_list o7BrauerTranscript "H_B0_RESTRICTION_H6",
   output_nat_list o7BrauerTranscript "H_B0_RESTRICTION_H7",
   output_nat_list o7BrauerTranscript "H_B0_RESTRICTION_H8",
   output_nat_list o7BrauerTranscript "H_B0_RESTRICTION_H9",
   output_nat_list o7BrauerTranscript "H_B0_RESTRICTION_H10"]

theorem principalBrauerRestrictionRows_are_the_transcript_rows :
    principalBrauerRestrictionPositionsFromTranscript =
      principalBrauerRestrictionRows.map
        (fun row => row.map SimplePrincipalBrauerLabel.position) := by
  decide

/-! ## Baby Monster data at seven -/

def babySevenRestrictionRanksFromTranscript : List Nat :=
  output_nat_list babyTranscript "DOUBLE_COVER_DEFECT_2_SEVEN_BLOCK_RANKS"

def babySevenRegularClassCountFromTranscript : Nat :=
  output_nat babyTranscript "DOUBLE_COVER_7_REGULAR_CLASS_COUNT"

theorem babySeven_data_are_the_transcript_data :
    babySevenRestrictionRanksFromTranscript = babySevenRestrictionRanks ∧
      babySevenRegularClassCountFromTranscript = babySevenRegularClassCount := by
  decide

/-! ## Three selected `Fi'_24` rows at three -/

/-- The triples `(l,fixed,free2)` read from the three printed `P3` rows.
The definition deliberately retains only the numerical fields.  It does not
identify a row with a mathematical block or assert that the rows form a
complete block census. -/
def fi24ThreePrintedRowsFromTranscript : List (Nat × Nat × Nat) :=
  [(output_line_nat fi24BlocksTranscript
      "BLOCK label=P3 p=3 id=1 " "l",
    output_line_nat fi24BlocksTranscript
      "BLOCK label=P3 p=3 id=1 " "fixed",
    output_line_nat fi24BlocksTranscript
      "BLOCK label=P3 p=3 id=1 " "free2"),
   (output_line_nat fi24BlocksTranscript
      "BLOCK label=P3 p=3 id=2 " "l",
    output_line_nat fi24BlocksTranscript
      "BLOCK label=P3 p=3 id=2 " "fixed",
    output_line_nat fi24BlocksTranscript
      "BLOCK label=P3 p=3 id=2 " "free2"),
   (output_line_nat fi24BlocksTranscript
      "BLOCK label=P3 p=3 id=3 " "l",
    output_line_nat fi24BlocksTranscript
      "BLOCK label=P3 p=3 id=3 " "fixed",
    output_line_nat fi24BlocksTranscript
      "BLOCK label=P3 p=3 id=3 " "free2")]

theorem fi24ThreePrintedRows_exact :
    fi24ThreePrintedRowsFromTranscript =
      [(25, 25, 0), (4, 2, 1), (1, 1, 0)] := by
  decide

/-! ## Prime-three local-table positions -/

/-- The six numerical fields printed for each selected quotient-table row.
They are table positions and degrees, not literal characters or blocks. -/
def fi24ThreeLocalTableCertificateFromTranscript : List (List Nat) :=
  output_nat_matrix fi24P3Transcript "P3_LOCAL_CERTIFICATE"

/-- One-based nonzero decomposition-matrix column positions, in the row order
printed by `fi24p3.g`.  These are positions in the named table only. -/
def fi24ThreeLocalDecompositionSupportPositionsFromTranscript :
    List (List Nat) :=
  output_nat_matrix fi24P3Transcript
    "P3_LOCAL_DECOMPOSITION_SUPPORTS"

/-- Nonzero decomposition coefficients in the same printed row order. -/
def fi24ThreeLocalDecompositionCoefficientsFromTranscript :
    List (List Nat) :=
  output_nat_matrix fi24P3Transcript
    "P3_LOCAL_DECOMPOSITION_COEFFICIENTS"

/-- The one-based positions returned by the local table's block-two
`modchars` field. -/
def fi24ThreeLocalBlockTwoBrauerPositionsFromTranscript : List Nat :=
  output_nat_list fi24P3Transcript
    "P3_LOCAL_BLOCK_TWO_BRAUER_ROWS"

theorem fi24ThreeLocalTableCertificate_exact :
    fi24ThreeLocalTableCertificateFromTranscript =
      [[23, 729, 2, 23, 2, 8], [24, 729, 3, 24, 2, 9],
       [51, 729, 5, 51, 2, 18], [52, 729, 6, 52, 2, 17]] := by
  decide

theorem fi24ThreeLocalDecompositionSupportPositions_exact :
    fi24ThreeLocalDecompositionSupportPositionsFromTranscript =
      [[8], [9], [18], [17]] := by
  decide

theorem fi24ThreeLocalDecompositionCoefficients_exact :
    fi24ThreeLocalDecompositionCoefficientsFromTranscript =
      [[1], [1], [1], [1]] := by
  decide

theorem fi24ThreeLocalBlockTwoBrauerPositions_exact :
    fi24ThreeLocalBlockTwoBrauerPositionsFromTranscript =
      [8, 9, 17, 18] := by
  decide

/-! ## The faithful `Fi'_24` block action at five -/

def Fi24FaithfulFiveBlock.ofPosition? : Nat -> Option Fi24FaithfulFiveBlock
  | 45 => some .b45
  | 46 => some .b46
  | 47 => some .b47
  | 48 => some .b48
  | _ => none

/-- Decode each printed `outer` field on the four faithful blocks. -/
def fi24FaithfulFiveOuterFromTranscript :
    Fi24FaithfulFiveBlock -> Option Fi24FaithfulFiveBlock
  | .b45 => Fi24FaithfulFiveBlock.ofPosition? <|
      output_line_nat fi24BlocksTranscript
        "BLOCK label=P5 p=5 id=45 " "outer"
  | .b46 => Fi24FaithfulFiveBlock.ofPosition? <|
      output_line_nat fi24BlocksTranscript
        "BLOCK label=P5 p=5 id=46 " "outer"
  | .b47 => Fi24FaithfulFiveBlock.ofPosition? <|
      output_line_nat fi24BlocksTranscript
        "BLOCK label=P5 p=5 id=47 " "outer"
  | .b48 => Fi24FaithfulFiveBlock.ofPosition? <|
      output_line_nat fi24BlocksTranscript
        "BLOCK label=P5 p=5 id=48 " "outer"

theorem fi24FaithfulFiveOuter_is_the_transcript_action
    (block : Fi24FaithfulFiveBlock) :
    fi24FaithfulFiveOuterFromTranscript block =
      some (fi24FaithfulFiveOuter block) := by
  cases block <;> decide

end ModularRep.PaperProofs.ComputationTranscriptAdditionalBindings


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
