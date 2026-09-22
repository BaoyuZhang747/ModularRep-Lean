import ModularRep.ComputationTranscriptElab
import ModularRep.ComputationTranscriptSnapshots

/-!
# Printed prime-three central character allocation for `Fi'_{24}`

This module retains only natural numbers parsed from the canonical
`fi24blocks.out` transcript.  The GAP packet applies `BlockAssignments` to
the six ordinary rows in position two of the named local table for every
table-compatible class fusion into the named ambient table.

The declarations below do not identify either named table with a literal
group or normaliser, do not identify a table fusion with the actual inclusion,
and do not construct central characters, blocks, characters, weights, or a
`BlockInducesTo` witness in Lean.  In particular, the printed maximal-subgroup
and stored-fusion positions are table-library metadata, not literal subgroup
or fusion constructors.  These declarations therefore record E3 numerical
evidence only and imply no BAW or iBAW conclusion.

The possible-fusion value is only the length of the returned candidate list.
It does not assert that the returned fusions are distinct, and this module
does not compute a table-automorphism orbit.
-/

namespace ModularRep.PaperProofs.SporadicFi24P3NamedTableCentralCharacterTranscript

open ModularRep.ComputationTranscriptElab
open ModularRep.ComputationTranscriptSnapshots

/-- Defect exponents printed for the three ambient block positions. -/
def ambientDefectExponentsFromTranscript : List Nat :=
  output_nat_list fi24BlocksTranscript
    "P3_INDUCED_CENTRAL_CHARACTER_AMBIENT_DEFECTS"

/-- Position of the named local table in the ambient table's maximal-subgroup
metadata.  This is a printed table coordinate only. -/
def localMaximalSubgroupPositionFromTranscript : Nat :=
  output_nat fi24BlocksTranscript
    "P3_LOCAL_MAXIMAL_SUBGROUP_POSITION"

/-- Number of table-compatible class fusions examined by the GAP packet. -/
def possibleFusionCountFromTranscript : Nat :=
  output_nat fi24BlocksTranscript
    "P3_INDUCED_CENTRAL_CHARACTER_POSSIBLE_FUSIONS"

/-- Position of the stored fusion candidate selected by the canonical packet.
This does not identify it with a literal group inclusion. -/
def storedFusionCandidatePositionFromTranscript : Nat :=
  output_nat fi24BlocksTranscript
    "P3_STORED_FUSION_CANDIDATE_POSITION"

/-- Distinct vectors of ambient block positions returned by the GAP packet.
The six entries correspond to named-table ordinary row positions printed in
the same transcript. -/
def assignmentPatternsFromTranscript : List (List Nat) :=
  output_nat_matrix fi24BlocksTranscript
    "P3_INDUCED_CENTRAL_CHARACTER_ASSIGNMENT_PATTERNS"

theorem ambientDefectExponents_exact :
    ambientDefectExponentsFromTranscript = [16, 2, 0] := by
  decide

theorem localMaximalSubgroupPosition_exact :
    localMaximalSubgroupPositionFromTranscript = 17 := by
  decide

theorem possibleFusionCount_exact :
    possibleFusionCountFromTranscript = 32 := by
  decide

theorem storedFusionCandidatePosition_exact :
    storedFusionCandidatePositionFromTranscript = 1 := by
  decide

theorem assignmentPatterns_exact :
    assignmentPatternsFromTranscript = [[2, 2, 2, 2, 2, 2]] := by
  decide

end ModularRep.PaperProofs.SporadicFi24P3NamedTableCentralCharacterTranscript


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
