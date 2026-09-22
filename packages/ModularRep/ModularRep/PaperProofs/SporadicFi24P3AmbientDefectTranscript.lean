import ModularRep.ComputationTranscriptElab
import ModularRep.ComputationTranscriptSnapshots

/-!
# Printed `Fi'_{24}` block defects at three

This module retains only the block identifiers and defect exponents printed
by the current `fi24blocks.out` transcript for the CTblLib table `F3+` at
three.  The declarations below concern parsed natural numbers.  They do not
identify a printed position with a literal block, primitive idempotent, or
Navarro defect representative, and they imply no exact-defect, induction,
BAW, or iBAW statement.
-/

namespace ModularRep.PaperProofs.SporadicFi24P3AmbientDefectTranscript

open ModularRep.ComputationTranscriptElab
open ModularRep.ComputationTranscriptSnapshots

/-- The number after `blocks=` on the printed `P3` `BLOCK_DATA` line.  This
is parsed independently of the three selected block rows below. -/
def fi24P3AmbientBlockCountFromTranscript : Nat :=
  output_line_nat fi24BlocksTranscript
    "BLOCK_DATA label=P3 p=3 carrier=F3+ " "blocks"

/-- The current transcript states that the complete named-table block list at
three has three entries. -/
theorem fi24P3AmbientBlockCount_exact :
    fi24P3AmbientBlockCountFromTranscript = 3 := by
  decide

/-- The pairs `(id,defect)` parsed from the three printed `P3` block rows.
Here `id` is the position returned by the CTblLib `PrimeBlocks` computation,
not a literal block identifier in the group algebra. -/
def fi24P3AmbientBlockDefectRowsFromTranscript : List (Nat × Nat) :=
  [(output_line_nat fi24BlocksTranscript
      "BLOCK label=P3 p=3 id=1 " "id",
    output_line_nat fi24BlocksTranscript
      "BLOCK label=P3 p=3 id=1 " "defect"),
   (output_line_nat fi24BlocksTranscript
      "BLOCK label=P3 p=3 id=2 " "id",
    output_line_nat fi24BlocksTranscript
      "BLOCK label=P3 p=3 id=2 " "defect"),
   (output_line_nat fi24BlocksTranscript
      "BLOCK label=P3 p=3 id=3 " "id",
    output_line_nat fi24BlocksTranscript
      "BLOCK label=P3 p=3 id=3 " "defect")]

/-- The current transcript prints precisely these three pairs. -/
theorem fi24P3AmbientBlockDefectRows_exact :
    fi24P3AmbientBlockDefectRowsFromTranscript =
      [(1, 16), (2, 2), (3, 0)] := by
  decide

/-- The printed CTblLib block identifiers are `1`, `2`, and `3`. -/
theorem fi24P3AmbientBlockIds_exact :
    fi24P3AmbientBlockDefectRowsFromTranscript.map Prod.fst = [1, 2, 3] := by
  decide

/-- The defect exponents printed in those positions are `16`, `2`, and `0`.
This is a numerical transcript statement only. -/
theorem fi24P3AmbientDefectExponents_exact :
    fi24P3AmbientBlockDefectRowsFromTranscript.map Prod.snd = [16, 2, 0] := by
  decide

end ModularRep.PaperProofs.SporadicFi24P3AmbientDefectTranscript


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
