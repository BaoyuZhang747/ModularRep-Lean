import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

/-!
# The corrected Table 8 column for one faithful central character

Transcription of the plain lambda_3 column on page 5 of the
An--Dietrich erratum, corrected Table 8. The list below records its 34
entries. These are ordinary local counts for one faithful character;
they carry no fixed-point coordinate. Actual group, row and retained-root
bindings are required separately. The first printed row is Q=1.
-/

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulLocalTableAtTwo

def correctedFi24FaithfulTable8AtTwo : List Nat :=
  [0,0,1,0,1,1,0,0,1,1,1,0,1,1,0,0,1,1,1,1,1,0,1,1,1,1,1,1,1,1,1,1,1,1]

theorem correctedFi24FaithfulTable8AtTwo_length :
    correctedFi24FaithfulTable8AtTwo.length = 34 := by decide

theorem correctedFi24FaithfulTable8AtTwo_sum :
    correctedFi24FaithfulTable8AtTwo.sum = 25 := by decide

theorem correctedFi24FaithfulTable8AtTwo_first :
    correctedFi24FaithfulTable8AtTwo[0]? = some 0 := by decide

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulLocalTableAtTwo


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
