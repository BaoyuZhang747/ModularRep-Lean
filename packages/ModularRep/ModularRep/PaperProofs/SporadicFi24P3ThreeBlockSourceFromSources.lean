import ModularRep.PaperProofs.ComputationTranscriptAdditionalBindings
import ModularRep.PaperProofs.SporadicFi24P3AmbientDefectTranscript
import ModularRep.PaperProofs.SporadicFi24SelectedOuterInvolutionCarrier
import ModularRep.PaperProofs.SporadicFi24ThreeBlockCarrierActual

/-!
# The Fischer three-block source from narrow catalogue bindings

For `Fi'_{24}` at three, An--Cannon--O'Brien--Unger, Lemma 4.2(c),
identifies the principal positive-defect block and the unique nonprincipal
positive-defect block, whose defect group has order `3^2`.  Their block
calculation also gives Brauer ranks `25` and `4`; the remaining ordinary
defect-zero character accounts for the defect-zero role.  Independently, the
current `fi24blocks.g/out` packet prints exactly three CTblLib block positions,
with defect exponents `16`, `2`, and `0`, and prints the identity outer image
on those three positions.

Those statements do not themselves identify a CTblLib position with a
primitive central idempotent in the Lean coefficient algebra.  This module
therefore leaves precisely two semantic bindings visible:

* `Fi24P3BlockIndexBinding` is one equivalence from the three source roles to
  the indices of an already supplied complete block-idempotent decomposition;
* `Fi24P3SelectedOuterBlockActionBinding` identifies the selected literal
  block action, role by role, with the action parsed from `fi24blocks.out`.

From the first binding Lean derives pairwise distinction and exhaustiveness.
From the second and the parsed identity permutation Lean derives all three
fixedness equations.  The square-one equation comes from the existing
`SelectedOuterInvolutionCarrier`.  Hence the old `Fi24ThreeBlockSource` is a
kernel construction from these narrower inputs.

There is no character--weight map, principal cancellation, blockwise
equivalence, weight or radical coverage statement, BAW condition, or iBAW
conclusion in this file.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3ThreeBlockSourceFromSources

open ModularRep
open ModularRep.ComputationTranscriptElab
open ModularRep.ComputationTranscriptSnapshots
open ModularRep.PaperProofs.ComputationTranscriptAdditionalBindings
open ModularRep.PaperProofs.SporadicFi24P3AmbientDefectTranscript
open ModularRep.PaperProofs.SporadicFi24SelectedOuterInvolutionCarrier
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual

universe u

/-! ## The three source roles and their transcript rows -/

/-- The three block roles occurring in the prime-three Fischer calculation.
The order is the order of the selected `P3` rows in `fi24blocks.out`. -/
inductive Fi24P3BlockRole
  | principal
  | nonprincipal
  | defectZero
  deriving DecidableEq

instance : Fintype Fi24P3BlockRole :=
  ⟨{.principal, .nonprincipal, .defectZero}, by
    intro role
    cases role <;> simp⟩

namespace Fi24P3BlockRole

/-- The one-based CTblLib `PrimeBlocks` position attached to a source role. -/
def transcriptId : Fi24P3BlockRole → Nat
  | .principal => 1
  | .nonprincipal => 2
  | .defectZero => 3

/-- The defect exponent printed for the corresponding CTblLib position. -/
def transcriptDefectExponent : Fi24P3BlockRole → Nat
  | .principal => 16
  | .nonprincipal => 2
  | .defectZero => 0

/-- The printed triple `(l,fixed,free2)` for the corresponding position. -/
def transcriptBrauerRow : Fi24P3BlockRole → Nat × Nat × Nat
  | .principal => (25, 25, 0)
  | .nonprincipal => (4, 2, 1)
  | .defectZero => (1, 1, 0)

/-- Decode the three selected CTblLib positions and no others. -/
def ofTranscriptId? : Nat → Option Fi24P3BlockRole
  | 1 => some .principal
  | 2 => some .nonprincipal
  | 3 => some .defectZero
  | _ => none

@[simp]
theorem ofTranscriptId?_transcriptId (role : Fi24P3BlockRole) :
    ofTranscriptId? role.transcriptId = some role := by
  cases role <;> rfl

/-- The `outer` coordinate read directly from the role's selected `P3` row. -/
def outerImageIdFromTranscript : Fi24P3BlockRole → Nat
  | .principal =>
      output_line_nat fi24BlocksTranscript
        "BLOCK label=P3 p=3 id=1 " "outer"
  | .nonprincipal =>
      output_line_nat fi24BlocksTranscript
        "BLOCK label=P3 p=3 id=2 " "outer"
  | .defectZero =>
      output_line_nat fi24BlocksTranscript
        "BLOCK label=P3 p=3 id=3 " "outer"

/-- Decode the printed outer image back to a role.  The default is present
only to make the transcript projection total; the exact theorem below proves
that it is not used on any of the three roles. -/
def outerRoleFromTranscript (role : Fi24P3BlockRole) : Fi24P3BlockRole :=
  (ofTranscriptId? role.outerImageIdFromTranscript).getD role

/-- The current transcript sends each of its three selected block positions
to itself. -/
theorem outerImageIdFromTranscript_eq
    (role : Fi24P3BlockRole) :
    role.outerImageIdFromTranscript = role.transcriptId := by
  cases role <;> decide

/-- Consequently the decoded transcript action is the identity on roles. -/
@[simp]
theorem outerRoleFromTranscript_eq_self
    (role : Fi24P3BlockRole) :
    role.outerRoleFromTranscript = role := by
  cases role <;> decide

end Fi24P3BlockRole

/-- The source roles in the printed row order. -/
def fi24P3BlockRoles : List Fi24P3BlockRole :=
  [.principal, .nonprincipal, .defectZero]

/-- The typed role defects are exactly the three rows parsed independently
by `SporadicFi24P3AmbientDefectTranscript`.  This is still a statement about
natural-number table positions, not literal blocks. -/
theorem fi24P3RoleDefects_are_transcript_rows :
    fi24P3AmbientBlockDefectRowsFromTranscript =
      fi24P3BlockRoles.map fun role =>
        (role.transcriptId, role.transcriptDefectExponent) := by
  rw [fi24P3AmbientBlockDefectRows_exact]
  rfl

/-- The typed role signatures are exactly the three selected rows already
parsed from the same transcript. -/
theorem fi24P3RoleBrauerRows_are_transcript_rows :
    fi24ThreePrintedRowsFromTranscript =
      fi24P3BlockRoles.map Fi24P3BlockRole.transcriptBrauerRow := by
  rw [fi24ThreePrintedRows_exact]
  rfl

/-- The three independently parsed outer-image coordinates, in source-role
order. -/
def fi24P3OuterImageIdsFromTranscript : List Nat :=
  fi24P3BlockRoles.map Fi24P3BlockRole.outerImageIdFromTranscript

/-- The outer-image fields in `fi24blocks.out` are exactly `1,2,3`. -/
theorem fi24P3OuterImageIdsFromTranscript_exact :
    fi24P3OuterImageIdsFromTranscript = [1, 2, 3] := by
  decide

/-! ## The literal catalogue binding -/

/-- The exact E2/U identification still required between the three
ACOU/transcript roles and the indices of the supplied complete literal block
decomposition.

A single equivalence records both allocation of the named roles and coverage
of the complete index catalogue.  It contains no character, weight,
automorphism, or equivalence between character fibres. -/
structure Fi24P3BlockIndexBinding (BlockIndex : Type u) where
  indexEquiv : Fi24P3BlockRole ≃ BlockIndex

namespace Fi24P3BlockIndexBinding

variable {BlockIndex : Type u}

/-- The role equivalence gives the older role-labelled index census.
Pairwise distinction and exhaustiveness are consequences of bijectivity. -/
def toIndexCensus (C : Fi24P3BlockIndexBinding BlockIndex) :
    Fi24ThreeBlockIndexCensus BlockIndex where
  principalIndex := C.indexEquiv .principal
  nonprincipalIndex := C.indexEquiv .nonprincipal
  defectZeroIndex := C.indexEquiv .defectZero
  principal_ne_nonprincipal := by
    intro h
    cases C.indexEquiv.injective h
  principal_ne_defectZero := by
    intro h
    cases C.indexEquiv.injective h
  nonprincipal_ne_defectZero := by
    intro h
    cases C.indexEquiv.injective h
  all_indices := by
    intro i
    obtain ⟨role, rfl⟩ := C.indexEquiv.surjective i
    cases role with
    | principal => exact Or.inl rfl
    | nonprincipal => exact Or.inr (Or.inl rfl)
    | defectZero => exact Or.inr (Or.inr rfl)

variable {k X : Type u}
variable [Field k] [Group X] [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}

/-- Compose the role binding with the canonical equivalence from a complete
decomposition to all literal primitive central idempotents. -/
noncomputable def literalBlockEquiv
    (C : Fi24P3BlockIndexBinding BlockIndex)
    (blocks : BlockIdempotentDecomposition blockIdempotent) :
    Fi24P3BlockRole ≃
      ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual.ActualBlock
        (k := k) (X := X) :=
  C.indexEquiv.trans blocks.primitiveBlockEquiv

@[simp]
theorem literalBlockEquiv_apply
    (C : Fi24P3BlockIndexBinding BlockIndex)
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (role : Fi24P3BlockRole) :
    C.literalBlockEquiv blocks role =
      blocks.primitiveBlockOfIndex (C.indexEquiv role) :=
  rfl

end Fi24P3BlockIndexBinding

/-! ## The selected outer action binding and final construction -/

variable {k X BlockIndex : Type u}
variable [Field k] [Group X] [Fintype X] [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}
variable (blocks : BlockIdempotentDecomposition blockIdempotent)

/-- The smallest remaining E1/E2/E3/U action certificate: the selected
literal action agrees, on the three role-labelled primitive idempotents, with
the outer-image coordinates parsed from `fi24blocks.out`.

This is one action-alignment field, rather than the three fixedness fields of
`Fi24ThreeBlockSource`.  The parsed permutation happens to be the identity,
so those fixedness fields are derived below. -/
structure Fi24P3SelectedOuterBlockActionBinding
    (I : SelectedOuterInvolutionCarrier X)
    (C : Fi24P3BlockIndexBinding BlockIndex) : Prop where
  action_eq_transcript : ∀ role : Fi24P3BlockRole,
    I.outer • blocks.primitiveBlockOfIndex (C.indexEquiv role) =
      blocks.primitiveBlockOfIndex
        (C.indexEquiv role.outerRoleFromTranscript)

omit [Fintype X] in
/-- Agreement with the parsed identity permutation fixes every one of the
three literal role blocks. -/
theorem selectedOuter_fixed_of_actionBinding
    (I : SelectedOuterInvolutionCarrier X)
    (C : Fi24P3BlockIndexBinding BlockIndex)
    (A : Fi24P3SelectedOuterBlockActionBinding blocks I C)
    (role : Fi24P3BlockRole) :
    I.outer • blocks.primitiveBlockOfIndex (C.indexEquiv role) =
      blocks.primitiveBlockOfIndex (C.indexEquiv role) := by
  calc
    I.outer • blocks.primitiveBlockOfIndex (C.indexEquiv role) =
        blocks.primitiveBlockOfIndex
          (C.indexEquiv role.outerRoleFromTranscript) :=
      A.action_eq_transcript role
    _ = blocks.primitiveBlockOfIndex (C.indexEquiv role) := by
      rw [Fi24P3BlockRole.outerRoleFromTranscript_eq_self]

/-- Construct the complete family of three blocks from the given source
bindings.  Literal block distinction and exhaustiveness are derived through
`Fi24ThreeBlockSource.ofIndexCensus`; literal stability is derived from the
single transcript-action alignment. -/
noncomputable def fi24ThreeBlockSourceOfBindings
    (I : SelectedOuterInvolutionCarrier X)
    (C : Fi24P3BlockIndexBinding BlockIndex)
    (A : Fi24P3SelectedOuterBlockActionBinding blocks I C) :
    Fi24ThreeBlockSource (k := k) (X := X) :=
  Fi24ThreeBlockSource.ofIndexCensus
    (blocks := blocks)
    I.outer I.outer_square C.toIndexCensus
    (selectedOuter_fixed_of_actionBinding blocks I C A .principal)
    (selectedOuter_fixed_of_actionBinding blocks I C A .nonprincipal)
    (selectedOuter_fixed_of_actionBinding blocks I C A .defectZero)

end ModularRep.PaperProofs.SporadicFi24P3ThreeBlockSourceFromSources


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
