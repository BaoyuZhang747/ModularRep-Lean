import ModularRep.PaperProofs.SporadicFi24P3QSquaredCarrierAlignment

/-!
# Exact `Q` ambient uniqueness for the generic `Fi'_{24}` packet at three

This file isolates the two external block defect exclusions needed to show
that the named nonprincipal block is the only literal ambient block having
the nominated subgroup `Q` as a Navarro (4.11) defect representative.  The
source fields exclude the principal and defect-zero blocks independently of
any local block or induction map.

The uniqueness theorems are kernel deductions from those exclusions and the
exhaustive source listing the three blocks.  Existence remains a separate
input, and the final adapters obtain it from the previously isolated bare
target or compatibility carrier-alignment source.  No table row, First Main
image, block induction, support correspondence, character--weight map,
cancellation, BAW, or iBAW statement is stored in the source below.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3QSquaredAmbientUniqueness

open ModularRep
open ModularRep.CharacterWeight
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual
open ModularRep.PaperProofs.SporadicFi24P3QSquaredCarrierAlignment

universe u

variable {k K X : Type u}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

/-! ## The two external exclusions -/

/-- The minimal composite consumer boundary excluding the other two literal
blocks from the exact `Q` ambient defect sector.

These direct exclusions are conservatively graded E1/E2/E3/U.  The intended
external justification combines standard principal and defect-group facts,
the specialised ordinary block classification, the ambient computational
cross-check, an ordinary-defect-to-Navarro bridge, and literal
group/subgroup/block-role matches.  In particular, An--Cannon--O'Brien--Unger,
Lemma 4.2(c), does not by itself prove either displayed literal Navarro
negation.  The fields do not name a local block, an induction map, or the
desired nonprincipal image. -/
structure Source
    (R : LiteralCarrierAdapter
      (p := 3) (k := k) (K := K) (X := X))
    (three : Fi24ThreeBlockSource (k := k) (X := X))
    (Q : Subgroup X) : Prop where
  principal_not_exactQ :
    ¬ AmbientHasDefect R Q three.principalBlock
  defectZero_not_exactQ :
    ¬ AmbientHasDefect R Q three.defectZeroBlock

namespace Source

variable
  {R : LiteralCarrierAdapter
    (p := 3) (k := k) (K := K) (X := X)}
  {three : Fi24ThreeBlockSource (k := k) (X := X)}
  {Q : Subgroup X}

/-! ## Kernel consequences -/

/-- Any literal ambient block having exact defect representative `Q` is the
named nonprincipal block.  This is only the three case split supplied by
`three.all_blocks`. -/
theorem eq_nonprincipal_of_ambientHasDefect
    (U : Source R three Q)
    {B : ActualBlock (k := k) (X := X)}
    (hB : AmbientHasDefect R Q B) :
    B = three.nonprincipalBlock := by
  rcases three.all_blocks B with h | h | h
  · subst B
    exact False.elim (U.principal_not_exactQ hB)
  · exact h
  · subst B
    exact False.elim (U.defectZero_not_exactQ hB)

/-- Once existence for the named nonprincipal block is supplied separately,
the ambient exact `Q` predicate is equivalent to equality with that block. -/
theorem ambientHasDefect_iff_eq_nonprincipal
    (U : Source R three Q)
    (hNonprincipal :
      AmbientHasDefect R Q three.nonprincipalBlock)
    (B : ActualBlock (k := k) (X := X)) :
    AmbientHasDefect R Q B ↔ B = three.nonprincipalBlock := by
  constructor
  · exact U.eq_nonprincipal_of_ambientHasDefect
  · intro h
    subst B
    exact hNonprincipal

/-- Once existence is supplied separately, the named nonprincipal block is
the unique literal ambient block having exact defect representative `Q`. -/
theorem existsUnique_ambientHasDefect
    (U : Source R three Q)
    (hNonprincipal :
      AmbientHasDefect R Q three.nonprincipalBlock) :
    ∃! B : ActualBlock (k := k) (X := X), AmbientHasDefect R Q B := by
  refine ⟨three.nonprincipalBlock, hNonprincipal, ?_⟩
  intro B hB
  exact U.eq_nonprincipal_of_ambientHasDefect hB

/-- A bare-target alignment supplies nonprincipal existence on the same
literal ambient catalogue.  Uniqueness is then the kernel case split above;
no inherited three-block coverage field is inspected by the alignment. -/
theorem existsUnique_ambientHasDefect_of_coreAlignment
    (U : Source R three Q)
    {table :
      SporadicFi24P3QSquaredLocalTableSource.Source Q
        (R.1.operations.toLocalNormalizerBlockOperations Q)}
    (alignment :
      SporadicFi24P3QSquaredCarrierAlignment.CoreSource R Q table
        three.nonprincipalBlock) :
    ∃! B : ActualBlock (k := k) (X := X), AmbientHasDefect R Q B :=
  U.existsUnique_ambientHasDefect alignment.ambientHasDefect

/-- The carrier alignment source supplies existence on the same literal
ambient catalogue; the compatibility conversion forgets its unused
three-block data before the two exclusions above give uniqueness. -/
theorem existsUnique_ambientHasDefect_of_alignment
    (U : Source R three Q)
    {table :
      SporadicFi24P3QSquaredLocalTableSource.Source Q
        (R.1.operations.toLocalNormalizerBlockOperations Q)}
    (alignment :
      SporadicFi24P3QSquaredCarrierAlignment.Source R three Q table) :
    ∃! B : ActualBlock (k := k) (X := X), AmbientHasDefect R Q B :=
  U.existsUnique_ambientHasDefect_of_coreAlignment alignment.toCore

end Source

end ModularRep.PaperProofs.SporadicFi24P3QSquaredAmbientUniqueness


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
