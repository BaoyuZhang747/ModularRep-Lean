import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBabyTwoNumerical
import ModularRep.PaperProofs.ComputationTranscriptAdditionalBindings

/-!
# The Baby Monster counts in Proposition 5.4

The complete classification by two blocks is on the specified primitive
idempotents and the actual Brauer and weight fibres. The table
interpretation supplies the two Brauer counts, and the published weight
classification supplies the total weight count. Sambale's Theorem 13.7
supplies only the numerical equality for the block with defect group of
order eight. The principal weight count and the equality in every block are
deductions.

At seven, the theorem verifies the displayed numerical values from the GAP
record. Identifying the character table with the double cover remains a
separate assumption.
-/

noncomputable section
set_option autoImplicit false

namespace ManuscriptIBAW.Sporadic.BabyNumerical

open ModularRep
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
  (ActualBlock LiteralBlockSource WeightClass)
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBabyTwoSources
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllPairs

universe u
variable {k K X : Type u}
  [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
  [Group X] [Fintype X]
  (iota : PrimeRegularRootEmbedding 2 k K X)
  (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
  (R : LiteralBlockSource (p := 2) (k := k) (K := K) (X := X))
  (source : BabyTwoSource iota hinj R)
  (small : SmallDefectNumericalSource iota hinj R)

include source small

/-- The theorem for small defect groups applies to the same nonprincipal block. -/
theorem nonprincipal_count :
    Nat.card (WeightFibre R (source.roles 1)) = 2 := by
  have h := ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBabyTwoNumerical.nonprincipal_count_eq
    iota hinj R source small
  exact h.symm.trans (source.brauer_ranks iota hinj R).2

/-- The exhaustive block decomposition forces the principal weight count. -/
theorem principal_count :
    Nat.card (BrauerFibre iota hinj R (source.roles 0)) = 25 ∧
      Nat.card (WeightFibre R (source.roles 0)) = 25 := by
  have hsum := source.actual_weight_decomposition iota hinj R
  have hsmall := nonprincipal_count iota hinj R source small
  have htotal := source.totalWeights
  exact ⟨(source.brauer_ranks iota hinj R).1, by omega⟩

/-- Both block counts are established before applying complete collapse. -/
theorem all_block_counts (b : ActualBlock (k := k) (X := X)) :
    Nat.card (BrauerFibre iota hinj R b) = Nat.card (WeightFibre R b) := by
  rcases source.roles_cover iota hinj R b with rfl | rfl
  · exact (principal_count iota hinj R source small).1.trans
      (principal_count iota hinj R source small).2.symm
  · exact (source.brauer_ranks iota hinj R).2.trans
      (nonprincipal_count iota hinj R source small).symm

local instance brauerFintype : Fintype (IBr iota) := Fintype.ofFinite _

/-- Convert the proved counts to the exact hypotheses of Lemma 5.2. -/
theorem numericalBlockwiseAWC [Fintype (WeightClass (p := 2) (K := K) (X := X))] :
    letI := R.1.operations.ambientBlockData.fintypeBlock
    ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual.NumericalBlockwiseAWC
      (iota := iota) (hinj := hinj)
      (blocks := R.1.operations.ambientBlockData.blocks) (R := R) := by
  classical
  let := R.1.operations.ambientBlockData.fintypeBlock
  intro b
  let e :
      {phi : IBr iota // ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual.brauerBlock
        iota hinj R.1.operations.ambientBlockData.blocks phi = b} ≃
      BrauerFibre iota hinj R b :=
    Equiv.subtypeEquivRight (fun phi => by
      rw [operationsBlock_eq iota hinj R R.1.operations.ambientBlockData.blocks phi]
      rfl)
  simpa only [← Nat.card_eq_fintype_card] using
    (Nat.card_congr e).trans (all_block_counts iota hinj R source small b)

omit source small in
/-- Check the recorded total and four restriction ranks at seven.
Their identification with the character table remains an assumption. -/
theorem seven_transcript_values :
    ModularRep.PaperProofs.ComputationTranscriptAdditionalBindings.babySevenRegularClassCountFromTranscript = 222 ∧
      ModularRep.PaperProofs.ComputationTranscriptAdditionalBindings.babySevenRestrictionRanksFromTranscript =
        [24, 24, 21, 24] := by
  decide

end ManuscriptIBAW.Sporadic.BabyNumerical

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
