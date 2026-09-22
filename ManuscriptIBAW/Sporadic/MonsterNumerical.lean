import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierMonsterTwoNumerical

/-!
# The Monster subtraction in Proposition 5.4

The five specified blocks exhaust the primitive blocks. Their four
nonprincipal defect groups have orders one, one, sixteen and one. The
numerical theorem for small defect groups applies to these blocks. Equality
of the two total counts then determines the principal count equality on the
same Brauer and weight fibres. No principal count or matching is supplied.
-/

noncomputable section
set_option autoImplicit false

namespace ManuscriptIBAW.Sporadic.MonsterNumerical

open ModularRep
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
  (ActualBlock LiteralBlockSource WeightClass)
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBabyTwoSources
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierMonsterTwoSources
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllPairs
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFiniteFibres

universe u
variable {k K X : Type u}
  [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
  [Group X] [Fintype X]
  (iota : PrimeRegularRootEmbedding 2 k K X)
  (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
  (R : LiteralBlockSource (p := 2) (k := k) (K := K) (X := X))
  (source : MonsterTwoSource iota hinj R)
  (small : SmallDefectNumericalSource iota hinj R)

include source small

/-- The three blocks of defect zero and the block with defect exponent four
exhaust the nonprincipal blocks. The numerical theorem covers all four. -/
theorem nonprincipal_count_eq (b : ActualBlock (k := k) (X := X))
    (hb : b ≠ source.roles 0) :
    Nat.card (BrauerFibre iota hinj R b) = Nat.card (WeightFibre R b) := by
  obtain ⟨i, rfl⟩ := (source.roles_bijective iota hinj R).surjective b
  have hi : i ≠ 0 := fun h => hb (congrArg source.roles h)
  obtain ⟨D, hD, hcard⟩ := source.nonprincipal_defect i hi
  exact small.card_eq _ D hD (hcard.trans_le (nonprincipal_defect_bound i hi))

/-- Cancelling the four actual nonprincipal fibres proves the principal equality. -/
theorem principal_count_eq :
    Nat.card (BrauerFibre iota hinj R (source.roles 0)) =
      Nat.card (WeightFibre R (source.roles 0)) := by
  let := R.1.operations.ambientBlockData.fintypeBlock
  let := source.weight_finite iota hinj R
  exact card_fibre_eq_of_other_fibres (operationsBlock iota hinj R) R.1.weightBlock
    (source.roles 0) (source.total_card_eq iota hinj R)
    (nonprincipal_count_eq iota hinj R source small)

/-- The fixed complete block family satisfies the numerical criterion. -/
theorem all_block_counts (b : ActualBlock (k := k) (X := X)) :
    Nat.card (BrauerFibre iota hinj R b) = Nat.card (WeightFibre R b) := by
  by_cases hb : b = source.roles 0
  · subst b
    exact principal_count_eq iota hinj R source small
  · exact nonprincipal_count_eq iota hinj R source small b hb

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

end ManuscriptIBAW.Sporadic.MonsterNumerical

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
