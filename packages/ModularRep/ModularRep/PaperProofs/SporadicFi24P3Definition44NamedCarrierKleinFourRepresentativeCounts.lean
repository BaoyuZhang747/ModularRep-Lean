import ModularRep.PaperProofs.SporadicFi24LiteralCarrierBase
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOrdinaryRowAllocation
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeFixedPoints
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFixedRowComplement

/-!
# Complementary ordinary allocations give the Klein-four row counts

Both target primitives are tested by their actual interval evaluations.
Raw block membership and the complement identity are derived in the proof.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierKleinFourRepresentativeCounts

open ModularRep ModularRep.CharacterWeight
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierOrdinaryRowAllocation
open SporadicFi24P3Definition44NamedCarrierRepresentativeFixedPoints
open SporadicFi24P3Definition44NamedCarrierFixedRowComplement
open TypeBCentralKernelNormalizerInertia

universe u v

theorem representative_counts_of_complementary_catalogue
    {k K G : Type u} {Row : Type v}
    [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
    [Group G] [Fintype G]
    (iota : PrimeRegularRootEmbedding 2 k K G)
    (R : LiteralCarrierAdapter (p := 2) (k := k) (K := K) (X := G))
    (Q : RadicalSubgroup (p := 2) (G := G))
    (bD8 bK4 : ActualBlock (k := k) (X := G))
    (rows : Row → LocalDefectZeroCharacter (K := K) Q)
    (rowInjective : Function.Injective rows) (rowSurjective : Function.Surjective rows)
    (C : ∀ r : Row, CanonicalRawReduction iota (characterWeightAt iota.prime Q (rows r)))
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (S414 : NormalizerIntervalSource R.1.operations Q) (hit : Row → Bool)
    (evaluationD8 : ∀ r : Row,
      intervalEvaluation R.1.operations Q
        (NavarroLocalReductionInflationBlockCompatibility.normalizerBrauerBlock
          R.1.operations Q.1 (C r).normalizerRoot (C r).localBrauer) bD8 =
        if hit r then (1 : k) else 0)
    (evaluationK4 : ∀ r : Row,
      intervalEvaluation R.1.operations Q
        (NavarroLocalReductionInflationBlockCompatibility.normalizerBrauerBlock
          R.1.operations Q.1 (C r).normalizerRoot (C r).localBrauer) bK4 =
        if !(hit r) then (1 : k) else 0)
    (alpha : MulAut G) (stable : Q.1.comap alpha.toMonoidHom = Q.1)
    (hbD8 : MulOpposite.op alpha • bD8 = bD8)
    (hrows : Nat.card Row = 4) (hhit : Nat.card {r : Row // hit r = true} = 1)
    (hfixedRows : Nat.card {r : Row //
      OrdinaryIrreducibleCharacter.twist K _ (rows r).1
        (localAut Q.1 alpha stable) = (rows r).1} = 2) :
    Nat.card (RepresentativeDZ iota.prime R.1 Q bK4) = 3 ∧
      Nat.card {theta : RepresentativeDZ iota.prime R.1 Q bK4 //
        OrdinaryIrreducibleCharacter.twist K _ theta.1.1
          (localAut Q.1 alpha stable) = theta.1.1} = 1 := by
  classical
  let E : Row ≃ LocalDefectZeroCharacter (K := K) Q :=
    Equiv.ofBijective rows ⟨rowInjective, rowSurjective⟩
  let A8 := hitRowsEquivRepresentativeDZ iota R.1 Q bD8
    rows rowInjective rowSurjective C compatibility S414 hit evaluationD8
  let A4 := hitRowsEquivRepresentativeDZ iota R.1 Q bK4
    rows rowInjective rowSurjective C compatibility S414 (fun r => !(hit r)) evaluationK4
  let B := fun theta : LocalDefectZeroCharacter (K := K) Q =>
    R.1.operations.rawWeightBlock (characterWeightAt iota.prime Q theta)
  let P := fun theta : LocalDefectZeroCharacter (K := K) Q => B theta = bD8
  let T := localTwistAt (K := K) iota.prime Q alpha stable
  have allocationD8 (r : Row) : B (rows r) = bD8 ↔ hit r = true := by
    constructor
    · intro h
      obtain ⟨s, hs⟩ := A8.surjective ⟨rows r, h⟩
      have hsr : s.1 = r := rowInjective (congrArg Subtype.val hs)
      simpa only [hsr] using s.2
    · intro h
      exact (A8 ⟨r, h⟩).2
  have allocationK4 (r : Row) : B (rows r) = bK4 ↔ (!hit r) = true := by
    constructor
    · intro h
      obtain ⟨s, hs⟩ := A4.surjective ⟨rows r, h⟩
      have hsr : s.1 = r := rowInjective (congrArg Subtype.val hs)
      simpa only [hsr] using s.2
    · intro h
      exact (A4 ⟨r, h⟩).2
  have complement (theta : LocalDefectZeroCharacter (K := K) Q) :
      ¬ P theta ↔ B theta = bK4 := by
    obtain ⟨r, rfl⟩ := rowSurjective theta
    change ¬ B (rows r) = bD8 ↔ B (rows r) = bK4
    rw [allocationD8 r, allocationK4 r]
    cases hit r <;> simp
  let Ecomp : {theta : LocalDefectZeroCharacter (K := K) Q // ¬ P theta} ≃
      RepresentativeDZ iota.prime R.1 Q bK4 := Equiv.subtypeEquivRight complement
  have htotalLocal : Nat.card (LocalDefectZeroCharacter (K := K) Q) = 4 :=
    (Nat.card_congr E).symm.trans hrows
  have hsingleton : Nat.card {theta : LocalDefectZeroCharacter (K := K) Q // P theta} = 1 :=
    (Nat.card_congr A8).symm.trans hhit
  have hpreserve : ∀ theta : LocalDefectZeroCharacter (K := K) Q,
      P theta → P (T theta) := by
    intro theta htheta
    change B theta = bD8 at htheta
    change B (T theta) = bD8
    exact (localTwistAt_block iota.prime R.1 Q alpha stable theta).trans
      ((congrArg (fun b => MulOpposite.op alpha • b) htheta).trans hbD8)
  let EfixedRows :
      {r : Row // OrdinaryIrreducibleCharacter.twist K _ (rows r).1
        (localAut Q.1 alpha stable) = (rows r).1} ≃
      {theta : LocalDefectZeroCharacter (K := K) Q // T theta = theta} :=
    E.subtypeEquiv (fun r => (localTwistAt_fixed_iff iota.prime Q alpha stable (rows r)).symm)
  have hfixedLocal : Nat.card
      {theta : LocalDefectZeroCharacter (K := K) Q // T theta = theta} = 2 :=
    (Nat.card_congr EfixedRows).symm.trans hfixedRows
  have htotalComplement :
      Nat.card {theta : LocalDefectZeroCharacter (K := K) Q // ¬ P theta} = 3 :=
    compl_card_three_of_card_four P htotalLocal hsingleton
  have hfixedComplement :
      Nat.card {theta : LocalDefectZeroCharacter (K := K) Q // ¬ P theta ∧ T theta = theta} = 1 :=
    fixed_compl_card_one_of_invariant_singleton T P hpreserve hsingleton hfixedLocal
  let EfixedComplement :
      {theta : LocalDefectZeroCharacter (K := K) Q // ¬ P theta ∧ T theta = theta} ≃
      {theta : RepresentativeDZ iota.prime R.1 Q bK4 //
        OrdinaryIrreducibleCharacter.twist K _ theta.1.1
          (localAut Q.1 alpha stable) = theta.1.1} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun theta : LocalDefectZeroCharacter (K := K) Q => ¬ P theta)
      (fun theta => T theta = theta)).symm.trans
        (Ecomp.subtypeEquiv (fun theta => localTwistAt_fixed_iff iota.prime Q alpha stable theta.1))
  exact ⟨(Nat.card_congr Ecomp).symm.trans htotalComplement,
    (Nat.card_congr EfixedComplement).symm.trans hfixedComplement⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierKleinFourRepresentativeCounts


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
