import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSmallDefectNumericalSource
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFixedSingletonBlock
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorFiveBlocks
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllPairs

/-!
# Specified small-block totals and stable singleton signatures

The guarded small-defect numerical input is applied to the same specified
blocks as the Brauer dictionary. Positive Brauer fixed counts derive
block stability. The two non-singleton fixed counts remain intermediate
arguments, supplied by the independent local-row constructions.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSmallDefectPhysicalCounts

open ModularRep ModularRep.FDRepSimpleClassKZero
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierSmallDefectNumericalSource
open SporadicFi24P3Definition44NamedCarrierFixedSingletonBlock
open SporadicFi24P3Definition44NamedCarrierFiveSupportedSignatures
open SporadicFi24P3Definition44NamedCarrierTrivialSectorFiveBlocks
open SporadicFi24P3Definition44NamedCarrierAllPairs

universe u
variable {k K X : Type u}
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
local instance centerFintype : Fintype (Subgroup.center X) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center X) : k)]
variable (iota : PrimeRegularRootEmbedding 2 k K X)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable {I : Type u} [Fintype I] {e : I → k[X]} (blocks : BlockIdempotentDecomposition e)
variable (R : LiteralCarrierAdapter (p := 2) (k := k) (K := K) (X := X))

omit [Invertible (Fintype.card (Subgroup.center X) : k)] in
theorem weight_card_of_actual_brauer_card
    (small : SmallDefectNumericalSource iota hinj R)
    (b : ActualBlock (k := k) (X := X)) {d n : ℕ} (hd : d ≤ 16)
    (hdefect : ∃ D : Subgroup X, actualHasDefect R b D ∧ Nat.card D = d)
    (hbrauer : Nat.card {phi : IBr iota // brauerBlock iota hinj blocks phi = b} = n) :
    Nat.card {w : WeightClass (p := 2) (K := K) (X := X) // R.1.weightBlock w = b} = n := by
  have h := card_eq_of_defect_order iota hinj R small b hd hdefect
  change Nat.card {phi : IBr iota // operationsBlock iota hinj R phi = b} =
    Nat.card {w : WeightClass (p := 2) (K := K) (X := X) // R.1.weightBlock w = b} at h
  have h' : Nat.card {phi : IBr iota // brauerBlock iota hinj blocks phi = b} =
      Nat.card {w : WeightClass (p := 2) (K := K) (X := X) // R.1.weightBlock w = b} := by
    simpa only [operationsBlock_eq iota hinj R blocks] using h
  exact h'.symm.trans hbrauer

variable (tau : MulAut X)
variable (roles : Fin 5 ≃ {b : ActualBlock (k := k) (X := X) // blockSector b = 1})
variable (hBrOther : ∀ j : Fin 4,
  actualBrauerSignature iota hinj blocks tau (roles j.succ).1 = nonprincipalSignature j)

include hBrOther in
theorem nonprincipal_blocks_fixed (j : Fin 4) :
    MulOpposite.op tau • (roles j.succ).1 = (roles j.succ).1 := by
  have hBrFixed : Nat.card {phi : IBr iota //
      brauerBlock iota hinj blocks phi = (roles j.succ).1 ∧ MulOpposite.op tau • phi = phi} =
      (nonprincipalSignature j).2 := congrArg Prod.snd (hBrOther j)
  apply block_fixed_of_brauer_fixed_card_pos iota hinj blocks tau (roles j.succ).1
  rw [hBrFixed]
  exact (by decide : ∀ j : Fin 4, 0 < (nonprincipalSignature j).2) j

variable (small : SmallDefectNumericalSource iota hinj R)
variable (hDefectTrivial : ∀ j : Fin 4, ∃ D : Subgroup X,
  actualHasDefect R (roles j.succ).1 D ∧ Nat.card D =
    (if j = 0 then 4 else if j = 1 then 8 else 1))

include hBrOther small hDefectTrivial in
theorem nonprincipal_weight_totals (j : Fin 4) :
    Nat.card {w : WeightClass (p := 2) (K := K) (X := X) //
      R.1.weightBlock w = (roles j.succ).1} = (nonprincipalSignature j).1 := by
  exact weight_card_of_actual_brauer_card iota hinj blocks R small (roles j.succ).1
    (by split_ifs <;> decide) (hDefectTrivial j) (congrArg Prod.fst (hBrOther j))

include hBrOther small hDefectTrivial in
theorem nonprincipal_weight_signatures_of_two_fixed_counts
    (hK4 : Nat.card {w : WeightClass (p := 2) (K := K) (X := X) //
      R.1.weightBlock w = (roles 1).1 ∧ MulOpposite.op tau • w = w} = 1)
    (hD8 : Nat.card {w : WeightClass (p := 2) (K := K) (X := X) //
      R.1.weightBlock w = (roles 2).1 ∧ MulOpposite.op tau • w = w} = 3) :
    ∀ j : Fin 4, actualWeightSignature R tau (roles j.succ).1 = nonprincipalSignature j := by
  have hTotal := nonprincipal_weight_totals iota hinj blocks R tau roles hBrOther small hDefectTrivial
  have hBlockFixed := nonprincipal_blocks_fixed iota hinj blocks tau roles hBrOther
  intro j
  unfold actualWeightSignature fibreSignature
  apply Prod.ext
  · exact hTotal j
  · by_cases h0 : j = 0
    · subst j
      exact hK4
    · by_cases h1 : j = 1
      · subst j
        exact hD8
      · have ht : Nat.card {w : WeightClass (p := 2) (K := K) (X := X) //
            R.1.weightBlock w = (roles j.succ).1} = 1 := by
          simpa only [nonprincipalSignature, if_neg h0, if_neg h1] using hTotal j
        simpa only [nonprincipalSignature, if_neg h0, if_neg h1] using
          (weight_fixed_card_one_of_singleton R tau (roles j.succ).1 (hBlockFixed j) ht)

include small in
theorem faithful_small_weight_totals
    (faithfulRoles : ∀ nu : CentralSector (k := k) (X := X), nu ≠ 1 →
      Fin 2 ≃ {b : ActualBlock (k := k) (X := X) // blockSector b = nu})
    (hDefectFaithful : ∀ (nu : CentralSector (k := k) (X := X)) (hnu : nu ≠ 1),
      ∃ D : Subgroup X, actualHasDefect R (faithfulRoles nu hnu 1).1 D ∧ Nat.card D = 8)
    (hBrSmall : ∀ (nu : CentralSector (k := k) (X := X)) (hnu : nu ≠ 1),
      Nat.card {phi : IBr iota // brauerBlock iota hinj blocks phi = (faithfulRoles nu hnu 1).1} = 2) :
    ∀ (nu : CentralSector (k := k) (X := X)) (hnu : nu ≠ 1),
      Nat.card {w : WeightClass (p := 2) (K := K) (X := X) //
        R.1.weightBlock w = (faithfulRoles nu hnu 1).1} = 2 := by
  intro nu hnu
  exact weight_card_of_actual_brauer_card iota hinj blocks R small
    (faithfulRoles nu hnu 1).1 (by decide) (hDefectFaithful nu hnu) (hBrSmall nu hnu)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSmallDefectPhysicalCounts


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
