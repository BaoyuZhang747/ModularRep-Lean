import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRootSectorWeightAssembly
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulLocalTableAtTwo

/-!
# Original sector total from the faithful ordinary Table 8 column

The input binds the 34 counts of actual local ordinary characters over
one retained-root central character. Restricted-row exhaustivity and
the central-restriction theorem derive the original weight count.
An empty row remains in the complete radical index.
-/

noncomputable section
open scoped BigOperators

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulSectorTable8AtTwo

open ModularRep ModularRep.CharacterWeight
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierRootSectorWeightAssembly
open SporadicFi24P3Definition44NamedCarrierFaithfulLocalTableAtTwo

universe u w
variable {k K X : Type u}
variable [Field k] [Field K] [CharZero K] [Group X] [Fintype X]
variable (iota : PrimeRegularRootEmbedding 2 k K X)
variable (nu : CentralSector (k := k) (X := X))
variable {Row : Fin 34 → Type w}
variable (C : SectorCatalogue iota nu (Fin 34) Row)

theorem table8_local_row_sum
    (htable : (List.ofFn (fun i : Fin 34 =>
      Nat.card (RootSectorLocal iota nu (C.representative i)))).Perm
        correctedFi24FaithfulTable8AtTwo) :
    (∑ i : Fin 34, Nat.card (Row i)) = 25 := by
  calc
    (∑ i : Fin 34, Nat.card (Row i)) =
        ∑ i : Fin 34, Nat.card (RootSectorLocal iota nu (C.representative i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Nat.card_congr (C.localEquiv i)
    _ = (List.ofFn (fun i : Fin 34 =>
        Nat.card (RootSectorLocal iota nu (C.representative i)))).sum := List.sum_ofFn.symm
    _ = correctedFi24FaithfulTable8AtTwo.sum := htable.sum_eq
    _ = 25 := correctedFi24FaithfulTable8AtTwo_sum

theorem local_row_isEmpty_of_card_zero [∀ i, Finite (Row i)] (i : Fin 34)
    (hzero : Nat.card (RootSectorLocal iota nu (C.representative i)) = 0) :
    IsEmpty (RootSectorLocal iota nu (C.representative i)) := by
  let _ : Finite (RootSectorLocal iota nu (C.representative i)) :=
    (C.localEquiv i).finite_iff.mp inferInstance
  let _ : Fintype (RootSectorLocal iota nu (C.representative i)) := Fintype.ofFinite _
  apply Fintype.card_eq_zero_iff.mp
  simpa only [Nat.card_eq_fintype_card] using hzero

variable [CharP k 2] [IsAlgClosed k]
local instance centerFintype : Fintype (Subgroup.center X) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center X) : k)]
variable (R : LiteralCarrierAdapter (p := 2) (k := k) (K := K) (X := X))
variable (CU : ∀ i (theta : LocalDefectZeroCharacter (K := K) (C.representative i)),
  CanonicalRawReduction iota (characterWeightAt iota.prime (C.representative i) theta))
variable (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)

include C CU compatibility in
theorem actualSectorCount_of_table8 [∀ i, Finite (Row i)]
    (htable : (List.ofFn (fun i : Fin 34 =>
      Nat.card (RootSectorLocal iota nu (C.representative i)))).Perm
        correctedFi24FaithfulTable8AtTwo) :
    Nat.card {weight : WeightClass (p := 2) (K := K) (X := X) //
      weightSector (R := R) weight = nu} = 25 :=
  (C.weightSector_card R CU compatibility).trans (table8_local_row_sum iota nu C htable)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulSectorTable8AtTwo


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
