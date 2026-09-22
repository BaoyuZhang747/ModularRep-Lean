import ModularRep.PaperProofs.SporadicFi24LiteralCarrierBase
import ModularRep.Navarro417DefectSource

/-!
# Numerical input for actual two-blocks of small defect

The external input supplies only equality of actual Brauer and weight
cardinalities for a specified block with a Navarro defect representative
of order at most sixteen. The six-profile consequences are arithmetic.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSmallDefectNumericalSource

open ModularRep
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
  (ActualBlock WeightClass LiteralCarrierAdapter)

universe u
variable {k K X : Type u}
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
variable (iota : PrimeRegularRootEmbedding 2 k K X)
variable (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (R : LiteralCarrierAdapter (p := 2) (k := k) (K := K) (X := X))

/-- The actual block index in the same literal operations catalogue as R. -/
def actualBrauerBlock (phi : IBr iota) : ActualBlock (k := k) (X := X) := by
  let _ : Fintype (ActualBlock (k := k) (X := X)) :=
    R.1.operations.ambientBlockData.fintypeBlock
  exact FDRepSimpleClassKZero.irreducibleBrauerCharacterBlock iota hinj
    R.1.operations.ambientBlockData.blocks phi

abbrev actualBrauerFibre (b : ActualBlock (k := k) (X := X)) :=
  {phi : IBr iota // actualBrauerBlock iota hinj R phi = b}

abbrev actualWeightFibre (b : ActualBlock (k := k) (X := X)) :=
  {w : WeightClass (p := 2) (K := K) (X := X) // R.1.weightBlock w = b}

/-- The actual Navarro central Brauer support criterion for this specified block. -/
def actualHasDefect (b : ActualBlock (k := k) (X := X)) (D : Subgroup X) : Prop :=
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  letI := R.1.operations.ambientBlockData.fintypeBlock
  Navarro411DefectRepresentative (p := 2) R.1.operations.ambientBlockData.blocks b D

/-- The guarded numerical consequence, without equivalence or action data. -/
structure SmallDefectNumericalSource : Prop where
  card_eq : ∀ (b : ActualBlock (k := k) (X := X)) (D : Subgroup X),
    actualHasDefect R b D → Nat.card D ≤ 16 →
      Nat.card (actualBrauerFibre iota hinj R b) = Nat.card (actualWeightFibre R b)

theorem card_eq_of_defect_order
    (small : SmallDefectNumericalSource iota hinj R)
    (b : ActualBlock (k := k) (X := X)) {d : ℕ} (hd : d ≤ 16)
    (hdefect : ∃ D : Subgroup X, actualHasDefect R b D ∧ Nat.card D = d) :
    Nat.card (actualBrauerFibre iota hinj R b) = Nat.card (actualWeightFibre R b) := by
  obtain ⟨D, hD, hcard⟩ := hdefect
  exact small.card_eq b D hD (by rw [hcard]; exact hd)

/-- The six supplied defect orders: 4, 8, 1, 1, 8, 8. -/
def sixDefectOrder (i : Fin 6) : ℕ :=
  match i.1 with
  | 0 => 4
  | 1 => 8
  | 2 => 1
  | 3 => 1
  | _ => 8

/-- The six supplied Brauer cardinalities: 3, 3, 1, 1, 2, 2. -/
def sixBrauerRank (i : Fin 6) : ℕ :=
  match i.1 with
  | 0 => 3
  | 1 => 3
  | 2 => 1
  | 3 => 1
  | _ => 2

theorem sixDefectOrder_le : ∀ i : Fin 6, sixDefectOrder i ≤ 16 := by decide

theorem six_profile_weight_cards
    (small : SmallDefectNumericalSource iota hinj R)
    (b : Fin 6 → ActualBlock (k := k) (X := X))
    (hdefect : ∀ i : Fin 6, ∃ D : Subgroup X,
      actualHasDefect R (b i) D ∧ Nat.card D = sixDefectOrder i)
    (hbrauer : ∀ i : Fin 6,
      Nat.card (actualBrauerFibre iota hinj R (b i)) = sixBrauerRank i) :
    ∀ i : Fin 6, Nat.card (actualWeightFibre R (b i)) = sixBrauerRank i := by
  intro i
  exact (card_eq_of_defect_order iota hinj R small (b i)
    (sixDefectOrder_le i) (hdefect i)).symm.trans (hbrauer i)

theorem six_profile_weight_counts
    (small : SmallDefectNumericalSource iota hinj R)
    (b : Fin 6 → ActualBlock (k := k) (X := X))
    (hdefect : ∀ i : Fin 6, ∃ D : Subgroup X,
      actualHasDefect R (b i) D ∧ Nat.card D = sixDefectOrder i)
    (hbrauer : ∀ i : Fin 6,
      Nat.card (actualBrauerFibre iota hinj R (b i)) = sixBrauerRank i) :
    Nat.card (actualWeightFibre R (b 0)) = 3 ∧
    Nat.card (actualWeightFibre R (b 1)) = 3 ∧
    Nat.card (actualWeightFibre R (b 2)) = 1 ∧
    Nat.card (actualWeightFibre R (b 3)) = 1 ∧
    Nat.card (actualWeightFibre R (b 4)) = 2 ∧
    Nat.card (actualWeightFibre R (b 5)) = 2 := by
  have h := six_profile_weight_cards iota hinj R small b hdefect hbrauer
  exact ⟨h 0, h 1, h 2, h 3, h 4, h 5⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSmallDefectNumericalSource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
