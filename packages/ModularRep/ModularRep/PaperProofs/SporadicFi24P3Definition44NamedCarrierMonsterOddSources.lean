import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierJ4Numerical

/-! The uniform An--Wilson Monster count is used only for p >= 3.
Its weight fibre includes every radical representative belonging to the
actual primitive block; it is not restricted to a defect-group radical. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierMonsterOddSources

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierJ4Numerical

universe u
variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

local instance brauerFintype (iota : PrimeRegularRootEmbedding p k K X) : Fintype (IBr iota) :=
  Fintype.ofFinite _

variable [Fintype (WeightClass (p := p) (K := K) (X := X))]
variable (iota : PrimeRegularRootEmbedding p k K X)
variable (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (R : LiteralBlockSource (p := p) (k := k) (K := K) (X := X))

structure MonsterOddNumericalSource : Prop where
  existsDefect : ∀ b : ActualBlock (k := k) (X := X),
    ∃ D : Subgroup X, actualHasDefect iota R b D
  cyclicCardEq : ∀ (b : ActualBlock (k := k) (X := X)) (D : Subgroup X),
    actualHasDefect iota R b D → IsCyclic D → blockCardEq iota hinj R b
  noncyclicCardEq : 3 ≤ p →
    ∀ (b : ActualBlock (k := k) (X := X)) (D : Subgroup X),
      actualHasDefect iota R b D → ¬ IsCyclic D → blockCardEq iota hinj R b

theorem MonsterOddNumericalSource.toDefectCounts
    (source : MonsterOddNumericalSource iota hinj R) (hpOdd : 3 ≤ p) :
    CyclicNoncyclicNumericalSource iota hinj R where
  existsDefect := source.existsDefect
  cyclicCardEq := source.cyclicCardEq
  noncyclicCardEq := source.noncyclicCardEq hpOdd

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierMonsterOddSources


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
