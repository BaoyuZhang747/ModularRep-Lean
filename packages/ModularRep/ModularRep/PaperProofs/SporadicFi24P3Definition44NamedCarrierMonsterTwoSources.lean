import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBabyTwoSources
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFiniteFibres

/-! Literal Monster block roles at two, with bounded access to the exact
five transcript defect exponents. No default row or fibre decomposition
is used. The principal Brauer/weight counts are not source fields. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierMonsterTwoSources

open ModularRep
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
  (ActualBlock WeightClass LiteralCarrierAdapter)
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllPairs
open ModularRep.PaperProofs.SporadicFi24P3Definition44Clause3ACWindow (trivialIBr)
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBabyTwoSources
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFiniteFibres
open ModularRep.PaperProofs.ComputationTranscriptActual

theorem defect_list_length : monsterBlockDefectsFromTranscript.length = 5 := by decide

def defectExponent (i : Fin 5) : Nat :=
  monsterBlockDefectsFromTranscript[i.1]'(by
    rw [defect_list_length]
    exact i.2)

theorem nonprincipal_defect_bound :
    ∀ i : Fin 5, i ≠ 0 → 2 ^ defectExponent i ≤ 16 := by decide

universe u
variable {k K X : Type u}
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
variable (iota : PrimeRegularRootEmbedding 2 k K X)
variable (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (R : LiteralCarrierAdapter (p := 2) (k := k) (K := K) (X := X))

structure MonsterTwoSource where
  roles : Fin 5 → ActualBlock (k := k) (X := X)
  roles_injective : Function.Injective roles
  block_card : Nat.card (ActualBlock (k := k) (X := X)) = 5
  principal_role : roles 0 = operationsBlock iota hinj R (trivialIBr iota)
  brauerTotal : Nat.card (IBr iota) = monsterRegularClassCountFromTranscript
  totalWeights : Nat.card (WeightClass (p := 2) (K := K) (X := X)) = 61
  nonprincipal_defect : ∀ i : Fin 5, i ≠ 0 → ∃ D : Subgroup X,
    actualHasDefect R (roles i) D ∧ Nat.card D = 2 ^ defectExponent i

namespace MonsterTwoSource

variable (source : MonsterTwoSource iota hinj R)

theorem roles_bijective : Function.Bijective source.roles := by
  let := R.1.operations.ambientBlockData.fintypeBlock
  exact (Nat.bijective_iff_injective_and_card source.roles).mpr
    ⟨source.roles_injective, (Nat.card_fin 5).trans source.block_card.symm⟩

include source in
theorem weight_finite : Finite (WeightClass (p := 2) (K := K) (X := X)) :=
  Nat.finite_of_card_ne_zero (by rw [source.totalWeights]; decide)

include source in
theorem total_card_eq :
    Nat.card (IBr iota) = Nat.card (WeightClass (p := 2) (K := K) (X := X)) := by
  rw [source.brauerTotal, source.totalWeights]
  decide

theorem actual_brauer_decomposition :
    letI := R.1.operations.ambientBlockData.fintypeBlock
    Nat.card (IBr iota) = ∑ b : ActualBlock (k := k) (X := X), Nat.card (BrauerFibre iota hinj R b) := by
  let := R.1.operations.ambientBlockData.fintypeBlock
  exact card_eq_fibres (operationsBlock iota hinj R)

include source in
theorem actual_weight_decomposition :
    letI := R.1.operations.ambientBlockData.fintypeBlock
    Nat.card (WeightClass (p := 2) (K := K) (X := X)) =
      ∑ b : ActualBlock (k := k) (X := X), Nat.card (WeightFibre R b) := by
  let := R.1.operations.ambientBlockData.fintypeBlock
  let := source.weight_finite iota hinj R
  exact card_eq_fibres R.1.weightBlock

end MonsterTwoSource

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierMonsterTwoSources



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
