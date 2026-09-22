import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllPairs
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTwoFibre
import ModularRep.PaperProofs.ComputationTranscriptActual
import ModularRep.Navarro417DefectSource

/-! Literal source boundary for Baby at two.
The two actual block roles are distinct and the actual set of blocks has
cardinality two. Row zero is the block of the trivial Brauer character.
Ranks are bound to the existing canonical transcript values; the other
block has an actual defect representative of order eight. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBabyTwoSources

open ModularRep
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
  (ActualBlock WeightClass LiteralCarrierAdapter)
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllPairs
open ModularRep.PaperProofs.SporadicFi24P3Definition44Clause3ACWindow (trivialIBr)
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTwoFibre
open ModularRep.PaperProofs.ComputationTranscriptActual

universe u
variable {k K X : Type u}
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
variable (iota : PrimeRegularRootEmbedding 2 k K X)
variable (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (R : LiteralCarrierAdapter (p := 2) (k := k) (K := K) (X := X))

abbrev BrauerFibre (b : ActualBlock (k := k) (X := X)) :=
  {phi : IBr iota // operationsBlock iota hinj R phi = b}

abbrev WeightFibre (b : ActualBlock (k := k) (X := X)) :=
  {w : WeightClass (p := 2) (K := K) (X := X) // R.1.weightBlock w = b}

def actualHasDefect (b : ActualBlock (k := k) (X := X)) (D : Subgroup X) : Prop :=
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  letI := R.1.operations.ambientBlockData.fintypeBlock
  Navarro411DefectRepresentative (p := 2) R.1.operations.ambientBlockData.blocks b D

structure BabyTwoSource where
  roles : Fin 2 → ActualBlock (k := k) (X := X)
  roles_injective : Function.Injective roles
  block_card : Nat.card (ActualBlock (k := k) (X := X)) = 2
  principal_role : roles 0 = operationsBlock iota hinj R (trivialIBr iota)
  brauerRanks :
    [Nat.card (BrauerFibre iota hinj R (roles 0)),
      Nat.card (BrauerFibre iota hinj R (roles 1))] =
      babyBrauerBlockRanksFromTranscript
  totalWeights : Nat.card (WeightClass (p := 2) (K := K) (X := X)) = 27
  nonprincipal_defect : ∃ D : Subgroup X,
    actualHasDefect R (roles 1) D ∧ Nat.card D = 8

/-- Only the numerical consequence of the published small-defect theorem. -/
structure SmallDefectNumericalSource : Prop where
  card_eq : ∀ (b : ActualBlock (k := k) (X := X)) (D : Subgroup X),
    actualHasDefect R b D → Nat.card D ≤ 16 →
      Nat.card (BrauerFibre iota hinj R b) = Nat.card (WeightFibre R b)

namespace BabyTwoSource

variable (source : BabyTwoSource iota hinj R)

theorem roles_bijective : Function.Bijective source.roles :=
  two_roles_bijective source.roles source.roles_injective source.block_card

theorem roles_cover (b : ActualBlock (k := k) (X := X)) :
    b = source.roles 0 ∨ b = source.roles 1 :=
  two_roles_cover source.roles source.roles_injective source.block_card b

theorem roles_distinct : source.roles 0 ≠ source.roles 1 := by
  intro h
  have : (0 : Fin 2) = 1 := source.roles_injective h
  exact (by decide : (0 : Fin 2) ≠ 1) this

theorem brauer_ranks :
    Nat.card (BrauerFibre iota hinj R (source.roles 0)) = 25 ∧
      Nat.card (BrauerFibre iota hinj R (source.roles 1)) = 2 := by
  have h := source.brauerRanks.trans baby_transcript_counts_exact.2.1
  exact ⟨(List.cons.inj h).1, (List.cons.inj (List.cons.inj h).2).1⟩

include source in
theorem weight_finite : Finite (WeightClass (p := 2) (K := K) (X := X)) :=
  Nat.finite_of_card_ne_zero (by rw [source.totalWeights]; decide)

theorem actual_brauer_decomposition :
    Nat.card (IBr iota) = Nat.card (BrauerFibre iota hinj R (source.roles 0)) +
      Nat.card (BrauerFibre iota hinj R (source.roles 1)) :=
  card_eq_two_fibres (operationsBlock iota hinj R) _ _
    (source.roles_distinct iota hinj R) (source.roles_cover iota hinj R)

theorem actual_weight_decomposition :
    Nat.card (WeightClass (p := 2) (K := K) (X := X)) =
      Nat.card (WeightFibre R (source.roles 0)) + Nat.card (WeightFibre R (source.roles 1)) := by
  let := source.weight_finite iota hinj R
  exact card_eq_two_fibres R.1.weightBlock _ _
    (source.roles_distinct iota hinj R) (source.roles_cover iota hinj R)

end BabyTwoSource

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBabyTwoSources


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
