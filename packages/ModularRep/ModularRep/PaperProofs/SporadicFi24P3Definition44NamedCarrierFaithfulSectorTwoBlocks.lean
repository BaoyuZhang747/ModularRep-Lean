import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorFiveBlocks
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTwoSupportedTotals

/-! # Actual two-block faithful sector counts -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulSectorTwoBlocks

open ModularRep.FDRepSimpleClassKZero
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierTwoSupportedTotals

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

theorem faithful_two_block_counts
    (nu : CentralSector (k := k) (X := X))
    (roles : Fin 2 ≃ {b : ActualBlock (k := k) (X := X) // blockSector b = nu})
    (hBr25 : Nat.card {phi : IBr iota // brauerSector iota hinj blocks phi = nu} = 25)
    (hWt25 : Nat.card {w : WeightClass (p := 2) (K := K) (X := X) //
      weightSector (R := R) w = nu} = 25)
    (hBr2 : Nat.card {phi : IBr iota // brauerBlock iota hinj blocks phi = (roles 1).1} = 2)
    (hWt2 : Nat.card {w : WeightClass (p := 2) (K := K) (X := X) //
      R.1.weightBlock w = (roles 1).1} = 2) :
    (Nat.card {phi : IBr iota // brauerBlock iota hinj blocks phi = (roles 0).1} = 23 ∧
      Nat.card {w : WeightClass (p := 2) (K := K) (X := X) //
        R.1.weightBlock w = (roles 0).1} = 23) ∧
    ∀ b : ActualBlock (k := k) (X := X), blockSector b = nu →
      Nat.card {phi : IBr iota // brauerBlock iota hinj blocks phi = b} =
        Nat.card {w : WeightClass (p := 2) (K := K) (X := X) // R.1.weightBlock w = b} := by
  have hBr23 := twoSupported_large_card (brauerBlock iota hinj blocks)
    (fun b => blockSector b = nu) roles (by simpa only [brauerSector] using hBr25) hBr2
  have hWt23 := twoSupported_large_card R.1.weightBlock
    (fun b => blockSector b = nu) roles (by simpa only [weightSector] using hWt25) hWt2
  refine ⟨⟨hBr23, hWt23⟩, ?_⟩
  intro b hb
  obtain ⟨i, hi⟩ := roles.surjective ⟨b, hb⟩
  have hv : (roles i).1 = b := congrArg Subtype.val hi
  rw [← hv]
  refine Fin.cases (hBr23.trans hWt23.symm) ?_ i
  intro j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  exact hBr2.trans hWt2.symm

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulSectorTwoBlocks


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
