import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorFibreCancellation

/-!
# Principal fibre cancellation on the actual characteristic-two sector

The sector totals supply finiteness. Fixed fibres over moved blocks are
empty by the existing literal block transport laws.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorTwoNumerical

open ModularRep.FDRepSimpleClassKZero
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierTrivialSectorFibreCancellation

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

theorem principal_total_card_eq (b0 : ActualBlock (k := k) (X := X))
    (htriv : IsCentralCharacterSector (Subgroup.center X) b0.1 (1 : Subgroup.center X →* kˣ))
    (hBr41 : Nat.card {phi : IBr iota // brauerSector iota hinj blocks phi = 1} = 41)
    (hWt41 : Nat.card {w : WeightClass (p := 2) (K := K) (X := X) // weightSector (R := R) w = 1} = 41)
    (hother : ∀ b : ActualBlock (k := k) (X := X), blockSector b = 1 → b ≠ b0 →
      Nat.card {phi : IBr iota // brauerBlock iota hinj blocks phi = b} =
        Nat.card {w : WeightClass (p := 2) (K := K) (X := X) // R.1.weightBlock w = b}) :
    Nat.card {phi : IBr iota // brauerBlock iota hinj blocks phi = b0} =
      Nat.card {w : WeightClass (p := 2) (K := K) (X := X) // R.1.weightBlock w = b0} := by
  classical
  let _ : Fintype (ActualBlock (k := k) (X := X)) := R.1.operations.ambientBlockData.fintypeBlock
  let f := brauerBlock iota hinj blocks
  let g := R.1.weightBlock
  let P := fun b : ActualBlock (k := k) (X := X) => blockSector b = 1
  have hb0 : P b0 := (b0.2.centralCharacterSector_unique (Subgroup.center X) le_rfl htriv).symm
  have hA : Nat.card {phi : IBr iota // P (f phi) ∧ True} = 41 := by
    simpa only [P, f, brauerSector, and_true] using hBr41
  have hC : Nat.card {w : WeightClass (p := 2) (K := K) (X := X) // P (g w) ∧ True} = 41 := by
    simpa only [P, g, weightSector, and_true] using hWt41
  let _ : Finite {phi : IBr iota // P (f phi) ∧ True} :=
    Nat.finite_of_card_ne_zero (by rw [hA]; decide)
  let _ : Finite {w : WeightClass (p := 2) (K := K) (X := X) // P (g w) ∧ True} :=
    Nat.finite_of_card_ne_zero (by rw [hC]; decide)
  have hmain := supportedFixed_fibre_card_eq f g P (fun _ => True) (fun _ => True) b0 hb0
    (hA.trans hC.symm) (fun b hb hne => by simpa only [f, g, and_true] using hother b hb hne)
  simpa only [f, g, and_true] using hmain

theorem principal_fixed_card_eq (b0 : ActualBlock (k := k) (X := X))
    (htriv : IsCentralCharacterSector (Subgroup.center X) b0.1 (1 : Subgroup.center X →* kˣ))
    (tau : MulAut X)
    (hBr31 : Nat.card {phi : IBr iota // brauerSector iota hinj blocks phi = 1 ∧
      MulOpposite.op tau • phi = phi} = 31)
    (hWt31 : Nat.card {w : WeightClass (p := 2) (K := K) (X := X) // weightSector (R := R) w = 1 ∧
      MulOpposite.op tau • w = w} = 31)
    (hother : ∀ b : ActualBlock (k := k) (X := X), blockSector b = 1 → b ≠ b0 →
      MulOpposite.op tau • b = b →
      Nat.card {phi : IBr iota // brauerBlock iota hinj blocks phi = b ∧
        MulOpposite.op tau • phi = phi} =
      Nat.card {w : WeightClass (p := 2) (K := K) (X := X) // R.1.weightBlock w = b ∧
        MulOpposite.op tau • w = w}) :
    Nat.card {phi : IBr iota // brauerBlock iota hinj blocks phi = b0 ∧
      MulOpposite.op tau • phi = phi} =
    Nat.card {w : WeightClass (p := 2) (K := K) (X := X) // R.1.weightBlock w = b0 ∧
      MulOpposite.op tau • w = w} := by
  classical
  let _ : Fintype (ActualBlock (k := k) (X := X)) := R.1.operations.ambientBlockData.fintypeBlock
  let f := brauerBlock iota hinj blocks
  let g := R.1.weightBlock
  let P := fun b : ActualBlock (k := k) (X := X) => blockSector b = 1
  let TA := fun phi : IBr iota => MulOpposite.op tau • phi = phi
  let TC := fun w : WeightClass (p := 2) (K := K) (X := X) => MulOpposite.op tau • w = w
  have hb0 : P b0 := (b0.2.centralCharacterSector_unique (Subgroup.center X) le_rfl htriv).symm
  have hA : Nat.card {phi : IBr iota // P (f phi) ∧ TA phi} = 31 := by
    simpa only [P, f, TA, brauerSector] using hBr31
  have hC : Nat.card {w : WeightClass (p := 2) (K := K) (X := X) // P (g w) ∧ TC w} = 31 := by
    simpa only [P, g, TC, weightSector] using hWt31
  let _ : Finite {phi : IBr iota // P (f phi) ∧ TA phi} :=
    Nat.finite_of_card_ne_zero (by rw [hA]; decide)
  let _ : Finite {w : WeightClass (p := 2) (K := K) (X := X) // P (g w) ∧ TC w} :=
    Nat.finite_of_card_ne_zero (by rw [hC]; decide)
  change Nat.card {phi : IBr iota // f phi = b0 ∧ TA phi} =
    Nat.card {w : WeightClass (p := 2) (K := K) (X := X) // g w = b0 ∧ TC w}
  apply supportedFixed_fibre_card_eq f g P TA TC b0 hb0 (hA.trans hC.symm)
  intro b hb hne
  by_cases hstable : MulOpposite.op tau • b = b
  · simpa only [f, g, TA, TC] using hother b hb hne hstable
  · let _ : IsEmpty {phi : IBr iota // f phi = b ∧ TA phi} := ⟨fun x => by
      have ht := brauerBlock_transport iota hinj blocks (MulOpposite.op tau) x.1
      change f (MulOpposite.op tau • x.1) = MulOpposite.op tau • f x.1 at ht
      have hxblock : f x.1 = b := x.2.1
      have hxfix : MulOpposite.op tau • x.1 = x.1 := x.2.2
      exact hstable (by simpa only [hxblock, hxfix] using ht.symm)⟩
    let _ : IsEmpty {w : WeightClass (p := 2) (K := K) (X := X) // g w = b ∧ TC w} := ⟨fun x => by
      have ht := R.1.weightBlock_transport (MulOpposite.op tau) x.1
      change g (MulOpposite.op tau • x.1) = MulOpposite.op tau • g x.1 at ht
      have hxblock : g x.1 = b := x.2.1
      have hxfix : MulOpposite.op tau • x.1 = x.1 := x.2.2
      exact hstable (by simpa only [hxblock, hxfix] using ht.symm)⟩
    simp

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorTwoNumerical


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
