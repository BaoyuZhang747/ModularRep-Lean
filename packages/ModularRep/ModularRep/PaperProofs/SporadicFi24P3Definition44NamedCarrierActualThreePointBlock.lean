import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSingletonFibreFixedPoints
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualNumericalEquiv

/-! A local three-point block count from two invariant singleton radical
rows. This uses actual weight conjugacy classes and their canonical radical
projection; the named D8-block and local-row bindings remain explicit. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualThreePointBlock

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllPairs
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualTwoActions
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSingletonFibreFixedPoints

universe u

variable {k K X : Type u}
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
variable (R : LiteralCarrierAdapter (p := 2) (k := k) (K := K) (X := X))
variable (tau : MulAut X)
variable (decomposition : ∀ a : MulAut X, ∃ x : X,
  a = MulAut.conj x ∨ a = MulAut.conj x * tau)
variable (b : ActualBlock (k := k) (X := X))
variable (ra rb : RadicalConjugacyClass (p := 2) (G := X))
variable (hb : MulOpposite.op tau • b = b)
variable (hra : MulOpposite.op tau • ra = ra) (hrb : MulOpposite.op tau • rb = rb)
variable (hne : ra ≠ rb)
variable (hrowa : Nat.card {w : WeightClass (p := 2) (K := K) (X := X) //
  R.1.weightBlock w = b ∧ radicalClass w = ra} = 1)
variable (hrowb : Nat.card {w : WeightClass (p := 2) (K := K) (X := X) //
  R.1.weightBlock w = b ∧ radicalClass w = rb} = 1)
variable (hweightTotal : Nat.card {w : WeightClass (p := 2) (K := K) (X := X) //
  R.1.weightBlock w = b} = 3)

include decomposition ra rb hb hra hrb hne hrowa hrowb hweightTotal

omit [CharP k 2] [IsAlgClosed k] in
theorem weight_fixed_card_three :
    Nat.card {w : WeightClass (p := 2) (K := K) (X := X) //
      R.1.weightBlock w = b ∧ MulOpposite.op tau • w = w} = 3 :=
  fixed_card_three_of_two_singleton_labels R.1.weightBlock radicalClass
    R.1.weightBlock_transport radicalClass_equivariant
    (MulOpposite.op tau) (weight_tau_involutive (p := 2) (K := K) tau decomposition)
    b ra rb hb hra hrb hne hrowa hrowb hweightTotal

theorem block_counts_eq
    (iota : PrimeRegularRootEmbedding 2 k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (hbrauerTotal : Nat.card {phi : IBr iota // operationsBlock iota hinj R phi = b} = 3)
    (hbrauerFixed : Nat.card {phi : IBr iota // operationsBlock iota hinj R phi = b ∧
      MulOpposite.op tau • phi = phi} = 3) :
    (Nat.card {phi : IBr iota // operationsBlock iota hinj R phi = b} =
      Nat.card {w : WeightClass (p := 2) (K := K) (X := X) // R.1.weightBlock w = b}) ∧
    (Nat.card {phi : IBr iota // operationsBlock iota hinj R phi = b ∧
      MulOpposite.op tau • phi = phi} =
      Nat.card {w : WeightClass (p := 2) (K := K) (X := X) // R.1.weightBlock w = b ∧
        MulOpposite.op tau • w = w}) :=
  ⟨hbrauerTotal.trans hweightTotal.symm,
    hbrauerFixed.trans
      (weight_fixed_card_three R tau decomposition b ra rb hb hra hrb hne hrowa hrowb hweightTotal).symm⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualThreePointBlock


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
