import ModularRep.PaperProofs.SporadicFi24LiteralCarrierBase

/-! # Positive Brauer fixed counts and invariant singleton weight blocks -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFixedSingletonBlock

open ModularRep
open SporadicFi24CentralSectorAssemblyLemma56Actual

universe u

theorem fixed_card_one_of_invariant_singleton {W : Type*}
    (T : W → W) (P : W → Prop) (hP : ∀ w, P w → P (T w))
    (hcard : Nat.card {w : W // P w} = 1) :
    Nat.card {w : W // P w ∧ T w = w} = 1 := by
  have hsub : Subsingleton {w : W // P w} := (Nat.card_eq_one_iff_unique.mp hcard).1
  have hfix (w : W) (hw : P w) : T w = w :=
    congrArg Subtype.val (hsub.elim ⟨T w, hP w hw⟩ ⟨w, hw⟩)
  let E : {w : W // P w ∧ T w = w} ≃ {w : W // P w} :=
    { toFun := fun w => ⟨w.1, w.2.1⟩
      invFun := fun w => ⟨w.1, w.2, hfix w.1 w.2⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }
  exact (Nat.card_congr E).trans hcard

theorem weight_fixed_card_one_of_singleton
    {p : ℕ} {k K X : Type u} [Field k] [Field K] [CharZero K]
    [Group X] [Fintype X]
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
    (tau : MulAut X) (b : ActualBlock (k := k) (X := X))
    (hb : MulOpposite.op tau • b = b)
    (hcard : Nat.card {w : WeightClass (p := p) (K := K) (X := X) // R.1.weightBlock w = b} = 1) :
    Nat.card {w : WeightClass (p := p) (K := K) (X := X) //
      R.1.weightBlock w = b ∧ MulOpposite.op tau • w = w} = 1 := by
  apply fixed_card_one_of_invariant_singleton (fun w => MulOpposite.op tau • w)
    (fun w => R.1.weightBlock w = b) _ hcard
  intro w hw
  rw [R.1.weightBlock_transport, hw, hb]

theorem block_fixed_of_brauer_fixed_card_pos
    {p : ℕ} {k K X : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group X] [Fintype X]
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
    {I : Type u} [Fintype I] {e : I → k[X]} (blocks : BlockIdempotentDecomposition e)
    (tau : MulAut X) (b : ActualBlock (k := k) (X := X))
    (hpos : 0 < Nat.card {phi : IBr iota //
      brauerBlock iota hinj blocks phi = b ∧ MulOpposite.op tau • phi = phi}) :
    MulOpposite.op tau • b = b := by
  obtain ⟨x⟩ := (Nat.card_pos_iff.mp hpos).1
  calc
    MulOpposite.op tau • b = MulOpposite.op tau • brauerBlock iota hinj blocks x.1 :=
      congrArg (fun c : ActualBlock (k := k) (X := X) => MulOpposite.op tau • c) x.2.1.symm
    _ = brauerBlock iota hinj blocks (MulOpposite.op tau • x.1) :=
      (brauerBlock_transport iota hinj blocks (MulOpposite.op tau) x.1).symm
    _ = brauerBlock iota hinj blocks x.1 := congrArg (brauerBlock iota hinj blocks) x.2.2
    _ = b := x.2.1

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFixedSingletonBlock


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
