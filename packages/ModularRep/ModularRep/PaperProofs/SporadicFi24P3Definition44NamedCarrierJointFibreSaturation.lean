import Mathlib.SetTheory.Cardinal.Finite
import ModularRep.PaperProofs.CharacterWeightRepresentativeFibre

/-!
# A full-size joint fibre exhausts the actual block

The map is the literal inclusion of weight conjugacy classes. Both total
cardinalities are independent inputs; fixed-point transport is derived.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierJointFibreSaturation

open ModularRep ModularRep.CharacterWeight

def equivOfInjectiveOfNatCardEq {A B : Type*}
    (f : A → B) (hf : Function.Injective f)
    (hcard : Nat.card A = Nat.card B) (hne : Nat.card B ≠ 0) : A ≃ B := by
  let : Finite B := Nat.finite_of_card_ne_zero hne
  exact Equiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf, hcard⟩)

universe u
variable {p : ℕ} {k K G Block : Type u}
variable [Field k] [Field K] [CharZero K] [Group G] [Fintype G]
variable [MulAction (MulAut G)ᵐᵒᵖ Block]

def weightBlockRadicalEquivBlock
    (S : LocalBlockInductionSource
      (p := p) (k := k) (K := K) (G := G) (Block := Block))
    (Q : RadicalSubgroup (p := p) (G := G)) (b : Block)
    (hjoint : Nat.card (WeightBlockRadicalFibre S Q b) = 3)
    (hblock : Nat.card {w : ConjugacyClass (p := p) (K := K) (G := G) //
      S.weightBlock w = b} = 3) :
    WeightBlockRadicalFibre S Q b ≃
      {w : ConjugacyClass (p := p) (K := K) (G := G) // S.weightBlock w = b} :=
  equivOfInjectiveOfNatCardEq (fun w => ⟨w.1, w.2.1⟩)
    (fun x y h => by
      apply Subtype.ext
      exact congrArg
        (fun w : {w : ConjugacyClass (p := p) (K := K) (G := G) // S.weightBlock w = b} => w.1) h)
    (hjoint.trans hblock.symm) (by rw [hblock]; decide)

theorem weightBlockRadicalEquivBlock_apply_val
    (S : LocalBlockInductionSource
      (p := p) (k := k) (K := K) (G := G) (Block := Block))
    (Q : RadicalSubgroup (p := p) (G := G)) (b : Block)
    (hjoint : Nat.card (WeightBlockRadicalFibre S Q b) = 3)
    (hblock : Nat.card {w : ConjugacyClass (p := p) (K := K) (G := G) //
      S.weightBlock w = b} = 3) (w : WeightBlockRadicalFibre S Q b) :
    (weightBlockRadicalEquivBlock S Q b hjoint hblock w).1 = w.1 := rfl

def weightBlockRadicalFixedEquivBlock
    (S : LocalBlockInductionSource
      (p := p) (k := k) (K := K) (G := G) (Block := Block))
    (Q : RadicalSubgroup (p := p) (G := G)) (b : Block)
    (hjoint : Nat.card (WeightBlockRadicalFibre S Q b) = 3)
    (hblock : Nat.card {w : ConjugacyClass (p := p) (K := K) (G := G) //
      S.weightBlock w = b} = 3) (alpha : MulAut G) :
    {w : WeightBlockRadicalFibre S Q b // MulOpposite.op alpha • w.1 = w.1} ≃
      {w : ConjugacyClass (p := p) (K := K) (G := G) //
        S.weightBlock w = b ∧ MulOpposite.op alpha • w = w} :=
  ((weightBlockRadicalEquivBlock S Q b hjoint hblock).subtypeEquiv
    (fun _ => Iff.rfl)).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun w : ConjugacyClass (p := p) (K := K) (G := G) => S.weightBlock w = b)
        (fun w : ConjugacyClass (p := p) (K := K) (G := G) =>
          MulOpposite.op alpha • w = w))

theorem weightBlock_fixed_card_one
    (S : LocalBlockInductionSource
      (p := p) (k := k) (K := K) (G := G) (Block := Block))
    (Q : RadicalSubgroup (p := p) (G := G)) (b : Block)
    (hjoint : Nat.card (WeightBlockRadicalFibre S Q b) = 3)
    (hblock : Nat.card {w : ConjugacyClass (p := p) (K := K) (G := G) //
      S.weightBlock w = b} = 3) (alpha : MulAut G)
    (hfixed : Nat.card {w : WeightBlockRadicalFibre S Q b //
      MulOpposite.op alpha • w.1 = w.1} = 1) :
    Nat.card {w : ConjugacyClass (p := p) (K := K) (G := G) //
      S.weightBlock w = b ∧ MulOpposite.op alpha • w = w} = 1 :=
  (Nat.card_congr (weightBlockRadicalFixedEquivBlock S Q b hjoint hblock alpha)).symm.trans hfixed

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierJointFibreSaturation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
