import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorWeightAssembly

/-! # Fixed original sector weights split over fixed radical classes -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorFixedUnion

open ModularRep ModularRep.CharacterWeight
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierTrivialSectorWeightRadical
open SporadicFi24P3Definition44NamedCarrierTrivialSectorWeightAssembly

def rotateThreeSubtypes {W : Type*} (P S T : W → Prop) :
    {w : {w : {w : W // P w} // S w.1} // T w.1.1} ≃
      {w : {w : {w : W // S w} // T w.1} // P w.1.1} where
  toFun w := ⟨⟨⟨w.1.1.1, w.1.2⟩, w.2⟩, w.1.1.2⟩
  invFun w := ⟨⟨⟨w.1.1.1, w.2⟩, w.1.1.2⟩, w.1.2⟩
  left_inv w := by rcases w with ⟨⟨⟨w, hp⟩, hs⟩, ht⟩; rfl
  right_inv w := by rcases w with ⟨⟨⟨w, hs⟩, ht⟩, hp⟩; rfl

universe u v
variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
local instance subgroupFintype (H : Subgroup X) : Fintype H := Fintype.ofFinite H

abbrev FixedIndex {I : Type v} (Q : I → RadicalSubgroup (p := p) (G := X)) (tau : MulAut X) :=
  {i : I // MulOpposite.op tau •
      (Quotient.mk'' (Q i) : RadicalConjugacyClass (p := p) (G := X)) = Quotient.mk'' (Q i)}

def sectorFixedRadicalUnionEquiv {I : Type v}
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
    (Z : Subgroup X) [Z.Normal] [Invertible (Fintype.card Z : k)]
    (Q : I → RadicalSubgroup (p := p) (G := X))
    (hQ : Function.Bijective (fun i => (Quotient.mk'' (Q i) : RadicalConjugacyClass (p := p) (G := X))))
    (tau : MulAut X) :
    (Σ i : FixedIndex Q tau,
      {w : SectorWeightRadicalFibre R Z (Q i.1) // MulOpposite.op tau • w.1.1 = w.1.1}) ≃
      {w : SectorWeights R Z // MulOpposite.op tau • w.1 = w.1} := by
  let W := WeightClass (p := p) (K := K) (X := X)
  let F := {w : SectorWeights R Z // MulOpposite.op tau • w.1 = w.1}
  let J := {c : RadicalConjugacyClass (p := p) (G := X) // MulOpposite.op tau • c = c}
  let projection : F → RadicalConjugacyClass (p := p) (G := X) := fun w => radicalClass w.1.1
  have projection_fixed (w : F) : MulOpposite.op tau • projection w = projection w := by
    change MulOpposite.op tau • radicalClass w.1.1 = radicalClass w.1.1
    rw [← radicalClass_equivariant (MulOpposite.op tau) w.1.1, w.2]
  let eIndex : FixedIndex Q tau ≃ J :=
    (Equiv.ofBijective (fun i => (Quotient.mk'' (Q i) : RadicalConjugacyClass (p := p) (G := X))) hQ).subtypeEquiv
      (fun _ => Iff.rfl)
  let E : (Σ i : FixedIndex Q tau,
      {w : SectorWeightRadicalFibre R Z (Q i.1) // MulOpposite.op tau • w.1.1 = w.1.1}) ≃
      (Σ c : J, {w : F // projection w = c.1}) :=
    Equiv.sigmaCongr eIndex (fun i => rotateThreeSubtypes
      (fun w : W => radicalClass w = (Quotient.mk'' (Q i.1) : RadicalConjugacyClass (p := p) (G := X)))
      (fun w : W => IsCentralCharacterSector Z (R.1.weightBlock w).1 (1 : Z →* kˣ))
      (fun w : W => MulOpposite.op tau • w = w))
  exact E.trans (Equiv.sigmaSubtypeFiberEquiv projection
    (fun c : RadicalConjugacyClass (p := p) (G := X) => MulOpposite.op tau • c = c) projection_fixed)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorFixedUnion


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
