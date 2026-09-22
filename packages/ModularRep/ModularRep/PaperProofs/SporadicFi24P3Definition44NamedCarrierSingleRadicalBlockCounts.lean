import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeFixedPoints
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRadicalInnerCorrection
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOrdinaryRowAllocation

/-! One supported radical class and actual local ordinary rows determine
the whole block's weight signature. The interval scalar test supplies
block membership, and the corrected local action supplies fixed points. -/

noncomputable section
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSingleRadicalBlockCounts

open ModularRep ModularRep.CharacterWeight
open SporadicFi24P3Definition44NamedCarrierRepresentativeFixedPoints
open SporadicFi24P3Definition44NamedCarrierRadicalInnerCorrection
open SporadicFi24P3Definition44NamedCarrierOrdinaryRowAllocation
open TypeBCentralKernelNormalizerInertia (localAut)

universe u
variable {p : ℕ} {k K G Block : Type u}
variable [Field k] [Field K] [CharZero K] [Group G] [Fintype G]
variable [MulAction (MulAut G)ᵐᵒᵖ Block]
variable (S : LocalBlockInductionSource (p := p) (k := k) (K := K) (G := G) (Block := Block))
variable (Q : RadicalSubgroup (p := p) (G := G)) (b : Block)
variable (support : ∀ w : ConjugacyClass (p := p) (K := K) (G := G),
  S.weightBlock w = b → radicalClass w =
    (Quotient.mk'' Q : RadicalConjugacyClass (p := p) (G := G)))

def representativeBlockEquiv (hp : p.Prime) :
    RepresentativeDZ hp S Q b ≃
      {w : ConjugacyClass (p := p) (K := K) (G := G) // S.weightBlock w = b} :=
  (representativeDZEquivWeightBlockRadicalFibre hp S Q b).trans {
    toFun := fun w => ⟨w.1, w.2.1⟩
    invFun := fun w => ⟨w.1, w.2, support w.1 w.2⟩
    left_inv := fun _ => Subtype.ext rfl
    right_inv := fun _ => Subtype.ext rfl }

def fixedRepresentativeBlockEquiv (hp : p.Prime)
    (tau : MulAut G) (g : G)
    (stable : Q.1.comap (tau * MulAut.conj g).toMonoidHom = Q.1) :
    {theta : RepresentativeDZ hp S Q b //
      OrdinaryIrreducibleCharacter.twist K _ theta.1.1
        (localAut Q.1 (tau * MulAut.conj g) stable) = theta.1.1} ≃
    {w : ConjugacyClass (p := p) (K := K) (G := G) //
      S.weightBlock w = b ∧ MulOpposite.op tau • w = w} :=
  (fixedRepresentativeDZEquiv hp S Q b (tau * MulAut.conj g) stable).trans {
    toFun := fun w => ⟨w.1.1, w.1.2.1,
      (innerCorrection_weight_smul tau g w.1.1).symm.trans w.2⟩
    invFun := fun w => ⟨⟨w.1, w.2.1, support w.1 w.2.1⟩,
      (innerCorrection_weight_smul tau g w.1).trans w.2.2⟩
    left_inv := fun _ => Subtype.ext (Subtype.ext rfl)
    right_inv := fun _ => Subtype.ext rfl }

variable [CharP k p] [Fact p.Prime]

include support

theorem weight_signature_of_four_local_rows
    (iota : PrimeRegularRootEmbedding p k K G)
    (rows : Fin 4 → LocalDefectZeroCharacter (K := K) Q)
    (rowBijective : Function.Bijective rows)
    (S414 : NormalizerIntervalSource S.operations Q)
    (evaluation : ∀ r : Fin 4,
      intervalEvaluation S.operations Q
        (S.operations.inflateToNormalizer Q.1
          (S.operations.localCharacterBlock Q.1 (rows r).1 (rows r).2)) b = 1)
    (tau : MulAut G) (g : G)
    (stable : Q.1.comap (tau * MulAut.conj g).toMonoidHom = Q.1)
    (localFixed : Nat.card {theta : LocalDefectZeroCharacter (K := K) Q //
      OrdinaryIrreducibleCharacter.twist K _ theta.1
        (localAut Q.1 (tau * MulAut.conj g) stable) = theta.1} = 2) :
    Nat.card {w : ConjugacyClass (p := p) (K := K) (G := G) // S.weightBlock w = b} = 4 ∧
    Nat.card {w : ConjugacyClass (p := p) (K := K) (G := G) //
      S.weightBlock w = b ∧ MulOpposite.op tau • w = w} = 2 := by
  have allocation (theta : LocalDefectZeroCharacter (K := K) Q) :
      S.operations.rawWeightBlock (characterWeightAt iota.prime Q theta) = b := by
    obtain ⟨r, rfl⟩ := rowBijective.2 theta
    exact (rawWeightBlock_eq_iff_intervalEvaluation iota S.operations Q (rows r) b S414).mpr
      (evaluation r)
  let E : LocalDefectZeroCharacter (K := K) Q ≃ RepresentativeDZ iota.prime S Q b := {
    toFun := fun theta => ⟨theta, allocation theta⟩
    invFun := fun theta => theta.1
    left_inv := fun _ => rfl
    right_inv := fun _ => Subtype.ext rfl }
  have hlocal : Nat.card (LocalDefectZeroCharacter (K := K) Q) = 4 := by
    simpa only [Nat.card_fin] using (Nat.card_congr (Equiv.ofBijective rows rowBijective)).symm
  have total := Nat.card_congr (E.trans (representativeBlockEquiv S Q b support iota.prime))
  let fixedE : {theta : LocalDefectZeroCharacter (K := K) Q //
      OrdinaryIrreducibleCharacter.twist K _ theta.1
        (localAut Q.1 (tau * MulAut.conj g) stable) = theta.1} ≃
      {theta : RepresentativeDZ iota.prime S Q b //
        OrdinaryIrreducibleCharacter.twist K _ theta.1.1
          (localAut Q.1 (tau * MulAut.conj g) stable) = theta.1.1} :=
    E.subtypeEquiv (fun _ => Iff.rfl)
  have fixed := Nat.card_congr
    (fixedE.trans (fixedRepresentativeBlockEquiv S Q b support iota.prime tau g stable))
  exact ⟨total.symm.trans hlocal, fixed.symm.trans localFixed⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSingleRadicalBlockCounts


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
