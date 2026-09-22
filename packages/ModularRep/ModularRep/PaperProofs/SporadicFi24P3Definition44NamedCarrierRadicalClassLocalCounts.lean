import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeFixedPoints
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRadicalInnerCorrection

/-! Ordinary local total and fixed counts depend only on the actual radical class.
Inner corrections act trivially on ambient weight classes. -/

noncomputable section
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRadicalClassLocalCounts

open ModularRep ModularRep.CharacterWeight
open TypeBCentralKernelNormalizerInertia
open SporadicFi24P3Definition44NamedCarrierRepresentativeFixedPoints
open SporadicFi24P3Definition44NamedCarrierRadicalInnerCorrection

universe u
variable {p : ℕ} {K G : Type u}
variable [Field K] [CharZero K] [Group G] [Fintype G]

theorem local_card_eq_of_radicalClass_eq (hp : p.Prime)
    (Q U : RadicalSubgroup (p := p) (G := G))
    (hclass : (Quotient.mk'' Q : RadicalConjugacyClass (p := p) (G := G)) =
      Quotient.mk'' U) :
    Nat.card (LocalDefectZeroCharacter (K := K) Q) =
      Nat.card (LocalDefectZeroCharacter (K := K) U) := by
  calc
    Nat.card (LocalDefectZeroCharacter (K := K) Q) =
        Nat.card (WeightRadicalFibre (K := K) Q) :=
      Nat.card_congr (localDefectZeroEquivWeightRadicalFibre hp Q)
    _ = Nat.card (WeightRadicalFibre (K := K) U) := by
      unfold WeightRadicalFibre
      rw [hclass]
    _ = Nat.card (LocalDefectZeroCharacter (K := K) U) :=
      Nat.card_congr (localDefectZeroEquivWeightRadicalFibre hp U).symm

theorem fixed_fibre_card_eq_of_radicalClass_eq
    (Q U : RadicalSubgroup (p := p) (G := G)) (tau : MulAut G)
    (hclass : (Quotient.mk'' Q : RadicalConjugacyClass (p := p) (G := G)) =
      Quotient.mk'' U) :
    Nat.card {w : WeightRadicalFibre (K := K) Q // MulOpposite.op tau • w.1 = w.1} =
      Nat.card {w : WeightRadicalFibre (K := K) U // MulOpposite.op tau • w.1 = w.1} := by
  unfold WeightRadicalFibre
  rw [hclass]

def correctedLocalFixedEquiv (hp : p.Prime)
    (Q : RadicalSubgroup (p := p) (G := G)) (tau : MulAut G) (g : G)
    (stable : Q.1.comap (tau * MulAut.conj g).toMonoidHom = Q.1) :
    {theta : LocalDefectZeroCharacter (K := K) Q //
      OrdinaryIrreducibleCharacter.twist K _ theta.1
        (localAut Q.1 (tau * MulAut.conj g) stable) = theta.1} ≃
    {w : WeightRadicalFibre (K := K) Q // MulOpposite.op tau • w.1 = w.1} :=
  (localDefectZeroEquivWeightRadicalFibre hp Q).subtypeEquiv (fun theta => by
    change OrdinaryIrreducibleCharacter.twist K _ theta.1
        (localAut Q.1 (tau * MulAut.conj g) stable) = theta.1 ↔
      MulOpposite.op tau • (localDefectZeroEquivWeightRadicalFibre hp Q theta).1 =
        (localDefectZeroEquivWeightRadicalFibre hp Q theta).1
    simpa only [localDefectZeroEquivWeightRadicalFibre_apply_val, classAt,
      innerCorrection_weight_smul] using
      (classAt_fixed_iff_local_fixed hp Q (tau * MulAut.conj g) stable theta).symm)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRadicalClassLocalCounts


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
