import ModularRep.CharacterWeightRadicalProjection
import ModularRep.CharacterWeightBlockAssignment
import ModularRep.PaperProofs.CyclicOuterLemma37Concrete

/-! # Correcting an outer representative to stabilize the actual radical -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRadicalInnerCorrection

open ModularRep ModularRep.CharacterWeight
open CyclicOuterLemma37Concrete

universe u

theorem exists_innerCorrection_of_fixed_radicalClass
    {p : ℕ} {X : Type u} [Group X]
    (Q : RadicalSubgroup (p := p) (G := X)) (tau : MulAut X)
    (hfixed : MulOpposite.op tau •
        (Quotient.mk'' Q : RadicalConjugacyClass (p := p) (G := X)) = Quotient.mk'' Q) :
    ∃ g : X, Q.1.comap (tau * MulAut.conj g).toMonoidHom = Q.1 := by
  change (Quotient.mk'' (Q.rightTwist tau) :
    RadicalConjugacyClass (p := p) (G := X)) = Quotient.mk'' Q at hfixed
  obtain ⟨g, hg⟩ := Quotient.exact hfixed
  refine ⟨g, ?_⟩
  have hback : (Q.rightTwist tau).rightTwist (MulAut.conj g) = Q := by
    rw [← hg]
    change (Q.rightTwist (MulAut.conj g⁻¹)).rightTwist (MulAut.conj g) = Q
    rw [RadicalSubgroup.rightTwist_mul]
    simp only [map_inv, inv_mul_cancel, RadicalSubgroup.rightTwist_one]
  exact congrArg Subtype.val ((Q.rightTwist_mul tau (MulAut.conj g)).symm.trans hback)

theorem radical_op_conj_fixed {p : ℕ} {X : Type u} [Group X]
    (g : X) (c : RadicalConjugacyClass (p := p) (G := X)) :
    MulOpposite.op (MulAut.conj g) • c = c := by
  refine Quotient.inductionOn c ?_
  intro Q
  apply Quotient.sound
  refine ⟨g⁻¹, ?_⟩
  change Q.rightTwist (MulAut.conj ((g⁻¹)⁻¹)) = Q.rightTwist (MulAut.conj g)
  rw [inv_inv]

theorem innerCorrection_radical_smul {p : ℕ} {X : Type u} [Group X]
    (tau : MulAut X) (g : X) (c : RadicalConjugacyClass (p := p) (G := X)) :
    MulOpposite.op (tau * MulAut.conj g) • c = MulOpposite.op tau • c := by
  rw [MulOpposite.op_mul, mul_smul, radical_op_conj_fixed]

theorem innerCorrection_weight_smul {p : ℕ} {K X : Type u}
    [Field K] [CharZero K] [Group X] [Finite X]
    (tau : MulAut X) (g : X) (w : ConjugacyClass (p := p) (K := K) (G := X)) :
    MulOpposite.op (tau * MulAut.conj g) • w = MulOpposite.op tau • w := by
  rw [MulOpposite.op_mul, mul_smul]
  have h := inner_fixes_weightClass (p := p) (K := K) (g⁻¹) (MulOpposite.op tau • w)
  change MulOpposite.op (MulAut.conj ((g⁻¹)⁻¹)) • (MulOpposite.op tau • w) =
    MulOpposite.op tau • w at h
  simpa only [inv_inv] using h

theorem innerCorrection_block_smul {p : ℕ} {k K X Block : Type u}
    [Field k] [Field K] [CharZero K] [Group X] [Fintype X]
    [MulAction (MulAut X)ᵐᵒᵖ Block]
    (S : LocalBlockInductionSource
      (p := p) (k := k) (K := K) (G := X) (Block := Block))
    (tau : MulAut X) (g : X) (b : Block) :
    MulOpposite.op (tau * MulAut.conj g) • b = MulOpposite.op tau • b := by
  rw [MulOpposite.op_mul, mul_smul]
  simpa only [inv_inv] using S.inner_blocks_fixed (g⁻¹) (MulOpposite.op tau • b)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRadicalInnerCorrection


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
