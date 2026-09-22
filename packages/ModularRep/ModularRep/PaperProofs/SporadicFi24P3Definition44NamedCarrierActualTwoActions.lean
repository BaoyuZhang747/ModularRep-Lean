import ModularRep.PaperProofs.CyclicOuterLemma37Concrete

/-! The same original inner/outer decomposition acts on both Brauer
characters and weight classes by either identity or one common involution.
The lift itself need not have order two. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualTwoActions

open ModularRep
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete

universe u

theorem square_inner_of_two_cosets
    {X : Type u} [Group X] (tau : MulAut X)
    (decomposition : ∀ a : MulAut X, ∃ x : X,
      a = MulAut.conj x ∨ a = MulAut.conj x * tau) :
    ∃ x : X, tau ^ 2 = MulAut.conj x := by
  obtain ⟨x, h | h⟩ := decomposition (tau * tau)
  · exact ⟨x, by simpa only [pow_two] using h⟩
  · have htau : tau = MulAut.conj x := mul_right_cancel h
    refine ⟨x * x, ?_⟩
    rw [pow_two, htau, map_mul]

variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Finite X]

private theorem ibr_op_conj_fixed
    (iota : PrimeRegularRootEmbedding p k K X) (x : X) (phi : IBr iota) :
    MulOpposite.op (MulAut.conj x) • phi = phi := by
  have h := inner_fixes_ibr iota (x⁻¹) phi
  change MulOpposite.op (MulAut.conj ((x⁻¹)⁻¹)) • phi = phi at h
  simpa only [inv_inv] using h

private theorem weight_op_conj_fixed (x : X)
    (w : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := X)) :
    MulOpposite.op (MulAut.conj x) • w = w := by
  have h := inner_fixes_weightClass (p := p) (K := K) (x⁻¹) w
  change MulOpposite.op (MulAut.conj ((x⁻¹)⁻¹)) • w = w at h
  simpa only [inv_inv] using h

theorem actual_two_actions
    (iota : PrimeRegularRootEmbedding p k K X) (tau : MulAut X)
    (decomposition : ∀ a : MulAut X, ∃ x : X,
      a = MulAut.conj x ∨ a = MulAut.conj x * tau)
    (a : (MulAut X)ᵐᵒᵖ) :
    ((∀ phi : IBr iota, a • phi = phi) ∧
      (∀ w : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := X), a • w = w)) ∨
    ((∀ phi : IBr iota, a • phi = MulOpposite.op tau • phi) ∧
      (∀ w : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := X),
        a • w = MulOpposite.op tau • w)) := by
  obtain ⟨x, h | h⟩ := decomposition a.unop
  · have ha : a = MulOpposite.op (MulAut.conj x) := MulOpposite.unop_injective h
    left
    constructor
    · intro phi
      rw [ha]
      exact ibr_op_conj_fixed iota x phi
    · intro w
      rw [ha]
      exact weight_op_conj_fixed x w
  · have ha : a = MulOpposite.op (MulAut.conj x * tau) := MulOpposite.unop_injective h
    right
    constructor
    · intro phi
      rw [ha, MulOpposite.op_mul, mul_smul, ibr_op_conj_fixed]
    · intro w
      rw [ha, MulOpposite.op_mul, mul_smul, weight_op_conj_fixed]

theorem brauer_tau_involutive
    (iota : PrimeRegularRootEmbedding p k K X) (tau : MulAut X)
    (decomposition : ∀ a : MulAut X, ∃ x : X,
      a = MulAut.conj x ∨ a = MulAut.conj x * tau) :
    Function.Involutive (fun phi : IBr iota => MulOpposite.op tau • phi) := by
  obtain ⟨x, hx⟩ := square_inner_of_two_cosets tau decomposition
  intro phi
  calc
    MulOpposite.op tau • (MulOpposite.op tau • phi) =
        MulOpposite.op (tau ^ 2) • phi := by rw [pow_two, MulOpposite.op_mul, mul_smul]
    _ = MulOpposite.op (MulAut.conj x) • phi := by rw [hx]
    _ = phi := ibr_op_conj_fixed iota x phi

theorem weight_tau_involutive
    (tau : MulAut X)
    (decomposition : ∀ a : MulAut X, ∃ x : X,
      a = MulAut.conj x ∨ a = MulAut.conj x * tau) :
    Function.Involutive (fun w : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := X) =>
      MulOpposite.op tau • w) := by
  obtain ⟨x, hx⟩ := square_inner_of_two_cosets tau decomposition
  intro w
  calc
    MulOpposite.op tau • (MulOpposite.op tau • w) =
        MulOpposite.op (tau ^ 2) • w := by rw [pow_two, MulOpposite.op_mul, mul_smul]
    _ = MulOpposite.op (MulAut.conj x) • w := by rw [hx]
    _ = w := weight_op_conj_fixed x w

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualTwoActions


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
