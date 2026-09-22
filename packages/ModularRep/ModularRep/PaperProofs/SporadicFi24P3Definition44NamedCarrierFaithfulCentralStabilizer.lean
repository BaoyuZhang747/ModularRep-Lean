import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBrauerKernel
import ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily

/-! A centrally faithful irreducible Brauer character can be fixed only
by an automorphism fixing the full centre pointwise. This follows from
actual representation isomorphism, without choosing new root lifts. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulCentralStabilizer

open CategoryTheory ModularRep ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily

universe u v

theorem fixes_center_of_faithful_brauer_fixed
    {p : ℕ} {k X : Type u} {K : Type v}
    [Field k] [Field K] [Group X] [Finite X]
    [CharP k p] [IsAlgClosed k] [CharZero K]
    (iota : PrimeRegularRootEmbedding p k K X)
    (V : FDRep k X) (hV : Representation.IsIrreducible V.ρ)
    (hfaithful : Subgroup.center X ⊓ V.ρ.ker = ⊥)
    (alpha : MulAut X)
    (hfixed : (Representation.brauerCharacterOfRootEmbedding V.ρ iota).twist alpha =
      Representation.brauerCharacterOfRootEmbedding V.ρ iota) :
    ∀ z : Subgroup.center X, alpha (z : X) = z := by
  let := hV
  let W := FDRep.of (Representation.twist V.ρ alpha)
  have hW : Representation.IsIrreducible W.ρ := hV.twist alpha
  have hchar : Representation.brauerCharacterOfRootEmbedding V.ρ iota =
      Representation.brauerCharacterOfRootEmbedding W.ρ iota := by
    simpa only [W, FDRep.of_ρ', Representation.brauerCharacterOfRootEmbedding_twist]
      using hfixed.symm
  obtain ⟨e⟩ := irreducibleModularTraceDeterminesRepresentation V W hV hW
    (brauerCharacterDeterminesModularTrace_of_rootEmbedding iota V W hchar)
  intro z
  have hrho : V.ρ (alpha (z : X)) = V.ρ (z : X) := by
    change W.ρ (z : X) = V.ρ (z : X)
    rw [FDRep.Iso.conj_ρ e z,
      Representation.centralCharacter_spec V.ρ (Subgroup.center X) le_rfl z]
    ext v
    simp [LinearEquiv.conj_apply]
  have hzalpha : alpha (z : X) ∈ Subgroup.center X :=
    (Subgroup.centerCongr alpha z).property
  have hkernel : (z : X)⁻¹ * alpha (z : X) ∈ Subgroup.center X ⊓ V.ρ.ker :=
    ⟨(Subgroup.center X).mul_mem ((Subgroup.center X).inv_mem z.property) hzalpha,
      (MonoidHom.eq_iff V.ρ).mp hrho⟩
  rw [hfaithful] at hkernel
  exact (inv_mul_eq_one.mp (Subgroup.mem_bot.mp hkernel)).symm

theorem inner_of_center_fixed_of_outer_decomposition
    {X : Type u} [Group X]
    (tau : MulAut X)
    (decomposition : ∀ a : MulAut X, ∃ x : X,
      a = MulAut.conj x ∨ a = MulAut.conj x * tau)
    (movesCenter : ∃ z : Subgroup.center X, tau (z : X) ≠ z)
    (alpha : MulAut X) (hfixed : ∀ z : Subgroup.center X, alpha (z : X) = z) :
    ∃ x : X, alpha = MulAut.conj x := by
  obtain ⟨x, hx | hx⟩ := decomposition alpha
  · exact ⟨x, hx⟩
  · obtain ⟨z, hz⟩ := movesCenter
    have h := hfixed z
    rw [hx] at h
    have hcentral : tau (z : X) ∈ Subgroup.center X :=
      (Subgroup.centerCongr tau z).property
    have hc : MulAut.conj x (tau (z : X)) = tau (z : X) := by
      change x * tau (z : X) * x⁻¹ = tau (z : X)
      rw [Subgroup.mem_center_iff.mp hcentral x, mul_inv_cancel_right]
    exact (hz (hc.symm.trans h)).elim

theorem stabilizerInner_of_faithful_center
    (P : Definition35Problem.{u}) (psi : Definition35Brauer P)
    (hfaithful : centralCharacterKernel P psi = ⊥)
    (tau : MulAut P.H)
    (decomposition : ∀ a : MulAut P.H, ∃ x : P.H,
      a = MulAut.conj x ∨ a = MulAut.conj x * tau)
    (movesCenter : ∃ z : Subgroup.center P.H, tau (z : P.H) ≠ z) :
    ∀ a : MulAction.stabilizer (MulAut P.H)ᵐᵒᵖ psi.1,
      ∃ x : P.H, a.1.unop = MulAut.conj x := by
  intro a
  have hfixed : psi.1.1.twist a.1.unop = psi.1.1 := by
    exact congrArg Subtype.val a.2
  rw [chosenBrauerRepresentation_character P psi] at hfixed
  apply inner_of_center_fixed_of_outer_decomposition tau decomposition movesCenter
  exact fixes_center_of_faithful_brauer_fixed P.iota (chosenBrauerRepresentation P psi)
    (chosenBrauerRepresentation_irreducible P psi) hfaithful a.1.unop hfixed

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulCentralStabilizer


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
