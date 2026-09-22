import Mathlib.Algebra.Category.ModuleCat.Simple
import Mathlib.CategoryTheory.Action.Limits
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.QuotientGroup.Basic
import ModularRep.OrdinaryBlockFibre
import ModularRep.OrdinaryCharacterDefectZero

/-!
# Defect-zero ordinary inflation along a prime-to-p kernel

Surjective restriction preserves categorical simplicity and the underlying
finite-dimensional vector space. The prime-to-p kernel preserves the
p-part of the group order. No centrality or splitting-field hypothesis is
needed for this deduction.
-/

noncomputable section

open CategoryTheory Module

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToOrdinaryInflation

open ModularRep OrdinaryIrreducibleCharacter

universe u

private theorem res_simple_of_surjective
    {K A B : Type u} [Field K] [Group A] [Group B]
    (f : A →* B) (hf : Function.Surjective f)
    (V : FDRep K B) (hV : Simple V) :
    Simple ((Action.res (FGModuleCat K) f).obj V) := by
  let _ : Simple V := hV
  refine ⟨fun {Y} g hg => ?_⟩
  let _ : Mono g := hg
  let _ : Mono g.hom := by
    change Mono ((Action.forget (FGModuleCat K) A).map g)
    infer_instance
  have hkernel : f.ker ≤ (Action.ρ Y).ker := by
    intro a ha
    apply MonoidHom.mem_ker.mpr
    change Action.ρ Y a = 𝟙 Y.V
    apply (cancel_mono g.hom).mp
    rw [g.comm]
    change g.hom ≫ Action.ρ V (f a) = (𝟙 Y.V) ≫ g.hom
    rw [MonoidHom.mem_ker.mp ha, Action.ρ_one]
    exact (Category.comp_id g.hom).trans (Category.id_comp g.hom).symm
  let e : A ⧸ f.ker ≃* B := QuotientGroup.quotientKerEquivOfSurjective f hf
  let Ybar : FDRep K B :=
    { V := Y.V
      ρ := (QuotientGroup.lift f.ker (Action.ρ Y) hkernel).comp
        e.symm.toMonoidHom }
  have hYbar (a : A) : Action.ρ Ybar (f a) = Action.ρ Y a := by
    change QuotientGroup.lift f.ker (Action.ρ Y) hkernel
      (e.symm (f a)) = Action.ρ Y a
    have he : e.symm (f a) = QuotientGroup.mk' f.ker a := by
      apply e.injective
      rw [e.apply_symm_apply]
      exact (QuotientGroup.kerLift_mk f a).symm
    rw [he]
    exact QuotientGroup.lift_mk' f.ker hkernel a
  let gbar : Ybar ⟶ V :=
    { hom := g.hom
      comm := by
        intro b
        obtain ⟨a, rfl⟩ := hf b
        rw [hYbar]
        exact g.comm a }
  let _ : Mono gbar := by
    apply (Action.forget (FGModuleCat K) B).mono_of_mono_map
    change Mono g.hom
    infer_instance
  have hiso : IsIso g ↔ IsIso gbar := by
    constructor
    · intro h
      let _ : IsIso g := h
      let _ : IsIso gbar.hom := by
        change IsIso ((Action.forget (FGModuleCat K) A).map g)
        infer_instance
      infer_instance
    · intro h
      let _ : IsIso gbar := h
      let _ : IsIso g.hom := by
        change IsIso ((Action.forget (FGModuleCat K) B).map gbar)
        infer_instance
      infer_instance
  have hzero : gbar = 0 ↔ g = 0 := by
    constructor
    · intro h
      apply Action.hom_ext
      exact congrArg (fun t : Ybar ⟶ V => t.hom) h
    · intro h
      apply Action.hom_ext
      exact congrArg
        (fun t : Y ⟶ (Action.res (FGModuleCat K) f).obj V => t.hom) h
  rw [hiso, Simple.mono_isIso_iff_nonzero]
  exact not_congr hzero

theorem ordProj_card_eq_of_surjective
    {p : Nat} {A B : Type u}
    [Group A] [Finite A] [Group B] [Finite B]
    (f : A →* B) (hf : Function.Surjective f)
    (hkerCard : ¬ p ∣ Nat.card f.ker) :
    ordProj[p] (Nat.card A) = ordProj[p] (Nat.card B) := by
  have hcard : Nat.card A = Nat.card B * Nat.card f.ker := by
    calc
      Nat.card A = Nat.card (A ⧸ f.ker) * Nat.card f.ker :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
      _ = Nat.card B * Nat.card f.ker := by
        rw [Nat.card_congr
          (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]
  rw [hcard, Nat.ordProj_mul p Nat.card_pos.ne' Nat.card_pos.ne',
    show ordProj[p] (Nat.card f.ker) = 1 by
      simp only [Nat.factorization_eq_zero_of_not_dvd hkerCard, pow_zero],
    mul_one]

theorem inflateAlong_defectZero
    {p : Nat} {K A B : Type u} [Field K] [CharZero K]
    [Group A] [Finite A] [Group B] [Finite B]
    (f : A →* B) (hf : Function.Surjective f)
    (hkerCard : ¬ p ∣ Nat.card f.ker)
    (theta : Irr K B) (htheta : IsDefectZeroOrdinaryCharacter p theta) :
    IsDefectZeroOrdinaryCharacter p (inflateAlong f hf theta) := by
  rcases htheta with ⟨V, hVsimple, hVcharacter, hVzero⟩
  let W : FDRep K A := (Action.res (FGModuleCat K) f).obj V
  have hWsimple : Simple W := res_simple_of_surjective f hf V hVsimple
  have hWzero : IsDefectZeroRepresentation p W := by
    unfold IsDefectZeroRepresentation at hVzero ⊢
    change ordProj[p] (Module.finrank K V) = ordProj[p] (Nat.card A)
    exact hVzero.trans (ordProj_card_eq_of_surjective f hf hkerCard).symm
  refine ⟨W, hWsimple, ?_, hWzero⟩
  funext a
  change V.character (f a) = theta (f a)
  exact congrFun hVcharacter (f a)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToOrdinaryInflation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
