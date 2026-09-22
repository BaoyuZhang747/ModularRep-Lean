import Mathlib.Algebra.Category.ModuleCat.Simple
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.GroupTheory.Coset.Card
import ModularRep.OrdinaryCharacterLiesOverKernel
import ModularRep.RepresentationSurjectiveDescent
import ModularRep.OrdinaryCharacterDefectZero

/-!
# Ordinary irreducible characters descended along a surjection

This neutral module descends a function-valued ordinary irreducible
character when its value is constant at the degree on the kernel.  Finite
averaging derives the necessary representation-kernel containments.  A
prime-to-`p` kernel preserves defect zero using the exact `FDRep` witness in
`IsDefectZeroOrdinaryCharacter`.

There is no character correspondence, block, weight, or manuscript source.
-/

noncomputable section

open CategoryTheory Module

namespace ModularRep.OrdinaryIrreducibleCharacterSurjectiveDescent

open ModularRep.RepresentationSurjectiveDescent

universe u

private theorem ordProj_card_eq_of_surjective_of_ker_card_not_dvd
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

private noncomputable def descendedFDRep
    {K A B : Type u} [Field K] [Group A] [Group B]
    (f : A →* B) (hf : Function.Surjective f)
    (V : FDRep K A) (hkernel : f.ker ≤ V.ρ.ker) :
    FDRep K B :=
  FDRep.of (descend f hf V.ρ hkernel)

private theorem res_preservesMonomorphisms
    {K A B : Type u} [Field K] [Group A] [Group B]
    (f : A →* B) :
    (Action.res (FGModuleCat K) f).PreservesMonomorphisms where
  preserves g _ := by
    apply (Action.forget (FGModuleCat K) A).mono_of_mono_map
    change Mono ((Action.forget (FGModuleCat K) B).map g)
    infer_instance

private theorem descendedFDRep_simple
    {K A B : Type u} [Field K] [Group A] [Group B]
    (f : A →* B) (hf : Function.Surjective f)
    (V : FDRep K A) (hVsimple : Simple V)
    (hkernel : f.ker ≤ V.ρ.ker) :
    Simple (descendedFDRep f hf V hkernel) := by
  let F := Action.res (FGModuleCat K) f
  let W : FDRep K B := descendedFDRep f hf V hkernel
  letI : F.Full := by
    dsimp only [F]
    exact Action.full_res (V := FGModuleCat K) f hf
  letI : F.PreservesMonomorphisms := by
    dsimp only [F]
    exact res_preservesMonomorphisms f
  letI : Simple V := hVsimple
  have hresIso : F.obj W ≅ V := by
    refine Action.mkIso
      (LinearEquiv.toFGModuleCatIso (LinearEquiv.refl K V)) (fun a ↦ ?_)
    ext v
    change descend f hf V.ρ hkernel (f a) v = V.ρ a v
    rw [descend_apply]
  letI : Simple (F.obj W) := Simple.of_iso hresIso
  change Simple W
  exact Functor.simple_of_simple_obj F W

private theorem descendedFDRep_defectZero
    {p : Nat} {K A B : Type u} [Field K]
    [Group A] [Finite A] [Group B] [Finite B]
    (f : A →* B) (hf : Function.Surjective f)
    (hkerCard : ¬ p ∣ Nat.card f.ker)
    (V : FDRep K A) (hkernel : f.ker ≤ V.ρ.ker)
    (hVzero : IsDefectZeroRepresentation p V) :
    IsDefectZeroRepresentation p (descendedFDRep f hf V hkernel) := by
  unfold IsDefectZeroRepresentation at hVzero ⊢
  change ordProj[p] (Module.finrank K V) = ordProj[p] (Nat.card B)
  exact hVzero.trans
    (ordProj_card_eq_of_surjective_of_ker_card_not_dvd
      f hf hkerCard)

private theorem kernel_le_of_character_eq_on_ker
    {K A B V : Type u} [Field K] [CharZero K]
    [Group A] [Finite A] [Group B]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : A →* B) (rho : Representation K A V)
    (theta : OrdinaryIrreducibleCharacter.Irr K A)
    (hcharacter : rho.character = theta.1)
    (hconstant : ∀ x : f.ker,
      theta (x : A) = theta (1 : A)) :
    f.ker ≤ rho.ker := by
  apply Representation.subgroup_le_ker_of_character_eq_one rho f.ker
  intro x
  rw [hcharacter]
  exact hconstant x

private noncomputable def chosenRealisation
    {K A : Type u} [Field K] [CharZero K] [Group A]
    (theta : OrdinaryIrreducibleCharacter.Irr K A) :
    OrdinaryIrreducibleCharacter.Realisation K A theta.1 :=
  Classical.choice theta.property

private theorem chosenRealisation_kernel_le
    {K A B : Type u} [Field K] [CharZero K]
    [Group A] [Finite A] [Group B]
    (f : A →* B)
    (theta : OrdinaryIrreducibleCharacter.Irr K A)
    (hconstant : ∀ x : f.ker,
      theta (x : A) = theta (1 : A)) :
    f.ker ≤ (chosenRealisation theta).representation.ker :=
  kernel_le_of_character_eq_on_ker
    f (chosenRealisation theta).representation theta
      (chosenRealisation theta).character_eq hconstant

private noncomputable def descendedRealisation
    {K A B : Type u} [Field K] [CharZero K]
    [Group A] [Group B]
    (f : A →* B) (hf : Function.Surjective f)
    (theta : OrdinaryIrreducibleCharacter.Irr K A)
    (R : OrdinaryIrreducibleCharacter.Realisation K A theta.1)
    (hkernel : f.ker ≤ R.representation.ker) :
    OrdinaryIrreducibleCharacter.Realisation K B
      (descend f hf R.representation hkernel).character where
  dimension := R.dimension
  representation := descend f hf R.representation hkernel
  irreducible := descend_irreducible
    f hf R.representation hkernel R.irreducible
  character_eq := rfl

/-- Descend an ordinary irreducible character along a surjection.  The
affording realisation is selected internally, and finite averaging derives
its kernel containment from the stated character values. -/
noncomputable def descendCharacter
    {K A B : Type u} [Field K] [CharZero K]
    [Group A] [Finite A] [Group B]
    (f : A →* B) (hf : Function.Surjective f)
    (theta : OrdinaryIrreducibleCharacter.Irr K A)
    (hconstant : ∀ x : f.ker,
      theta (x : A) = theta (1 : A)) :
    OrdinaryIrreducibleCharacter.Irr K B :=
  ⟨(descend f hf (chosenRealisation theta).representation
      (chosenRealisation_kernel_le f theta hconstant)).character,
    ⟨descendedRealisation f hf theta (chosenRealisation theta)
      (chosenRealisation_kernel_le f theta hconstant)⟩⟩

@[simp]
private theorem descendCharacter_apply
    {K A B : Type u} [Field K] [CharZero K]
    [Group A] [Finite A] [Group B]
    (f : A →* B) (hf : Function.Surjective f)
    (theta : OrdinaryIrreducibleCharacter.Irr K A)
    (hconstant : ∀ x : f.ker,
      theta (x : A) = theta (1 : A)) (a : A) :
    descendCharacter f hf theta hconstant (f a) = theta a := by
  change
    (descend f hf (chosenRealisation theta).representation
      (chosenRealisation_kernel_le f theta hconstant)).character (f a) =
        theta a
  unfold Representation.character
  rw [descend_apply]
  exact congrFun (chosenRealisation theta).character_eq a

/-- Exact function-level factorisation in the manuscript orientation. -/
theorem descendCharacter_factorisation
    {K A B : Type u} [Field K] [CharZero K]
    [Group A] [Finite A] [Group B]
    (f : A →* B) (hf : Function.Surjective f)
    (theta : OrdinaryIrreducibleCharacter.Irr K A)
    (hconstant : ∀ x : f.ker,
      theta (x : A) = theta (1 : A)) :
    theta.1 = fun a ↦ descendCharacter f hf theta hconstant (f a) := by
  funext a
  exact (descendCharacter_apply f hf theta hconstant a).symm

/-- Surjectivity makes the descended ordinary character unique. -/
theorem descendCharacter_unique
    {K A B : Type u} [Field K] [CharZero K]
    [Group A] [Finite A] [Group B]
    (f : A →* B) (hf : Function.Surjective f)
    (theta : OrdinaryIrreducibleCharacter.Irr K A)
    (hconstant : ∀ x : f.ker,
      theta (x : A) = theta (1 : A))
    (psi : OrdinaryIrreducibleCharacter.Irr K B)
    (hpsi : theta.1 = fun a ↦ psi (f a)) :
    psi = descendCharacter f hf theta hconstant := by
  apply OrdinaryIrreducibleCharacter.ext
  intro b
  obtain ⟨a, rfl⟩ := hf b
  exact (congrFun hpsi a).symm.trans
    (descendCharacter_apply f hf theta hconstant a).symm

/-- Defect zero descends across a finite surjection with prime-to-`p`
kernel.  The proof repeats finite averaging on the exact `FDRep` witness
selected from `htheta`; it does not transfer a kernel fact from the
internally chosen `Realisation`. -/
theorem descendCharacter_defectZero
    {p : Nat} {K A B : Type u} [Field K] [CharZero K]
    [Group A] [Finite A] [Group B] [Finite B]
    (f : A →* B) (hf : Function.Surjective f)
    (hkerCard : ¬ p ∣ Nat.card f.ker)
    (theta : OrdinaryIrreducibleCharacter.Irr K A)
    (hconstant : ∀ x : f.ker,
      theta (x : A) = theta (1 : A))
    (htheta : ModularRep.IsDefectZeroOrdinaryCharacter p theta) :
    ModularRep.IsDefectZeroOrdinaryCharacter p
      (descendCharacter f hf theta hconstant) := by
  rcases htheta with ⟨V, hVsimple, hVcharacter, hVzero⟩
  let hVkernel : f.ker ≤ V.ρ.ker :=
    kernel_le_of_character_eq_on_ker
      f V.ρ theta hVcharacter hconstant
  let W : FDRep K B := descendedFDRep f hf V hVkernel
  have hWsimple : Simple W :=
    descendedFDRep_simple f hf V hVsimple hVkernel
  have hWzero : IsDefectZeroRepresentation p W :=
    descendedFDRep_defectZero f hf hkerCard V hVkernel hVzero
  refine ⟨W, hWsimple, ?_, hWzero⟩
  apply funext
  intro b
  obtain ⟨a, rfl⟩ := hf b
  calc
    W.character (f a) = V.character a := by
      change
        (descend f hf V.ρ hVkernel).character (f a) =
          Representation.character V.ρ a
      unfold Representation.character
      rw [descend_apply]
    _ = theta a := congrFun hVcharacter a
    _ = descendCharacter f hf theta hconstant (f a) :=
      (descendCharacter_apply f hf theta hconstant a).symm

end ModularRep.OrdinaryIrreducibleCharacterSurjectiveDescent


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
