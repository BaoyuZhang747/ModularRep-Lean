import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToOrdinaryInflation
import ModularRep.OrdinaryIrreducibleCharacterSurjectiveDescent

/-!
# Actual defect-zero character inflation and descent

The upstream carrier consists precisely of defect-zero ordinary characters
constant at their degree on the literal kernel. The inverse is inflation.
Both inverse laws retain the character's values along the same map.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToOrdinaryEquiv

open ModularRep OrdinaryIrreducibleCharacter
open ModularRep.OrdinaryIrreducibleCharacterSurjectiveDescent
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToOrdinaryInflation

universe u

abbrev DefectZeroIrr
    (p : Nat) (K G : Type u)
    [Field K] [CharZero K] [Group G] [Finite G] :=
  {theta : Irr K G // IsDefectZeroOrdinaryCharacter p theta}

variable {p : Nat} {K A B : Type u}
variable [Field K] [CharZero K]
variable [Group A] [Finite A] [Group B] [Finite B]

abbrev KernelConstantDefectZeroIrr (f : A →* B) :=
  {theta : DefectZeroIrr p K A //
    ∀ x : f.ker, theta.1 (x : A) = theta.1 (1 : A)}

omit [Finite A] [Finite B] in
private theorem inflated_kernel_constant
    (f : A →* B) (hf : Function.Surjective f) (psi : Irr K B) :
    ∀ x : f.ker,
      inflateAlong f hf psi (x : A) = inflateAlong f hf psi (1 : A) := by
  intro x
  change psi (f (x : A)) = psi (f 1)
  rw [MonoidHom.mem_ker.mp x.property, map_one]

def defectZeroInflationDescentEquiv
    (f : A →* B) (hf : Function.Surjective f)
    (hkerCard : ¬ p ∣ Nat.card f.ker) :
    KernelConstantDefectZeroIrr (p := p) (K := K) f ≃ DefectZeroIrr p K B where
  toFun theta :=
    ⟨descendCharacter f hf theta.1.1 theta.2,
      descendCharacter_defectZero f hf hkerCard theta.1.1 theta.2 theta.1.2⟩
  invFun psi :=
    ⟨⟨inflateAlong f hf psi.1,
        inflateAlong_defectZero f hf hkerCard psi.1 psi.2⟩,
      inflated_kernel_constant f hf psi.1⟩
  left_inv theta := by
    apply Subtype.ext
    apply Subtype.ext
    apply OrdinaryIrreducibleCharacter.ext
    intro a
    exact (congrFun
      (descendCharacter_factorisation f hf theta.1.1 theta.2) a).symm
  right_inv psi := by
    apply Subtype.ext
    exact (descendCharacter_unique f hf
      (inflateAlong f hf psi.1)
      (inflated_kernel_constant f hf psi.1) psi.1 rfl).symm

theorem defectZeroInflationDescentEquiv_apply
    (f : A →* B) (hf : Function.Surjective f)
    (hkerCard : ¬ p ∣ Nat.card f.ker)
    (theta : KernelConstantDefectZeroIrr (p := p) (K := K) f) (a : A) :
    (defectZeroInflationDescentEquiv f hf hkerCard theta).1 (f a) = theta.1.1 a :=
  (congrFun (descendCharacter_factorisation f hf theta.1.1 theta.2) a).symm

@[simp]
theorem defectZeroInflationDescentEquiv_symm_apply
    (f : A →* B) (hf : Function.Surjective f)
    (hkerCard : ¬ p ∣ Nat.card f.ker)
    (psi : DefectZeroIrr p K B) (a : A) :
    ((defectZeroInflationDescentEquiv f hf hkerCard).symm psi).1.1 a =
      psi.1 (f a) := rfl

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToOrdinaryEquiv


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
