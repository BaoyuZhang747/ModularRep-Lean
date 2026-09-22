import ModularRep.IrreducibleBrauerCharacterSurjectiveDescent
import ModularRep.OrdinaryIrreducibleCharacterSurjectiveDescent

/-!
# Ordinary/Brauer reduction across a finite surjection

This thin neutral adapter combines the independently constructed ordinary
and Brauer descents.  A literal upstairs reduction relation and the exact
kernel-trivial Brauer witness are inputs.  The quotient Brauer character,
both manuscript-oriented pullback identities, and the quotient reduction
relation are outputs.

At a concrete manuscript binding, the literal reduction and root compatibility
on quotient-side representation roots are E1/U carrier data.  Equality of the
two total zero-extended lift functions is deliberately not assumed.  The
transport below is K and contains no block, weight, character correspondence,
BAW, or iBAW conclusion.
-/

noncomputable section

namespace ModularRep.OrdinaryBrauerReductionSurjectiveDescent

open ModularRep.IrreducibleBrauerCharacterSurjectiveDescent
open ModularRep.OrdinaryIrreducibleCharacterSurjectiveDescent

universe u

variable {p : Nat} {k K A B : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group A] [Finite A] [Group B] [Finite B] [Fact p.Prime]

/-- Literal equality of an ordinary character with a Brauer character on
the prime regular elements of the same group. -/
def IsOrdinaryBrauerReduction
    {G : Type u} [Group G] [Finite G]
    (iota : PrimeRegularRootEmbedding p k K G)
    (theta : OrdinaryIrreducibleCharacter.Irr K G)
    (phi : IBr iota) : Prop :=
  forall g : PrimeRegularElement (G := G) p, theta g.1 = phi.1 g

/-- Construct the quotient Brauer character and prove the two literal
pullback identities and the descended reduction relation.  Neither the
quotient character nor either factorisation identity is an input. -/
theorem exists_descendedOrdinaryBrauerPair
    (f : A →* B) (hf : Function.Surjective f)
    (hkerPrimeTo : (Nat.card f.ker).Coprime p)
    (iotaA : PrimeRegularRootEmbedding p k K A)
    (iotaB : PrimeRegularRootEmbedding p k K B)
    (hcompat : ∀ W : FDRep k B,
      Representation.BrauerRootLiftCompatibleAlong
        W.ρ iotaB iotaA f)
    (thetaA : OrdinaryIrreducibleCharacter.Irr K A)
    (hconstant : forall x : f.ker,
      thetaA (x : A) = thetaA (1 : A))
    (htheta : IsDefectZeroOrdinaryCharacter p thetaA)
    (phiA : KernelTrivialIBrAlong f iotaA)
    (hReduction : IsOrdinaryBrauerReduction iotaA thetaA phiA.1) :
    exists phiB : IBr iotaB,
      (thetaA.1 = fun a : A =>
        descendCharacter f hf thetaA hconstant (f a)) ∧
      IsDefectZeroOrdinaryCharacter p
        (descendCharacter f hf thetaA hconstant) ∧
      PrimeRegularClassFunction.pullback f phiB.1 = phiA.1.1 ∧
      IsOrdinaryBrauerReduction iotaB
        (descendCharacter f hf thetaA hconstant) phiB := by
  let phiB := descendIBrAlong f hf iotaA iotaB phiA
  have hordinary :=
    descendCharacter_factorisation f hf thetaA hconstant
  have hkerNotDvd : ¬ p ∣ Nat.card f.ker :=
    (Fact.out : p.Prime).coprime_iff_not_dvd.mp hkerPrimeTo.symm
  have hdefectZero :=
    descendCharacter_defectZero
      f hf hkerNotDvd thetaA hconstant htheta
  have hbrauer :=
    descendIBrAlong_pullback f hf iotaA iotaB hcompat phiA
  refine ⟨phiB, hordinary, hdefectZero, hbrauer, ?_⟩
  intro b
  obtain ⟨a, rfl⟩ :=
    primeRegularElement_map_surjective_of_ker_card_coprime
      f hf hkerPrimeTo b
  have hordinaryValue := congrFun hordinary a.1
  have hbrauerValue := congrArg
    (fun eta : PrimeRegularClassFunction K A p => eta a) hbrauer
  change phiB.1 (PrimeRegularElement.map f a) = phiA.1.1 a at hbrauerValue
  calc
    descendCharacter f hf thetaA hconstant (f a.1) = thetaA a.1 :=
      hordinaryValue.symm
    _ = phiA.1.1 a := hReduction a
    _ = phiB.1 (PrimeRegularElement.map f a) := hbrauerValue.symm

end ModularRep.OrdinaryBrauerReductionSurjectiveDescent


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
