import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierNumericalOrbitAssembly
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualTwoActions
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllPairs

/-! Actual primitive-block totals and fixed-point totals construct a fully
automorphism-equivariant correspondence. The only numerical inputs are
cardinal equalities of the literal character and weight fibres. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualNumericalEquiv

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllPairs
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierNumericalOrbitAssembly
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualTwoActions
open ModularRep.PaperProofs.OddConlonOrbitAssembly

universe u

variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
variable [Finite (WeightClass (p := p) (K := K) (X := X))]

structure ActualBlockC2Counts
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
    (tau : MulAut X) : Prop where
  total : ∀ b : ActualBlock (k := k) (X := X),
    Nat.card {phi : IBr iota // operationsBlock iota hinj R phi = b} =
      Nat.card {w : WeightClass (p := p) (K := K) (X := X) // R.1.weightBlock w = b}
  fixed : ∀ b : ActualBlock (k := k) (X := X), MulOpposite.op tau • b = b →
    Nat.card {phi : IBr iota // operationsBlock iota hinj R phi = b ∧
      MulOpposite.op tau • phi = phi} =
    Nat.card {w : WeightClass (p := p) (K := K) (X := X) // R.1.weightBlock w = b ∧
      MulOpposite.op tau • w = w}

theorem exists_actual_equivariant_of_counts
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
    (tau : MulAut X)
    (decomposition : ∀ a : MulAut X, ∃ x : X,
      a = MulAut.conj x ∨ a = MulAut.conj x * tau)
    (counts : ActualBlockC2Counts iota hinj R tau) :
    ∃ Omega : IBr iota ≃ WeightClass (p := p) (K := K) (X := X),
      (∀ (a : (MulAut X)ᵐᵒᵖ) (phi : IBr iota), Omega (a • phi) = a • Omega phi) ∧
      (∀ phi, R.1.weightBlock (Omega phi) = operationsBlock iota hinj R phi) := by
  have hX := operationsBrauerSupport (iota := iota) (hinj := hinj) R
  have hY := R.1.weightBlock_transport
  let H := representativeEquivExists
    (operationsBlock iota hinj R) R.1.weightBlock hX hY
    (fun _ => inferInstance) (fun _ => inferInstance)
    (MulOpposite.op tau) (brauer_tau_involutive iota tau decomposition)
    (weight_tau_involutive (p := p) (K := K) tau decomposition)
    (actual_two_actions iota tau decomposition) counts.total counts.fixed
  let F := RepresentativeEquivFamily.ofExists
    (operationsBlock iota hinj R) R.1.weightBlock hX H
  let Omega := RepresentativeEquivFamily.globalEquiv
    (operationsBlock iota hinj R) R.1.weightBlock hX hY F
  exact ⟨Omega,
    RepresentativeEquivFamily.globalEquiv_equivariant
      (operationsBlock iota hinj R) R.1.weightBlock hX hY F,
    RepresentativeEquivFamily.globalEquiv_block_preserving
      (operationsBlock iota hinj R) R.1.weightBlock hX hY F⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualNumericalEquiv


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
