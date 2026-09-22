import ModularRep.IBrSimpleModuleClass
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualNumericalEquiv
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorFibreCancellation

/-! Cancel the already understood block fibres from an unblocked global
correspondence. The remaining block counts and block preservation are
deductions; the original global map need not preserve any block. -/

noncomputable section
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualComplementCancellation

open ModularRep ModularRep.FDRepSimpleClassKZero
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierAllPairs
open SporadicFi24P3Definition44NamedCarrierActualNumericalEquiv
open SporadicFi24P3Definition44NamedCarrierFiniteFibres
open SporadicFi24P3Definition44NamedCarrierTrivialSectorFibreCancellation

universe u
variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G]
variable (iota : PrimeRegularRootEmbedding p k K G)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := G))
variable (tau : MulAut G)
variable (E : IBr iota ≃ WeightClass (p := p) (K := K) (X := G))
variable (hE : ∀ phi, E (MulOpposite.op tau • phi) = MulOpposite.op tau • E phi)
variable (b0 : ActualBlock (k := k) (X := G))
variable (hother : ∀ b, b ≠ b0 →
  Nat.card {phi : IBr iota // operationsBlock iota hinj R phi = b} =
    Nat.card {w : WeightClass (p := p) (K := K) (X := G) // R.1.weightBlock w = b})
variable (hotherFixed : ∀ b, b ≠ b0 →
  Nat.card {phi : IBr iota // operationsBlock iota hinj R phi = b ∧
    MulOpposite.op tau • phi = phi} =
    Nat.card {w : WeightClass (p := p) (K := K) (X := G) //
      R.1.weightBlock w = b ∧ MulOpposite.op tau • w = w})

include hE hother hotherFixed

theorem actual_counts_of_complement : ActualBlockC2Counts iota hinj R tau := by
  let _ : Fintype (ActualBlock (k := k) (X := G)) :=
    R.1.operations.ambientBlockData.fintypeBlock
  let _ : Finite (WeightClass (p := p) (K := K) (X := G)) :=
    Finite.of_equiv (IBr iota) E
  let Efix : {phi : IBr iota // MulOpposite.op tau • phi = phi} ≃
      {w : WeightClass (p := p) (K := K) (X := G) // MulOpposite.op tau • w = w} :=
    E.subtypeEquiv (fun phi => by
      constructor
      · intro h
        rw [← hE phi, h]
      · intro h
        apply E.injective
        exact (hE phi).trans h)
  have hprincipal := card_fibre_eq_of_other_fibres
    (operationsBlock iota hinj R) R.1.weightBlock b0 (Nat.card_congr E) hother
  have hprincipalFixed := supportedFixed_fibre_card_eq
    (operationsBlock iota hinj R) R.1.weightBlock (fun _ => True)
    (fun phi => MulOpposite.op tau • phi = phi)
    (fun w => MulOpposite.op tau • w = w) b0 trivial
    (by simpa only [true_and] using Nat.card_congr Efix)
    (fun b _ hne => hotherFixed b hne)
  constructor
  · intro b
    by_cases hb : b = b0
    · subst b
      exact hprincipal
    · exact hother b hb
  · intro b _
    by_cases hb : b = b0
    · subst b
      exact hprincipalFixed
    · exact hotherFixed b hb

theorem exists_actual_equivariant_of_complement
    (decomposition : ∀ a : MulAut G, ∃ x : G,
      a = MulAut.conj x ∨ a = MulAut.conj x * tau) :
    ∃ Omega : IBr iota ≃ WeightClass (p := p) (K := K) (X := G),
      (∀ (a : (MulAut G)ᵐᵒᵖ) (phi : IBr iota), Omega (a • phi) = a • Omega phi) ∧
      (∀ phi, R.1.weightBlock (Omega phi) = operationsBlock iota hinj R phi) := by
  let _ : Finite (WeightClass (p := p) (K := K) (X := G)) :=
    Finite.of_equiv (IBr iota) E
  exact exists_actual_equivariant_of_counts iota hinj R tau decomposition
    (actual_counts_of_complement iota hinj R tau E hE b0 hother hotherFixed)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualComplementCancellation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
