import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalTripleCoverNumerical
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOtherPrimeNumericalJoins
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedDefinition41Certificate

/-! Numerical arguments for the remaining primes, producing raw extension and block data. Compatible roots are an additional requirement for the full inductive condition. -/
noncomputable section
set_option maxHeartbeats 4000000
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedOtherPrimeApplications
open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.NavarroBrauerRestrictionCovering ModularRep.NavarroCoveringBrauerExtension
open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
  (DefectZeroReductionSource TrivialWeightSource GlobalDefectZeroCharacter)
open ModularRep.PaperProofs.SporadicFi24QOneNormalisationActual
  (DefectZeroOrdinaryBlockSource)
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllPairs
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalDefinition41
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalIdentityFamily
  (QuotientDataFamily)
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalPrimeCenterFamily
  (TrivialAmbientDataFamily TrivialAmbientRootFamily)
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTripleCoverFacts
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualNumericalEquiv
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalEquivQOne

universe u

variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
variable [Finite (WeightClass (p := p) (K := K) (X := X))]


open SporadicFi24P3Definition44NamedCarrierOtherPrimeNumericalJoins
open SporadicFi24P3Definition44NamedCarrierAcceleratedDefinition41Certificate

theorem definition41_from_cyclic_inputs
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
    (C : ∀ V : CharacterWeight p K X, CanonicalRawReduction iota V)
    (hpne : p ≠ 3)
    {S : Type u} [Group S] [Fintype S]
    (q : X →* S) (hq : IsUniversalCentralExtension q)
    (hs : IsSimpleGroup S) (hna : ¬ IsMulCommutative S)
    (hkernel : Nat.card q.ker = 3)
    (hOuterS : Nat.card (LiteralOuterQuotient S) = 2)
    (tau : MulAut X)
    (decomposition : ∀ a : MulAut X,
      ∃ x : X, a = MulAut.conj x ∨ a = MulAut.conj x * tau)
    (hinverts : ∀ z : Subgroup.center X, tau (z : X) = (z : X)⁻¹)
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource (p := p) (X := X))
    (Bzero :
      letI := R.1.operations.ambientBlockData.fintypeBlock
      DefectZeroOrdinaryBlockSource iota hinj R.1.operations.ambientBlockData.blocks D)
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (lower : QuotientDataFamily iota hinj R C
      (ellPrimeCover_of_fullCover_kernel_three iota.prime hpne q hq hs hna hkernel))
    (ambientData : TrivialAmbientDataFamily iota hinj R C
      (ellPrimeCover_of_fullCover_kernel_three iota.prime hpne q hq hs hna hkernel) hq)
    (seed : TrivialAmbientRootFamily iota hinj R C
      (ellPrimeCover_of_fullCover_kernel_three iota.prime hpne q hq hs hna hkernel) hq)
    (extensionPrinciple : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} p k)
    (fieldSource : SpathCoefficientField p k iota.prime)
    (S9295 : Navarro9295BrauerRestrictionCoveringPrinciple p k K)
    (S9495 : Navarro9495BrauerCoveringPrinciple p k K)
    (S820 : Navarro820CyclicBrauerTwistPrinciple p k K)
    (cyclicData : CyclicNumericalData iota hinj R tau)
    (allCyclic : ∀ b : (ActualBlock (k := k) (X := X)), HasCyclicDefect iota R b) :
    RawDefinition41Certificate iota R
      (ellPrimeCover_of_fullCover_kernel_three iota.prime hpne q hq hs hna hkernel) := by
  have counts := actual_counts_of_cyclic_blocks iota hinj R tau
    cyclicData allCyclic
  exact raw_of_original (iota := iota) (R := R) (Cover := _) (C := C) (D := D) (T := T)
    (SporadicFi24P3Definition44NamedCarrierOriginalTripleCoverNumerical.exists_definition41_of_actual_counts
      iota hinj R C hpne q hq hs hna hkernel hOuterS tau decomposition hinverts counts
      D T Bzero compatibility lower ambientData seed extensionPrinciple fieldSource S9295 S9495 S820)

theorem definition41_from_five_inputs
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
    (C : ∀ V : CharacterWeight p K X, CanonicalRawReduction iota V)
    (hpne : p ≠ 3)
    {S : Type u} [Group S] [Fintype S]
    (q : X →* S) (hq : IsUniversalCentralExtension q)
    (hs : IsSimpleGroup S) (hna : ¬ IsMulCommutative S)
    (hkernel : Nat.card q.ker = 3)
    (hOuterS : Nat.card (LiteralOuterQuotient S) = 2)
    (tau : MulAut X)
    (decomposition : ∀ a : MulAut X,
      ∃ x : X, a = MulAut.conj x ∨ a = MulAut.conj x * tau)
    (hinverts : ∀ z : Subgroup.center X, tau (z : X) = (z : X)⁻¹)
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource (p := p) (X := X))
    (Bzero :
      letI := R.1.operations.ambientBlockData.fintypeBlock
      DefectZeroOrdinaryBlockSource iota hinj R.1.operations.ambientBlockData.blocks D)
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (lower : QuotientDataFamily iota hinj R C
      (ellPrimeCover_of_fullCover_kernel_three iota.prime hpne q hq hs hna hkernel))
    (ambientData : TrivialAmbientDataFamily iota hinj R C
      (ellPrimeCover_of_fullCover_kernel_three iota.prime hpne q hq hs hna hkernel) hq)
    (seed : TrivialAmbientRootFamily iota hinj R C
      (ellPrimeCover_of_fullCover_kernel_three iota.prime hpne q hq hs hna hkernel) hq)
    (extensionPrinciple : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} p k)
    (fieldSource : SpathCoefficientField p k iota.prime)
    (S9295 : Navarro9295BrauerRestrictionCoveringPrinciple p k K)
    (S9495 : Navarro9495BrauerCoveringPrinciple p k K)
    (S820 : Navarro820CyclicBrauerTwistPrinciple p k K)
    (cyclicData : CyclicNumericalData iota hinj R tau)
    (roles : Fin 7 → (ActualBlock (k := k) (X := X))) (roles_injective : Function.Injective roles)
    (coverage : ∀ b : (ActualBlock (k := k) (X := X)), (∃ i : Fin 7, roles i = b) ∨ HasCyclicDefect iota R b)
    (role_action : ∀ i : Fin 7, MulOpposite.op tau • roles i = roles (fiveOuter i))
    (brauer_counts : ∀ i : Fin 7, (fun b : (ActualBlock (k := k) (X := X)) => Nat.card {phi : IBr iota // (operationsBlock iota hinj R) phi = b}) (roles i) = fiveCount i)
    (weight_counts : ∀ i : Fin 7, (fun b : (ActualBlock (k := k) (X := X)) => Nat.card {w : (WeightClass (p := p) (K := K) (X := X)) // R.1.weightBlock w = b}) (roles i) = fiveCount i)
    (brauer_fixed_counts : ∀ i : Fin 3,
      (fun b : (ActualBlock (k := k) (X := X)) => Nat.card {phi : IBr iota // (operationsBlock iota hinj R) phi = b ∧ MulOpposite.op tau • phi = phi}) (roles (fiveTrivialIndex i)) = fiveTrivialFixedCount i)
    (weight_fixed_counts : ∀ i : Fin 3,
      (fun b : (ActualBlock (k := k) (X := X)) => Nat.card {w : (WeightClass (p := p) (K := K) (X := X)) // R.1.weightBlock w = b ∧ MulOpposite.op tau • w = w}) (roles (fiveTrivialIndex i)) = fiveTrivialFixedCount i) :
    RawDefinition41Certificate iota R
      (ellPrimeCover_of_fullCover_kernel_three iota.prime hpne q hq hs hna hkernel) := by
  have counts := actual_counts_of_five_literal_rows iota hinj R tau
    cyclicData roles roles_injective coverage role_action brauer_counts weight_counts brauer_fixed_counts weight_fixed_counts
  exact raw_of_original (iota := iota) (R := R) (Cover := _) (C := C) (D := D) (T := T)
    (SporadicFi24P3Definition44NamedCarrierOriginalTripleCoverNumerical.exists_definition41_of_actual_counts
      iota hinj R C hpne q hq hs hna hkernel hOuterS tau decomposition hinverts counts
      D T Bzero compatibility lower ambientData seed extensionPrinciple fieldSource S9295 S9495 S820)

section Seven
local instance centerFintype : Fintype (Subgroup.center X) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center X) : k)]

theorem definition41_from_seven_inputs
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
    (C : ∀ V : CharacterWeight p K X, CanonicalRawReduction iota V)
    (hpne : p ≠ 3)
    {S : Type u} [Group S] [Fintype S]
    (q : X →* S) (hq : IsUniversalCentralExtension q)
    (hs : IsSimpleGroup S) (hna : ¬ IsMulCommutative S)
    (hkernel : Nat.card q.ker = 3)
    (hOuterS : Nat.card (LiteralOuterQuotient S) = 2)
    (tau : MulAut X)
    (decomposition : ∀ a : MulAut X,
      ∃ x : X, a = MulAut.conj x ∨ a = MulAut.conj x * tau)
    (hinverts : ∀ z : Subgroup.center X, tau (z : X) = (z : X)⁻¹)
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource (p := p) (X := X))
    (Bzero :
      letI := R.1.operations.ambientBlockData.fintypeBlock
      DefectZeroOrdinaryBlockSource iota hinj R.1.operations.ambientBlockData.blocks D)
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (lower : QuotientDataFamily iota hinj R C
      (ellPrimeCover_of_fullCover_kernel_three iota.prime hpne q hq hs hna hkernel))
    (ambientData : TrivialAmbientDataFamily iota hinj R C
      (ellPrimeCover_of_fullCover_kernel_three iota.prime hpne q hq hs hna hkernel) hq)
    (seed : TrivialAmbientRootFamily iota hinj R C
      (ellPrimeCover_of_fullCover_kernel_three iota.prime hpne q hq hs hna hkernel) hq)
    (extensionPrinciple : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} p k)
    (fieldSource : SpathCoefficientField p k iota.prime)
    (S9295 : Navarro9295BrauerRestrictionCoveringPrinciple p k K)
    (S9495 : Navarro9495BrauerCoveringPrinciple p k K)
    (S820 : Navarro820CyclicBrauerTwistPrinciple p k K)
    (cyclicData : CyclicNumericalData iota hinj R tau)
    (distinguished : CentralSector (k := k) (X := X) → (ActualBlock (k := k) (X := X)))
    (distinguished_sector : ∀ nu, blockSector (distinguished nu) = nu)
    (cyclic_complement : ∀ nu (b : (ActualBlock (k := k) (X := X))), blockSector b = nu →
      b ≠ distinguished nu → HasCyclicDefect iota R b)
    (sectorCount : CentralSector (k := k) (X := X) → ℕ)
    (brauer_sector_counts : ∀ nu,
      Nat.card {phi : IBr iota // blockSector ((operationsBlock iota hinj R) phi) = nu} = sectorCount nu)
    (weight_sector_counts : ∀ nu,
      Nat.card {w : (WeightClass (p := p) (K := K) (X := X)) // blockSector (R.1.weightBlock w) = nu} = sectorCount nu)
    (trivialFixedCount : ℕ)
    (brauer_trivial_fixed : Nat.card {phi : IBr iota //
      blockSector ((operationsBlock iota hinj R) phi) = 1 ∧ MulOpposite.op tau • phi = phi} = trivialFixedCount)
    (weight_trivial_fixed : Nat.card {w : (WeightClass (p := p) (K := K) (X := X)) //
      blockSector (R.1.weightBlock w) = 1 ∧ MulOpposite.op tau • w = w} = trivialFixedCount) :
    RawDefinition41Certificate iota R
      (ellPrimeCover_of_fullCover_kernel_three iota.prime hpne q hq hs hna hkernel) := by
  have hcenter := center_card_three_of_fullCover q hq hs hna hkernel
  have counts := actual_counts_of_seven_sector_cancellation iota hinj R tau
    cyclicData hcenter hinverts distinguished distinguished_sector cyclic_complement sectorCount brauer_sector_counts weight_sector_counts trivialFixedCount brauer_trivial_fixed weight_trivial_fixed
  exact raw_of_original (iota := iota) (R := R) (Cover := _) (C := C) (D := D) (T := T)
    (SporadicFi24P3Definition44NamedCarrierOriginalTripleCoverNumerical.exists_definition41_of_actual_counts
      iota hinj R C hpne q hq hs hna hkernel hOuterS tau decomposition hinverts counts
      D T Bzero compatibility lower ambientData seed extensionPrinciple fieldSource S9295 S9495 S820)

end Seven

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedOtherPrimeApplications


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
