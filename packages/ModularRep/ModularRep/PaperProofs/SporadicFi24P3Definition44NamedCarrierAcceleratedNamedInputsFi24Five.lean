import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedCaseApplications
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedOtherPrimeApplications
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedModels

/-! The named Fi24Five input constructor stores only the checked application's
lower telescope and an explicit named-base equivalence. Its complete certificate
is produced by realise, never supplied as an input. -/
noncomputable section
open scoped MonoidAlgebra
set_option maxHeartbeats 4000000
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Five
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

open SporadicFi24P3Definition44NamedCarrierOtherPrimeNumericalJoins
open SporadicFi24P3Definition44NamedCarrierAcceleratedDefinition41Certificate
open ModularRep ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedModels
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedDefinition41Certificate
universe u

local instance brauerFintype {p : ℕ} {k K X : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group X] [Fintype X] (iota : PrimeRegularRootEmbedding p k K X) :
    Fintype (IBr iota) := Fintype.ofFinite _
local instance centerFintype {X : Type u} [Group X] [Fintype X] :
    Fintype (Subgroup.center X) := Fintype.ofFinite _
local instance quotientFintype {X : Type u} [Group X] [Fintype X] :
    Fintype (X ⧸ Subgroup.center X) := Fintype.ofFinite _

inductive Inputs (base : NamedBase.{u}) : Type (u + 1) where
  | mk
    {k K X : Type u}
    [inputInst1 : Field k]
    [inputInst2 : Field K]
    [inputInst3 : CharP k 5]
    [inputInst4 : IsAlgClosed k]
    [inputInst5 : CharZero K]
    [inputInst6 : Group X]
    [inputInst7 : Fintype X]
    [inputInst8 : Finite (WeightClass (p := 5) (K := K) (X := X))]
    (iota : PrimeRegularRootEmbedding 5 k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralCarrierAdapter (p := 5) (k := k) (K := K) (X := X))
    (C : ∀ V : CharacterWeight 5 K X, CanonicalRawReduction iota V)
    (hpne : 5 ≠ 3)
    {S : Type u}
    [inputInst9 : Group S]
    [inputInst10 : Fintype S]
    (q : X →* S)
    (hq : IsUniversalCentralExtension q)
    (hs : IsSimpleGroup S)
    (hna : ¬ IsMulCommutative S)
    (hkernel : Nat.card q.ker = 3)
    (hOuterS : Nat.card (LiteralOuterQuotient S) = 2)
    (tau : MulAut X)
    (decomposition : ∀ a : MulAut X,
          ∃ x : X, a = MulAut.conj x ∨ a = MulAut.conj x * tau)
    (hinverts : ∀ z : Subgroup.center X, tau (z : X) = (z : X)⁻¹)
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource (p := 5) (X := X))
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
    (extensionPrinciple : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} 5 k)
    (fieldSource : SpathCoefficientField 5 k iota.prime)
    (S9295 : Navarro9295BrauerRestrictionCoveringPrinciple 5 k K)
    (S9495 : Navarro9495BrauerCoveringPrinciple 5 k K)
    (S820 : Navarro820CyclicBrauerTwistPrinciple 5 k K)
    (cyclicData : CyclicNumericalData iota hinj R tau)
    (roles : Fin 7 → (ActualBlock (k := k) (X := X)))
    (roles_injective : Function.Injective roles)
    (coverage : ∀ b : (ActualBlock (k := k) (X := X)), (∃ i : Fin 7, roles i = b) ∨ HasCyclicDefect iota R b)
    (role_action : ∀ i : Fin 7, MulOpposite.op tau • roles i = roles (fiveOuter i))
    (brauer_counts : ∀ i : Fin 7, (fun b : (ActualBlock (k := k) (X := X)) => Nat.card {phi : IBr iota // (operationsBlock iota hinj R) phi = b}) (roles i) = fiveCount i)
    (weight_counts : ∀ i : Fin 7, (fun b : (ActualBlock (k := k) (X := X)) => Nat.card {w : (WeightClass (p := 5) (K := K) (X := X)) // R.1.weightBlock w = b}) (roles i) = fiveCount i)
    (brauer_fixed_counts : ∀ i : Fin 3,
          (fun b : (ActualBlock (k := k) (X := X)) => Nat.card {phi : IBr iota // (operationsBlock iota hinj R) phi = b ∧ MulOpposite.op tau • phi = phi}) (roles (fiveTrivialIndex i)) = fiveTrivialFixedCount i)
    (weight_fixed_counts : ∀ i : Fin 3,
          (fun b : (ActualBlock (k := k) (X := X)) => Nat.card {w : (WeightClass (p := 5) (K := K) (X := X)) // R.1.weightBlock w = b ∧ MulOpposite.op tau • w = w}) (roles (fiveTrivialIndex i)) = fiveTrivialFixedCount i)
    (namedBaseEquiv : ((ellPrimeCover_of_fullCover_kernel_three iota.prime hpne q hq hs hna hkernel)).S ≃* base.S) : Inputs base

def realise {base : NamedBase.{u}} (I : Inputs base) :
    {M : CaseModel base 5 // RawCaseConclusion M} := by
  cases I with
  | @mk k K X inputInst1 inputInst2 inputInst3 inputInst4 inputInst5 inputInst6 inputInst7 inputInst8 iota hinj R C hpne S inputInst9 inputInst10 q hq hs hna hkernel hOuterS tau decomposition hinverts D T Bzero compatibility lower ambientData seed extensionPrinciple fieldSource S9295 S9495 S820 cyclicData roles roles_injective coverage role_action brauer_counts weight_counts brauer_fixed_counts weight_fixed_counts namedBaseEquiv =>
      let selectedCover : EllPrimeCoverSource 5 X := (ellPrimeCover_of_fullCover_kernel_three iota.prime hpne q hq hs hna hkernel)
      let M : CaseModel base 5 := {
        k := k, K := K, X := X,
        iota := iota, R := R, Cover := selectedCover, baseEquiv := namedBaseEquiv }
      refine ⟨M, ?_⟩
      change RawDefinition41Certificate iota R selectedCover
      exact ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedOtherPrimeApplications.definition41_from_five_inputs
        (p := 5)
        (k := k)
        (K := K)
        (X := X)
        (iota := iota)
        (hinj := hinj)
        (R := R)
        (C := C)
        (hpne := hpne)
        (S := S)
        (q := q)
        (hq := hq)
        (hs := hs)
        (hna := hna)
        (hkernel := hkernel)
        (hOuterS := hOuterS)
        (tau := tau)
        (decomposition := decomposition)
        (hinverts := hinverts)
        (D := D)
        (T := T)
        (Bzero := Bzero)
        (compatibility := compatibility)
        (lower := lower)
        (ambientData := ambientData)
        (seed := seed)
        (extensionPrinciple := extensionPrinciple)
        (fieldSource := fieldSource)
        (S9295 := S9295)
        (S9495 := S9495)
        (S820 := S820)
        (cyclicData := cyclicData)
        (roles := roles)
        (roles_injective := roles_injective)
        (coverage := coverage)
        (role_action := role_action)
        (brauer_counts := brauer_counts)
        (weight_counts := weight_counts)
        (brauer_fixed_counts := brauer_fixed_counts)
        (weight_fixed_counts := weight_fixed_counts)

def model {base : NamedBase.{u}} (I : Inputs base) : CaseModel base 5 :=
  (realise I).val

theorem certificate {base : NamedBase.{u}} (I : Inputs base) :
    RawCaseConclusion (model I) := (realise I).property

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Five


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
