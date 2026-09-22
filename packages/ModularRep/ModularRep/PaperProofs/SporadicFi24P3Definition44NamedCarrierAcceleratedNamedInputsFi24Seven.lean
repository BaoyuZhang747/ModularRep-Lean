import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedCaseApplications
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedOtherPrimeApplications
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedModels

/-! The named Fi24Seven input constructor stores only the checked application's
lower telescope and an explicit named-base equivalence. Its complete certificate
is produced by realise, never supplied as an input. -/
noncomputable section
open scoped MonoidAlgebra
set_option maxHeartbeats 4000000
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Seven
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
    [inputInst3 : CharP k 7]
    [inputInst4 : IsAlgClosed k]
    [inputInst5 : CharZero K]
    [inputInst6 : Group X]
    [inputInst7 : Fintype X]
    [inputInst8 : Finite (WeightClass (p := 7) (K := K) (X := X))]
    [inputInst9 : Invertible (Fintype.card (Subgroup.center X) : k)]
    (iota : PrimeRegularRootEmbedding 7 k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralCarrierAdapter (p := 7) (k := k) (K := K) (X := X))
    (C : ∀ V : CharacterWeight 7 K X, CanonicalRawReduction iota V)
    (hpne : 7 ≠ 3)
    {S : Type u}
    [inputInst10 : Group S]
    [inputInst11 : Fintype S]
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
    (T : TrivialWeightSource (p := 7) (X := X))
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
    (extensionPrinciple : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} 7 k)
    (fieldSource : SpathCoefficientField 7 k iota.prime)
    (S9295 : Navarro9295BrauerRestrictionCoveringPrinciple 7 k K)
    (S9495 : Navarro9495BrauerCoveringPrinciple 7 k K)
    (S820 : Navarro820CyclicBrauerTwistPrinciple 7 k K)
    (cyclicData : CyclicNumericalData iota hinj R tau)
    (distinguished : CentralSector (k := k) (X := X) → (ActualBlock (k := k) (X := X)))
    (distinguished_sector : ∀ nu, blockSector (distinguished nu) = nu)
    (cyclic_complement : ∀ nu (b : (ActualBlock (k := k) (X := X))), blockSector b = nu →
          b ≠ distinguished nu → HasCyclicDefect iota R b)
    (sectorCount : CentralSector (k := k) (X := X) → ℕ)
    (brauer_sector_counts : ∀ nu,
          Nat.card {phi : IBr iota // blockSector ((operationsBlock iota hinj R) phi) = nu} = sectorCount nu)
    (weight_sector_counts : ∀ nu,
          Nat.card {w : (WeightClass (p := 7) (K := K) (X := X)) // blockSector (R.1.weightBlock w) = nu} = sectorCount nu)
    (trivialFixedCount : ℕ)
    (brauer_trivial_fixed : Nat.card {phi : IBr iota //
          blockSector ((operationsBlock iota hinj R) phi) = 1 ∧ MulOpposite.op tau • phi = phi} = trivialFixedCount)
    (weight_trivial_fixed : Nat.card {w : (WeightClass (p := 7) (K := K) (X := X)) //
          blockSector (R.1.weightBlock w) = 1 ∧ MulOpposite.op tau • w = w} = trivialFixedCount)
    (namedBaseEquiv : ((ellPrimeCover_of_fullCover_kernel_three iota.prime hpne q hq hs hna hkernel)).S ≃* base.S) : Inputs base

def realise {base : NamedBase.{u}} (I : Inputs base) :
    {M : CaseModel base 7 // RawCaseConclusion M} := by
  cases I with
  | @mk k K X inputInst1 inputInst2 inputInst3 inputInst4 inputInst5 inputInst6 inputInst7 inputInst8 inputInst9 iota hinj R C hpne S inputInst10 inputInst11 q hq hs hna hkernel hOuterS tau decomposition hinverts D T Bzero compatibility lower ambientData seed extensionPrinciple fieldSource S9295 S9495 S820 cyclicData distinguished distinguished_sector cyclic_complement sectorCount brauer_sector_counts weight_sector_counts trivialFixedCount brauer_trivial_fixed weight_trivial_fixed namedBaseEquiv =>
      let selectedCover : EllPrimeCoverSource 7 X := (ellPrimeCover_of_fullCover_kernel_three iota.prime hpne q hq hs hna hkernel)
      let M : CaseModel base 7 := {
        k := k, K := K, X := X,
        iota := iota, R := R, Cover := selectedCover, baseEquiv := namedBaseEquiv }
      refine ⟨M, ?_⟩
      change RawDefinition41Certificate iota R selectedCover
      exact ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedOtherPrimeApplications.definition41_from_seven_inputs
        (p := 7)
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
        (distinguished := distinguished)
        (distinguished_sector := distinguished_sector)
        (cyclic_complement := cyclic_complement)
        (sectorCount := sectorCount)
        (brauer_sector_counts := brauer_sector_counts)
        (weight_sector_counts := weight_sector_counts)
        (trivialFixedCount := trivialFixedCount)
        (brauer_trivial_fixed := brauer_trivial_fixed)
        (weight_trivial_fixed := weight_trivial_fixed)

def model {base : NamedBase.{u}} (I : Inputs base) : CaseModel base 7 :=
  (realise I).val

theorem certificate {base : NamedBase.{u}} (I : Inputs base) :
    RawCaseConclusion (model I) := (realise I).property

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Seven


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
