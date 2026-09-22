import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedCaseApplications
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedOtherPrimeApplications
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedModels

/-! The named BabyOdd input constructor stores only the checked application's
lower telescope and an explicit named-base equivalence. Its complete certificate
is produced by realise, never supplied as an input. -/
noncomputable section
open scoped MonoidAlgebra
set_option maxHeartbeats 4000000
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsBabyOdd
open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalDefinition41
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalIdentityFamily
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalDefectCounts
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierJ4Numerical
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCoverGroupFacts
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCoverAutomorphisms

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

inductive Inputs (base : NamedBase.{u}) (p : ℕ) : Type (u + 1) where
  | mk
    {k K X S : Type u}
    [inputInst1 : Field k]
    [inputInst2 : Field K]
    [inputInst3 : CharP k p]
    [inputInst4 : IsAlgClosed k]
    [inputInst5 : CharZero K]
    [inputInst6 : Group X]
    [inputInst7 : Fintype X]
    [inputInst8 : Group S]
    [inputInst9 : Fintype S]
    [inputInst10 : Fintype (WeightClass (p := p) (K := K) (X := X))]
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralBlockSource (p := p) (k := k) (K := K) (X := X))
    (C : ∀ V : CharacterWeight p K X, CanonicalRawReduction iota V)
    (hpne : p ≠ 2)
    (q : X →* S)
    (hq : IsUniversalCentralExtension q)
    (hkernel : Nat.card q.ker = 2)
    (hs : IsSimpleGroup S)
    (hna : ¬ IsMulCommutative S)
    (hOuter : Nat.card ((MulAut S)ᵐᵒᵖ ⧸
          (RepresentationWeight.innerInverseOpHom (G := S)).range) = 1)
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource (p := p) (X := X))
    (source : CyclicNoncyclicNumericalSource iota hinj R)
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (lower : QuotientDataFamily iota hinj R C
          (ellPrimeCover_of_fullCover_kernel_two iota.prime hpne q hq hs hna hkernel))
    (fieldSource : SpathCoefficientField p k iota.prime)
    (namedBaseEquiv : (ellPrimeCover_of_fullCover_kernel_two iota.prime hpne q hq hs hna hkernel).S ≃* base.S) : Inputs base p

def realise {base : NamedBase.{u}} {p : ℕ} (I : Inputs base p) :
    {M : CaseModel base p // RawCaseConclusion M} := by
  cases I with
  | @mk k K X S inputInst1 inputInst2 inputInst3 inputInst4 inputInst5 inputInst6 inputInst7 inputInst8 inputInst9 inputInst10 iota hinj R C hpne q hq hkernel hs hna hOuter D T source compatibility lower fieldSource namedBaseEquiv =>
      let selectedCover : EllPrimeCoverSource p X := ellPrimeCover_of_fullCover_kernel_two iota.prime hpne q hq hs hna hkernel
      let M : CaseModel base p := {
        k := k, K := K, X := X,
        iota := iota, R := R, Cover := selectedCover, baseEquiv := namedBaseEquiv }
      refine ⟨M, ?_⟩
      change RawDefinition41Certificate iota R selectedCover
      exact ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedCaseApplications.BabyOdd.definition41_from_external_inputs
        (p := p)
        (k := k)
        (K := K)
        (X := X)
        (S := S)
        (iota := iota)
        (hinj := hinj)
        (R := R)
        (C := C)
        (hpne := hpne)
        (q := q)
        (hq := hq)
        (hkernel := hkernel)
        (hs := hs)
        (hna := hna)
        (hOuter := hOuter)
        (D := D)
        (T := T)
        (source := source)
        (compatibility := compatibility)
        (lower := lower)
        (fieldSource := fieldSource)

def model {base : NamedBase.{u}} {p : ℕ} (I : Inputs base p) : CaseModel base p :=
  (realise I).val

theorem certificate {base : NamedBase.{u}} {p : ℕ} (I : Inputs base p) :
    RawCaseConclusion (model I) := (realise I).property

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsBabyOdd


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
