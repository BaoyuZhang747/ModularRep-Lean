import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedCaseApplications
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedOtherPrimeApplications
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedModels

/-! The named BabyTwo input constructor stores only the checked application's
lower telescope and an explicit named-base equivalence. Its complete certificate
is produced by realise, never supplied as an input. -/
noncomputable section
open scoped MonoidAlgebra
set_option maxHeartbeats 4000000
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsBabyTwo
open ModularRep
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
  (ActualBlock LiteralBlockSource DefectZeroReductionSource TrivialWeightSource)
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSelfCover
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierJ4FullCover
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBabyTwoSources
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalBabyTwoNumerical
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalDefinition41

open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBabyTwoFullCover
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction

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
    {k K U X : Type u}
    [inputInst1 : Field k]
    [inputInst2 : Field K]
    [inputInst3 : CharP k 2]
    [inputInst4 : IsAlgClosed k]
    [inputInst5 : CharZero K]
    [inputInst6 : Group U]
    [inputInst7 : Group X]
    [inputInst8 : Fintype X]
    (iota : PrimeRegularRootEmbedding 2 k K X)
    (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralBlockSource (p := 2) (k := k) (K := K) (X := X))
    (source : BabyTwoSource iota hinj R)
    (small : SmallDefectNumericalSource iota hinj R)
    (C : ∀ V : CharacterWeight 2 K X, CanonicalRawReduction iota V)
    (cover : U →* X)
    (hcover : IsUniversalCentralExtension cover)
    (hkernel : Nat.card cover.ker = 2)
    (hsimple : IsSimpleGroup X)
    (hnonabelian : ¬ IsMulCommutative X)
    (hOuter : Nat.card ((MulAut X)ᵐᵒᵖ ⧸
          (RepresentationWeight.innerInverseOpHom (G := X)).range) = 1)
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource (p := 2) (X := X))
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (fieldSource : SpathCoefficientField 2 k iota.prime)
    (namedBaseEquiv : (identityTwoPrimeCover_of_fullCover_kernel_card_two cover hcover hkernel hsimple hnonabelian).S ≃* base.S) : Inputs base

def realise {base : NamedBase.{u}} (I : Inputs base) :
    {M : CaseModel base 2 // RawCaseConclusion M} := by
  cases I with
  | @mk k K U X inputInst1 inputInst2 inputInst3 inputInst4 inputInst5 inputInst6 inputInst7 inputInst8 iota hinj R source small C cover hcover hkernel hsimple hnonabelian hOuter D T compatibility fieldSource namedBaseEquiv =>
      let selectedCover : EllPrimeCoverSource 2 X := identityTwoPrimeCover_of_fullCover_kernel_card_two cover hcover hkernel hsimple hnonabelian
      let M : CaseModel base 2 := {
        k := k, K := K, X := X,
        iota := iota, R := R, Cover := selectedCover, baseEquiv := namedBaseEquiv }
      refine ⟨M, ?_⟩
      change RawDefinition41Certificate iota R selectedCover
      exact ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedCaseApplications.BabyTwo.definition41_from_external_inputs
        (k := k)
        (K := K)
        (U := U)
        (X := X)
        (iota := iota)
        (hinj := hinj)
        (R := R)
        (source := source)
        (small := small)
        (C := C)
        (cover := cover)
        (hcover := hcover)
        (hkernel := hkernel)
        (hsimple := hsimple)
        (hnonabelian := hnonabelian)
        (hOuter := hOuter)
        (D := D)
        (T := T)
        (compatibility := compatibility)
        (fieldSource := fieldSource)

def model {base : NamedBase.{u}} (I : Inputs base) : CaseModel base 2 :=
  (realise I).val

theorem certificate {base : NamedBase.{u}} (I : Inputs base) :
    RawCaseConclusion (model I) := (realise I).property

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsBabyTwo


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
