import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedCaseApplications
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedOtherPrimeApplications
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedModels

/-! The named MonsterOdd input constructor stores only the checked application's
lower telescope and an explicit named-base equivalence. Its complete certificate
is produced by realise, never supplied as an input. -/
noncomputable section
open scoped MonoidAlgebra
set_option maxHeartbeats 4000000
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsMonsterOdd
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierMonsterOddSources
open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalDefinition41
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalJ4Numerical
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierJ4Numerical
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSelfCover

open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierJ4FullCover
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

inductive Inputs (base : NamedBase.{u}) (p : ℕ) : Type (u + 1) where
  | mk
    {k K U X : Type u}
    [inputInst1 : Field k]
    [inputInst2 : Field K]
    [inputInst3 : CharP k p]
    [inputInst4 : IsAlgClosed k]
    [inputInst5 : CharZero K]
    [inputInst6 : Group U]
    [inputInst7 : Group X]
    [inputInst8 : Fintype X]
    [inputInst9 : Fintype (WeightClass (p := p) (K := K) (X := X))]
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralBlockSource (p := p) (k := k) (K := K) (X := X))
    (C : ∀ V : CharacterWeight p K X, CanonicalRawReduction iota V)
    (cover : U →* X)
    (hcover : IsUniversalCentralExtension cover)
    (hkernel : Nat.card cover.ker = 1)
    (hsimple : IsSimpleGroup X)
    (hnonabelian : ¬ IsMulCommutative X)
    (hOuter : Nat.card ((MulAut X)ᵐᵒᵖ ⧸
          (RepresentationWeight.innerInverseOpHom (G := X)).range) = 1)
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource (p := p) (X := X))
    (hpOdd : 3 ≤ p)
    (source : MonsterOddNumericalSource iota hinj R)
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (fieldSource : SpathCoefficientField p k iota.prime)
    (namedBaseEquiv : (identityEllPrimeCover_of_fullCover_kernel_card_one iota.prime cover hcover hkernel hsimple hnonabelian).S ≃* base.S) : Inputs base p

def realise {base : NamedBase.{u}} {p : ℕ} (I : Inputs base p) :
    {M : CaseModel base p // RawCaseConclusion M} := by
  cases I with
  | @mk k K U X inputInst1 inputInst2 inputInst3 inputInst4 inputInst5 inputInst6 inputInst7 inputInst8 inputInst9 iota hinj R C cover hcover hkernel hsimple hnonabelian hOuter D T hpOdd source compatibility fieldSource namedBaseEquiv =>
      let selectedCover : EllPrimeCoverSource p X := identityEllPrimeCover_of_fullCover_kernel_card_one iota.prime cover hcover hkernel hsimple hnonabelian
      let M : CaseModel base p := {
        k := k, K := K, X := X,
        iota := iota, R := R, Cover := selectedCover, baseEquiv := namedBaseEquiv }
      refine ⟨M, ?_⟩
      change RawDefinition41Certificate iota R selectedCover
      exact ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedCaseApplications.MonsterOdd.definition41_from_external_inputs
        (p := p)
        (k := k)
        (K := K)
        (U := U)
        (X := X)
        (iota := iota)
        (hinj := hinj)
        (R := R)
        (C := C)
        (cover := cover)
        (hcover := hcover)
        (hkernel := hkernel)
        (hsimple := hsimple)
        (hnonabelian := hnonabelian)
        (hOuter := hOuter)
        (D := D)
        (T := T)
        (hpOdd := hpOdd)
        (source := source)
        (compatibility := compatibility)
        (fieldSource := fieldSource)

def model {base : NamedBase.{u}} {p : ℕ} (I : Inputs base p) : CaseModel base p :=
  (realise I).val

theorem certificate {base : NamedBase.{u}} {p : ℕ} (I : Inputs base p) :
    RawCaseConclusion (model I) := (realise I).property

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsMonsterOdd


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
