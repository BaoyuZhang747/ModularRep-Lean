import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedCaseApplications
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedOtherPrimeApplications
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedModels

/-! The named Fi24Three input constructor stores only the checked application's
lower telescope and an explicit named-base equivalence. Its complete certificate
is produced by realise, never supplied as an input. -/
noncomputable section
open scoped MonoidAlgebra
set_option maxHeartbeats 4000000
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Three
open ModularRep ModularRep.CharacterWeight
open SporadicFi24CentralSectorAssemblyLemma56Actual
open EvenFieldFLZSourceConditions
open SporadicFi24P3Definition44NamedCarrierAcceleratedP3Application
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
    {SourceAction SourceBrauer SourceWeight : Type u}
    [inputInst1 : Group SourceAction]
    [inputInst2 : MulAction SourceAction SourceBrauer]
    [inputInst3 : MulAction SourceAction SourceWeight]
    {k K X : Type u}
    [inputInst4 : Field k]
    [inputInst5 : Field K]
    [inputInst6 : CharP k 3]
    [inputInst7 : IsAlgClosed k]
    [inputInst8 : CharZero K]
    [inputInst9 : Group X]
    [inputInst10 : Fintype X]
    (iota : PrimeRegularRootEmbedding 3 k K X)
    (R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := X))
    (Cover : EllPrimeCoverSource 3 X)
    (I : ExternalInputs (SourceAction := SourceAction) (SourceBrauer := SourceBrauer)
          (SourceWeight := SourceWeight) iota R)
    (namedBaseEquiv : (Cover).S ≃* base.S) : Inputs base

def realise {base : NamedBase.{u}} (I : Inputs base) :
    {M : CaseModel base 3 // RawCaseConclusion M} := by
  cases I with
  | @mk SourceAction SourceBrauer SourceWeight inputInst1 inputInst2 inputInst3 k K X inputInst4 inputInst5 inputInst6 inputInst7 inputInst8 inputInst9 inputInst10 iota R Cover I namedBaseEquiv =>
      let selectedCover : EllPrimeCoverSource 3 X := Cover
      let M : CaseModel base 3 := {
        k := k, K := K, X := X,
        iota := iota, R := R, Cover := selectedCover, baseEquiv := namedBaseEquiv }
      refine ⟨M, ?_⟩
      change RawDefinition41Certificate iota R selectedCover
      exact ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedCaseApplications.Fi24Three.definition41_from_external_inputs
        (SourceAction := SourceAction)
        (SourceBrauer := SourceBrauer)
        (SourceWeight := SourceWeight)
        (k := k)
        (K := K)
        (X := X)
        (iota := iota)
        (R := R)
        (Cover := Cover)
        (I := I)

def model {base : NamedBase.{u}} (I : Inputs base) : CaseModel base 3 :=
  (realise I).val

theorem certificate {base : NamedBase.{u}} (I : Inputs base) :
    RawCaseConclusion (model I) := (realise I).property

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Three


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
