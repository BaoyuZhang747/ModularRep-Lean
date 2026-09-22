import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedDefinition41Certificate
import Formalisation.DependencyCases

/-! Named carriers and relevant-prime problems for the fixed sporadic join.
Names are externally interpreted; the explicit base equivalence ties every
prime's cover to the same selected finite simple-group carrier. This file
contains descriptors and fixed conclusions, not a claimed final sporadic proof. -/
noncomputable section
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedModels
open Formalisation.DependencyCases
open ModularRep
open EvenFieldFLZSourceConditions
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierAcceleratedDefinition41Certificate
universe u

structure NamedBase where
  S : Type u
  [groupS : Group S]
  [fintypeS : Fintype S]
attribute [instance] NamedBase.groupS NamedBase.fintypeS

structure CaseModel (base : NamedBase.{u}) (p : ℕ) where
  k : Type u
  K : Type u
  X : Type u
  [fieldk : Field k]
  [fieldK : Field K]
  [charPk : CharP k p]
  [algClosedk : IsAlgClosed k]
  [charZeroK : CharZero K]
  [groupX : Group X]
  [fintypeX : Fintype X]
  iota : PrimeRegularRootEmbedding p k K X
  R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X)
  Cover : EllPrimeCoverSource p X
  baseEquiv : Cover.S ≃* base.S
attribute [instance]
  CaseModel.fieldk CaseModel.fieldK CaseModel.charPk CaseModel.algClosedk
  CaseModel.charZeroK CaseModel.groupX CaseModel.fintypeX

def RelevantPrime (base : NamedBase.{u}) (p : ℕ) : Prop :=
  Nat.Prime p ∧ p ∣ Nat.card base.S

abbrev RelevantCase (bases : SporadicGroup → NamedBase.{u}) :=
  Σ s : SporadicGroup, {p : ℕ // RelevantPrime (bases s) p}

def RawCaseConclusion {base : NamedBase.{u}} {p : ℕ} (M : CaseModel base p) : Prop :=
  RawDefinition41Certificate M.iota M.R M.Cover

def RawSporadicConclusion (bases : SporadicGroup → NamedBase.{u})
    (models : (c : RelevantCase bases) → CaseModel (bases c.1) c.2.val) : Prop :=
  ∀ c, RawCaseConclusion (models c)

/-- The full inductive condition requires compatible roots in the selected
extension and intermediate block witnesses. -/
def CaseConclusion {base : NamedBase.{u}} {p : ℕ} (M : CaseModel base p) : Prop :=
  Definition41Certificate M.iota M.R M.Cover

def SporadicConclusion (bases : SporadicGroup → NamedBase.{u})
    (models : (c : RelevantCase bases) → CaseModel (bases c.1) c.2.val) : Prop :=
  ∀ c, CaseConclusion (models c)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedModels


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
