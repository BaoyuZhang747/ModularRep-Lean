import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalBaseBlockData
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualOuterQuotient

/-! All intermediate block data are combined from two internally derived
endpoint records and the actual quotient cardinal bound. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualIntermediateAssembly

open ModularRep
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualRadicalPacket

universe u

def actualIntermediateOfBaseOrTop
    (P : Definition35Problem.{u}) {A : Type u} [Group A] [Fintype A]
    (B D : Subgroup A) [B.Normal]
    (globalCharacter : PrimeRegularClassFunction P.K A P.p)
    (localCharacter : PrimeRegularClassFunction P.K D P.p)
    (hcard : Nat.card (A ⧸ B) ≤ 2)
    (atBase : ActualIntermediateBlockData P D globalCharacter localCharacter B)
    (atTop : ActualIntermediateBlockData P D globalCharacter localCharacter ⊤) :
    ∀ J : Subgroup A, B ≤ J →
      ActualIntermediateBlockData P D globalCharacter localCharacter J := by
  classical
  intro J hJ
  by_cases hbase : J = B
  · subst J
    exact atBase
  · have htop := (subgroup_eq_base_or_top_of_quotient_card_le_two B hcard J hJ).resolve_left hbase
    subst J
    exact atTop

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualIntermediateAssembly


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
