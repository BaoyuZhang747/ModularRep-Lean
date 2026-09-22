import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualBlockOrdinarySpan
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierKleinFourIntegerData

/-! Complete selected ordinary rows for any specified role in the printed trivial sector. -/

noncomputable section
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualBlockOrdinaryAllocation

open ModularRep ModularRep.FDRepSimpleClassKZero
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierActualSectorOrdinarySpan
open SporadicFi24P3Definition44NamedCarrierKleinFourIntegerData

universe u v
variable {p : ℕ} {k K X BlockIndex : Type u} {Row : Type v}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X] [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}
variable (iota : PrimeRegularRootEmbedding p k K X)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
local instance centerFintype : Fintype (Subgroup.center X) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center X) : k)]

theorem blockRows_complete_of_printed_allocation
    (D : ActualOrdinaryDecomposition iota hinj blocks)
    (C : ActualSectorOrdinaryRows iota hinj blocks D
      (1 : CentralSector (k := k) (X := X)) (Fin 108))
    (trivialRoles : Fin 5 ≃
      {b : ActualBlock (k := k) (X := X) // blockSector b = 1})
    (allocation : ∀ r, D.ordinaryBlock (C.character r) =
      (trivialRoles (printedBlockLabel r)).1)
    (j : Fin 5) (rowPosition : Row → Fin 108)
    (rowFibre : ∀ r, printedBlockLabel r = j ↔ ∃ i, rowPosition i = r) :
    ∀ chi, D.ordinaryBlock chi = (trivialRoles j).1 ↔
      ∃ i : Row, C.character (rowPosition i) = chi := by
  intro chi
  constructor
  · intro hchi
    have hsector : blockSector (D.ordinaryBlock chi) = 1 := by
      rw [hchi]
      exact (trivialRoles j).2
    obtain ⟨r, hr⟩ := (C.complete chi).1 hsector
    have hphysical : (trivialRoles (printedBlockLabel r)).1 = (trivialRoles j).1 :=
      (allocation r).symm.trans ((congrArg D.ordinaryBlock hr).trans hchi)
    have hlabel : printedBlockLabel r = j :=
      trivialRoles.injective (Subtype.ext hphysical)
    obtain ⟨i, hi⟩ := (rowFibre r).1 hlabel
    exact ⟨i, (congrArg C.character hi).trans hr⟩
  · rintro ⟨i, rfl⟩
    exact (allocation (rowPosition i)).trans
      (congrArg (fun t : Fin 5 => (trivialRoles t).1)
        ((rowFibre (rowPosition i)).2 ⟨i, rfl⟩))

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualBlockOrdinaryAllocation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
