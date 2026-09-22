import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualBlockOrdinarySpan
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulSmallPolynomialData

/-! The literal faithful label fibre selects all ordinary characters of specified role one. -/

noncomputable section
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulBlockOrdinaryAllocation

open ModularRep ModularRep.FDRepSimpleClassKZero
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierActualSectorOrdinarySpan
open SporadicFi24P3Definition44NamedCarrierFaithfulSmallPolynomialData

universe u
variable {p : ℕ} {k K X BlockIndex : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X] [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}
variable (iota : PrimeRegularRootEmbedding p k K X)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
local instance centerFintype : Fintype (Subgroup.center X) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center X) : k)]

theorem faithfulSmallRows_complete_of_allocation
    (D : ActualOrdinaryDecomposition iota hinj blocks)
    (nu : {nu : CentralSector (k := k) (X := X) // nu ≠ 1})
    (C : ActualSectorOrdinaryRows iota hinj blocks D nu.1 (Fin 74))
    (roles : Fin 2 ≃
      {b : ActualBlock (k := k) (X := X) // blockSector b = nu.1})
    (allocation : ∀ r, D.ordinaryBlock (C.character r) =
      (roles (faithfulPrintedBlockLabel r)).1) :
    ∀ chi, D.ordinaryBlock chi = (roles 1).1 ↔
      ∃ i : Fin 5, C.character (faithfulSmallRow i) = chi := by
  intro chi
  constructor
  · intro hchi
    have hsector : blockSector (D.ordinaryBlock chi) = nu.1 := by
      rw [hchi]
      exact (roles 1).2
    obtain ⟨r, hr⟩ := (C.complete chi).1 hsector
    have hphysical : (roles (faithfulPrintedBlockLabel r)).1 = (roles 1).1 :=
      (allocation r).symm.trans ((congrArg D.ordinaryBlock hr).trans hchi)
    have hlabel : faithfulPrintedBlockLabel r = 1 :=
      roles.injective (Subtype.ext hphysical)
    obtain ⟨i, hi⟩ := (faithfulSmall_fibre r).1 hlabel
    exact ⟨i, (congrArg C.character hi).trans hr⟩
  · rintro ⟨i, rfl⟩
    exact (allocation (faithfulSmallRow i)).trans
      (congrArg (fun j : Fin 2 => (roles j).1)
        ((faithfulSmall_fibre (faithfulSmallRow i)).2 ⟨i, rfl⟩))

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulBlockOrdinaryAllocation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
