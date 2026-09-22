import ModularRep.BrauerRootConvention
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIntermediateBlockConclusions
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQOneBlockCatalogues

/-! Intermediate restrictions and block induction under a common root correspondence. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.CoherentIntermediateBlocks

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open SporadicFi24P3Definition44NamedCarrierQOneIntermediateBlocks
open SporadicFi24P3Definition44NamedCarrierIntermediateBlockConclusions

universe u
variable {p : ℕ} {k K A : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group A] [Fintype A]
local instance subgroupFintype (J : Subgroup A) : Fintype J := Fintype.ofFinite J
local instance intersectionFintype (D J : Subgroup A) :
    Fintype (localIntersection D J) := Fintype.ofFinite _
variable (D : Subgroup A)
variable (globalCharacter : PrimeRegularClassFunction K A p)
variable (localCharacter : PrimeRegularClassFunction K D p)

/-- Restrictions and block induction with roots taken from one ambient
correspondence. The ambient global and local correspondences also agree. -/
def CoherentAllIntermediateBlocks
    (rA : PrimeRegularRootEmbedding p k K A)
    (rD : PrimeRegularRootEmbedding p k K D) (B : Subgroup A) : Prop :=
  rA.AgreesOnRoots rD ∧
  ∀ (J : Subgroup A), B ≤ J →
    ∃ (rJ : PrimeRegularRootEmbedding p k K J) (phiJ : IBr rJ)
      (rH : PrimeRegularRootEmbedding p k K (localIntersection D J)) (phiH : IBr rH)
      (BJ BH : Type u)
      (dataJ : AmbientBlockCatalogueData (k := k) (G := J) (Block := BJ))
      (dataH : AmbientBlockCatalogueData (k := k) (G := localIntersection D J) (Block := BH)),
      rA.AgreesOnRoots rJ ∧ rA.AgreesOnRoots rH ∧
      IntermediateBlockOutput D globalCharacter localCharacter J rJ phiJ rH phiH dataJ dataH

theorem CoherentAllIntermediateBlocks.forget
    {rA : PrimeRegularRootEmbedding p k K A}
    {rD : PrimeRegularRootEmbedding p k K D} {B : Subgroup A}
    (h : CoherentAllIntermediateBlocks D globalCharacter localCharacter rA rD B) :
    AllIntermediateBlocks (k := k) D globalCharacter localCharacter B := by
  intro J hJ
  obtain ⟨rJ, phiJ, rH, phiH, BJ, BH, dataJ, dataH, _, _, hdata⟩ := h.2 J hJ
  exact ⟨rJ, phiJ, rH, phiH, BJ, BH, dataJ, dataH, hdata⟩

end ModularRep.PaperProofs.CoherentIntermediateBlocks

/-
Part of the Lean formalisation accompanying Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
The results use the explicit assumptions described in the formalisation report.
-/
