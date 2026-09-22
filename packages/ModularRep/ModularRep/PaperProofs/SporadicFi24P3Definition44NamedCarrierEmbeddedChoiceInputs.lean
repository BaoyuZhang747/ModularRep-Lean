import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierEmbeddedCyclicChoice

/-! Only a proper base needs new top catalogues and an interval source.
The base-equals-top case follows directly from the specified base induction. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierEmbeddedChoiceInputs

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.NavarroCoveringBrauerExtension
open ModularRep.NavarroBrauerRestrictionCovering
open Representation.Extension
open SporadicFi24P3Definition44NamedCarrierQOneIntermediateBlocks
open SporadicFi24P3Definition44NamedCarrierIntermediateBlockConclusions
open SporadicFi24P3Definition44NamedCarrierEmbeddedIntermediateBlocks
open SporadicFi24P3Definition44NamedCarrierExtensionQuotientTwist
open SporadicFi24P3Definition44NamedCarrierEmbeddedCyclicChoice
open SporadicFi24P3Definition44NamedCarrierQOneBlockCatalogues (catalogueAlong UnselectedCatalogue)

universe u
variable {p : ℕ} {k K A : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group A] [Fintype A] [Fact p.Prime]
local instance subgroupFintype (B : Subgroup A) : Fintype B := Fintype.ofFinite _
local instance comapFintype (B D : Subgroup A) : Fintype (B.comap D.subtype) := Fintype.ofFinite _

def UnselectedIntervalCatalogue
    (Q D : Subgroup A) (interval : CentralBrauerInterval (p := p) Q D) : Prop :=
  ∃ BD : Type u, ∃ dataD : AmbientBlockCatalogueData (k := k) (G := D) (Block := BD),
    letI : Fintype BD := dataD.fintypeBlock
    Navarro414IntervalCentralCharacterSource interval dataD.blocks dataD.catalogue

theorem exists_selected_global_of_proper_base_inputs
    (S9295 : Navarro9295BrauerRestrictionCoveringPrinciple p k K)
    (S9495 : Navarro9495BrauerCoveringPrinciple p k K)
    (S820 : Navarro820CyclicBrauerTwistPrinciple p k K)
    (B : Subgroup A) [B.Normal] (D : Subgroup A)
    (rA : PrimeRegularRootEmbedding p k K A)
    (rB : PrimeRegularRootEmbedding p k K B)
    (rD : PrimeRegularRootEmbedding p k K D)
    (rM : PrimeRegularRootEmbedding p k K (B.comap D.subtype))
    (globalRootAgreement : ∀ zeta : rootsOfUnity (primeRegularExponent p B) k,
      rB.lift (((zeta : kˣ) : k)) = rA.lift (((zeta : kˣ) : k)))
    (localRootAgreement : ∀ zeta : rootsOfUnity (primeRegularExponent p (B.comap D.subtype)) k,
      rM.lift (((zeta : kˣ) : k)) = rD.lift (((zeta : kˣ) : k)))
    (fieldSource : SpathCoefficientField p k rA.prime)
    (hcyclic : IsCyclic (A ⧸ B))
    (phiB : IBr rB) (phiM : IBr rM)
    (initialGlobal : BrauerCharacterExtensionWitness rA rB phiB)
    (fixedLocal : BrauerCharacterExtensionWitness rD rM phiM)
    {BB BM : Type u}
    (dataB : AmbientBlockCatalogueData (k := k) (G := B) (Block := BB))
    (dataM : AmbientBlockCatalogueData (k := k) (G := B.comap D.subtype) (Block := BM))
    (cases : ∀ J : Subgroup A, B ≤ J → J = B ∨ J = ⊤)
    (Q : Subgroup A) (interval : CentralBrauerInterval (p := p) Q D)
    (ambient : B ≠ ⊤ → UnselectedCatalogue (k := k) (A := A))
    (localInput : B ≠ ⊤ → UnselectedIntervalCatalogue (k := k) Q D interval)
    (hbase : letI : Fintype BB := dataB.fintypeBlock
      letI : Fintype BM := dataM.fintypeBlock
      BlockInducesTo (localIntersection D B)
        (dataM.catalogue.alongMulEquiv (subgroupIntersectionEquiv D B)) dataB.catalogue
        (irreducibleBrauerCharacterBlock rM
          (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) dataM.blocks phiM)
        (irreducibleBrauerCharacterBlock rB
          (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) dataB.blocks phiB)) :
    ∃ selectedGlobal : BrauerCharacterExtensionWitness rA rB phiB,
      ∃ lambda : (A ⧸ B) →* Kˣ,
        (∀ x : PrimeRegularElement (G := A) p,
          selectedGlobal.val.val x =
            (lambda (QuotientGroup.mk' B x.val) : K) * initialGlobal.val.val x) ∧
        AllIntermediateBlocks (k := k) D selectedGlobal.val.val fixedLocal.val.val B := by
  classical
  let : Fintype BB := dataB.fintypeBlock
  let : Fintype BM := dataM.fintypeBlock
  by_cases hB : B = ⊤
  · refine ⟨initialGlobal, 1, ?_, ?_⟩
    · intro x
      simp only [MonoidHom.one_apply, Units.val_one, one_mul]
    · intro J hJ
      have hJB : J = B := le_antisymm (hB ▸ le_top) hJ
      subst J
      let d := subgroupIntersectionEquiv D B
      refine ⟨rB, phiB, rM.alongMulEquiv d,
        IrreducibleBrauerCharacter.alongMulEquiv rM d phiM,
        BB, BM, dataB, catalogueAlong dataM d, ?_⟩
      refine ⟨initialGlobal.property, ?_, ?_⟩
      · apply PrimeRegularClassFunction.ext
        intro x
        exact congrArg
          (fun chi : PrimeRegularClassFunction K (B.comap D.subtype) p =>
            chi (PrimeRegularElement.map d.symm.toMonoidHom x)) fixedLocal.property
      · change BlockInducesTo (localIntersection D B)
          (dataM.catalogue.alongMulEquiv d) dataB.catalogue
          (irreducibleBrauerCharacterBlock (rM.alongMulEquiv d)
            (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _)
            (dataM.blocks.alongMulEquiv d) (IrreducibleBrauerCharacter.alongMulEquiv rM d phiM))
          (irreducibleBrauerCharacterBlock rB
            (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) dataB.blocks phiB)
        rw [irreducibleBrauerCharacterBlock_alongMulEquiv rM
          (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) d
          (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) dataM.blocks phiM]
        exact hbase
  · obtain ⟨BA, ⟨dataA⟩⟩ := ambient hB
    obtain ⟨BD, dataD, S414⟩ := localInput hB
    exact exists_selected_global_with_all_intermediate_blocks
      S9295 S9495 S820 B D rA rB rD rM globalRootAgreement localRootAgreement
      fieldSource hcyclic phiB phiM initialGlobal fixedLocal
      dataA dataB dataD dataM cases Q interval S414 hbase

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierEmbeddedChoiceInputs


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
