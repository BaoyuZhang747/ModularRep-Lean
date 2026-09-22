import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierEmbeddedIntermediateBlocks
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierExtensionQuotientTwist
import ModularRep.CyclicBrauerTopBlockFromBaseInduction

/-! Select the global extension over the original base character, keep the
local extension fixed, and derive every intermediate block relation. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierEmbeddedCyclicChoice

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.NavarroCoveringBrauerExtension
open ModularRep.NavarroBrauerRestrictionCovering
open Representation.Extension
open SporadicFi24P3Definition44NamedCarrierQOneIntermediateBlocks
open SporadicFi24P3Definition44NamedCarrierIntermediateBlockConclusions
open SporadicFi24P3Definition44NamedCarrierEmbeddedIntermediateBlocks
open SporadicFi24P3Definition44NamedCarrierExtensionQuotientTwist

universe u
variable {p : ℕ} {k K A : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group A] [Fintype A] [Fact p.Prime]
local instance subgroupFintype (B : Subgroup A) : Fintype B := Fintype.ofFinite _
local instance comapFintype (B D : Subgroup A) : Fintype (B.comap D.subtype) := Fintype.ofFinite _

theorem exists_selected_global_with_all_intermediate_blocks
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
    {BA BB BD BM : Type u}
    (dataA : AmbientBlockCatalogueData (k := k) (G := A) (Block := BA))
    (dataB : AmbientBlockCatalogueData (k := k) (G := B) (Block := BB))
    (dataD : AmbientBlockCatalogueData (k := k) (G := D) (Block := BD))
    (dataM : AmbientBlockCatalogueData (k := k) (G := B.comap D.subtype) (Block := BM))
    (cases : ∀ J : Subgroup A, B ≤ J → J = B ∨ J = ⊤)
    (Q : Subgroup A) (interval : CentralBrauerInterval (p := p) Q D)
    (S414 : letI : Fintype BD := dataD.fintypeBlock
      Navarro414IntervalCentralCharacterSource interval dataD.blocks dataD.catalogue)
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
  let : Fintype BA := dataA.fintypeBlock
  let : Fintype BB := dataB.fintypeBlock
  let : Fintype BD := dataD.fintypeBlock
  let : Fintype BM := dataM.fintypeBlock
  obtain ⟨selectedGlobal, htop⟩ :=
    CyclicBrauerTopBlockFromBaseInduction.exists_global_extension_with_induced_block
      S9295 S9495 S820 B D rA rB rD rM globalRootAgreement localRootAgreement
      fieldSource hcyclic dataA.blocks dataB.blocks dataD.blocks dataM.blocks
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _)
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _)
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _)
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _)
      dataA.catalogue dataB.catalogue dataD.catalogue dataM.catalogue
      phiB phiM initialGlobal fixedLocal Q interval S414 hbase
  obtain ⟨lambda, htwist⟩ := quotient_twist_between_extensions
    S820 B rA rB globalRootAgreement hcyclic phiB initialGlobal selectedGlobal
  exact ⟨selectedGlobal, lambda, htwist,
    all_intermediate_blocks_of_base_top B D rA rB rD rM phiB phiM
      selectedGlobal fixedLocal dataA dataB dataD dataM cases hbase htop⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierEmbeddedCyclicChoice


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
