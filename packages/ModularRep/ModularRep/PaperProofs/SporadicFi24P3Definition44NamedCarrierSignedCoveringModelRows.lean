import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierEmbeddedModelBlockRows
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSignedModelTopBlockChoice

/-! Retain the original pair of factor-one models. Their literal local
restriction proves covering, and the base/top argument supplies the same
complete intermediate-block output using the index-two sign choice without a covering-extension source. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSignedCoveringModelRows

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.NavarroCoveringBrauerExtension
open Representation.Extension
open SporadicFi24P3Definition44NamedCarrierAssociatedProjectiveModel
open SporadicFi24P3Definition44NamedCarrierFactorOneExtension
open SporadicFi24P3Definition44NamedCarrierActualCyclicBrauerExtensions
open SporadicFi24P3Definition44NamedCarrierQOneIntermediateBlocks
open SporadicFi24P3Definition44NamedCarrierQOneBlockCatalogues (catalogueAlong UnselectedCatalogue)
open SporadicFi24P3Definition44NamedCarrierIntermediateBlockConclusions
open SporadicFi24P3Definition44NamedCarrierEmbeddedChoiceInputs
open SporadicFi24P3Definition44NamedCarrierEmbeddedModelBlockRows
open SporadicFi24P3Definition44NamedCarrierEmbeddedIntermediateBlocks
open SporadicFi24P3Definition44NamedCarrierExtensionQuotientTwist
open SporadicFi24P3Definition44NamedCarrierSignedModelTopBlockChoice
open SporadicFi24P3Definition44NamedCarrierQuotientSignAlgebra

universe u
variable {p : ℕ} {k K A : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group A] [Fintype A]
local instance subgroupFintype (B : Subgroup A) : Fintype B := Fintype.ofFinite _
local instance comapFintype (B D : Subgroup A) : Fintype (B.comap D.subtype) := Fintype.ofFinite _
variable (B : Subgroup A) [B.Normal] (D : Subgroup A)
variable (rB : PrimeRegularRootEmbedding p k K B)
variable (rM : PrimeRegularRootEmbedding p k K (B.comap D.subtype))
variable (phiB : IBr rB) (phiM : IBr rM)
variable {UG UL : Type u}
variable [AddCommGroup UG] [Module k UG] [FiniteDimensional k UG]
variable [AddCommGroup UL] [Module k UL] [FiniteDimensional k UL]
variable (rhoG : Representation k B UG) (rhoL : Representation k (B.comap D.subtype) UL)
variable (MG : AssociatedProjectiveModel B rhoG)
variable (ML : AssociatedProjectiveModel (B.comap D.subtype) rhoL)
variable (hMG : MG.factorSet = ScalarFactorSet.trivial) (hML : ML.factorSet = ScalarFactorSet.trivial)

theorem embedded_model_pair_blocks_of_index_two
    (h2 : (2 : k) ≠ 0)
    (hIndex : Nat.card (A ⧸ B) ≤ 2)
    (S820 : Navarro820CyclicBrauerTwistPrinciple p k K)
    (hirrG : Representation.IsIrreducible rhoG)
    (haffordsG : phiB.val = rhoG.brauerCharacterOfRootEmbedding rB)
    (hirrL : Representation.IsIrreducible rhoL)
    (haffordsL : phiM.val = rhoL.brauerCharacterOfRootEmbedding rM)
    (seed : Nonempty (PrimeRegularRootEmbedding p k K A))
    (hcyclic : IsCyclic (A ⧸ B))
    {BB BM : Type u}
    (dataB : AmbientBlockCatalogueData (k := k) (G := B) (Block := BB))
    (dataM : AmbientBlockCatalogueData (k := k) (G := B.comap D.subtype) (Block := BM))
    (cases : ∀ J : Subgroup A, B ≤ J → J = B ∨ J = ⊤)
    (Q : Subgroup A) (interval : CentralBrauerInterval (p := p) Q D)
    (ambient : B ≠ ⊤ → UnselectedCatalogue (k := k) (A := A))
    (localInput : letI : Fact p.Prime := ⟨rB.prime⟩
      B ≠ ⊤ → UnselectedIntervalCatalogue (k := k) Q D interval)
    (hbase : letI : Fintype BB := dataB.fintypeBlock
      letI : Fintype BM := dataM.fintypeBlock
      BlockInducesTo (localIntersection D B)
        (dataM.catalogue.alongMulEquiv (subgroupIntersectionEquiv D B)) dataB.catalogue
        (irreducibleBrauerCharacterBlock rM
          (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) dataM.blocks phiM)
        (irreducibleBrauerCharacterBlock rB
          (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) dataB.blocks phiB)) :
    EmbeddedModelPairBlocks B D rB rM phiB phiM rhoG rhoL MG ML hMG hML := by
  classical
  let : Fact p.Prime := ⟨rB.prime⟩
  let : Fintype BB := dataB.fintypeBlock
  let : Fintype BM := dataM.fintypeBlock
  obtain ⟨rA, hrootsG, initialGlobal, hInitial⟩ :=
    exists_brauer_extension_of_factor_one MG hMG hirrG rB phiB haffordsG.symm seed
  obtain ⟨rD, hrootsL, fixedLocal, hLocal⟩ :=
    exists_brauer_extension_of_factor_one ML hML hirrL rM phiM haffordsL.symm ⟨seedOnSubgroup rA D⟩
  refine ⟨rA, rD, hrootsG, hrootsL, initialGlobal, fixedLocal, hInitial, hLocal, ?_⟩
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
    let : Fintype BA := dataA.fintypeBlock
    let : Fintype BD := dataD.fintypeBlock
    let sigma := representationOfFactorOne ML hML
    let : Representation.IsIrreducible rhoL := hirrL
    let : Representation.IsIrreducible sigma :=
      (extensionOfFactorOne ML hML).representation_isIrreducible hirrL
    have hres : sigma.pullback (B.comap D.subtype).subtype = rhoL := by
      ext m v
      change ML.operator (m : D) v = rhoL m v
      rw [ML.restriction]
    let sigmaG := representationOfFactorOne MG hMG
    let : Representation.IsIrreducible rhoG := hirrG
    let : Representation.IsIrreducible sigmaG :=
      (extensionOfFactorOne MG hMG).representation_isIrreducible hirrG
    have hresG : sigmaG.pullback B.subtype = rhoG := by
      ext b v
      change MG.operator (b : A) v = rhoG b v
      rw [MG.restriction]
    obtain ⟨selectedGlobal, htop⟩ :=
      exists_global_extension_with_induced_block_of_index_two
        h2 B D rA rB rD rM hrootsG
        (index_eq_two_of_quotient_card_le_two B hIndex hB)
        dataA.blocks dataB.blocks dataD.blocks dataM.blocks
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _)
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _)
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _)
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _)
        dataA.catalogue dataB.catalogue dataD.catalogue dataM.catalogue
        phiB phiM initialGlobal fixedLocal sigmaG rhoG hresG hInitial haffordsG
        sigma rhoL hres hLocal haffordsL
        Q interval S414 hbase
    obtain ⟨lambda, htwist⟩ := quotient_twist_between_extensions
      S820 B rA rB hrootsG hcyclic phiB initialGlobal selectedGlobal
    exact ⟨selectedGlobal, lambda, htwist,
      all_intermediate_blocks_of_base_top B D rA rB rD rM phiB phiM
        selectedGlobal fixedLocal dataA dataB dataD dataM cases hbase htop⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSignedCoveringModelRows


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
