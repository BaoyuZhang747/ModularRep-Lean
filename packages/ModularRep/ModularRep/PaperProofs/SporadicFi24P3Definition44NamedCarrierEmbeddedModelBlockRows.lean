import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFactorOneExtension
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualCyclicBrauerExtensions
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierEmbeddedChoiceInputs

/-! Retain the initial global and fixed local model characters, then select
the global extension with every intermediate block law and its explicit twist. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierEmbeddedModelBlockRows

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.NavarroCoveringBrauerExtension ModularRep.NavarroBrauerRestrictionCovering
open Representation.Extension
open SporadicFi24P3Definition44NamedCarrierAssociatedProjectiveModel
open SporadicFi24P3Definition44NamedCarrierFactorOneExtension
open SporadicFi24P3Definition44NamedCarrierActualCyclicBrauerExtensions
open SporadicFi24P3Definition44NamedCarrierQOneIntermediateBlocks
open SporadicFi24P3Definition44NamedCarrierQOneBlockCatalogues (UnselectedCatalogue)
open SporadicFi24P3Definition44NamedCarrierIntermediateBlockConclusions
open SporadicFi24P3Definition44NamedCarrierEmbeddedChoiceInputs

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

def EmbeddedModelPairBlocks : Prop :=
  ∃ (rA : PrimeRegularRootEmbedding p k K A) (rD : PrimeRegularRootEmbedding p k K D),
    (∀ zeta : rootsOfUnity (primeRegularExponent p B) k,
      rB.lift (((zeta : kˣ) : k)) = rA.lift (((zeta : kˣ) : k))) ∧
    (∀ zeta : rootsOfUnity (primeRegularExponent p (B.comap D.subtype)) k,
      rM.lift (((zeta : kˣ) : k)) = rD.lift (((zeta : kˣ) : k))) ∧
    ∃ (initialGlobal : BrauerCharacterExtensionWitness rA rB phiB)
      (fixedLocal : BrauerCharacterExtensionWitness rD rM phiM),
      initialGlobal.val.val = (representationOfFactorOne MG hMG).brauerCharacterOfRootEmbedding rA ∧
      fixedLocal.val.val = (representationOfFactorOne ML hML).brauerCharacterOfRootEmbedding rD ∧
      ∃ (selectedGlobal : BrauerCharacterExtensionWitness rA rB phiB) (lambda : (A ⧸ B) →* Kˣ),
        (∀ x : PrimeRegularElement (G := A) p,
          selectedGlobal.val.val x =
            (lambda (QuotientGroup.mk' B x.val) : K) * initialGlobal.val.val x) ∧
        AllIntermediateBlocks (k := k) D selectedGlobal.val.val fixedLocal.val.val B

theorem embedded_model_pair_blocks
    (S9295 : Navarro9295BrauerRestrictionCoveringPrinciple p k K)
    (S9495 : Navarro9495BrauerCoveringPrinciple p k K)
    (S820 : Navarro820CyclicBrauerTwistPrinciple p k K)
    (hirrG : Representation.IsIrreducible rhoG)
    (haffordsG : phiB.val = rhoG.brauerCharacterOfRootEmbedding rB)
    (hirrL : Representation.IsIrreducible rhoL)
    (haffordsL : phiM.val = rhoL.brauerCharacterOfRootEmbedding rM)
    (seed : Nonempty (PrimeRegularRootEmbedding p k K A))
    (fieldSource : SpathCoefficientField p k rB.prime)
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
  let : Fact p.Prime := ⟨rB.prime⟩
  obtain ⟨rA, hrootsG, initialGlobal, hInitial⟩ :=
    exists_brauer_extension_of_factor_one MG hMG hirrG rB phiB haffordsG.symm seed
  obtain ⟨rD, hrootsL, fixedLocal, hLocal⟩ :=
    exists_brauer_extension_of_factor_one ML hML hirrL rM phiM haffordsL.symm ⟨seedOnSubgroup rA D⟩
  obtain ⟨selectedGlobal, lambda, htwist, hall⟩ :=
    exists_selected_global_of_proper_base_inputs
      S9295 S9495 S820 B D rA rB rD rM hrootsG hrootsL fieldSource hcyclic
      phiB phiM initialGlobal fixedLocal dataB dataM cases Q interval ambient localInput hbase
  exact ⟨rA, rD, hrootsG, hrootsL, initialGlobal, fixedLocal,
    hInitial, hLocal, selectedGlobal, lambda, htwist, hall⟩

def EveryEmbeddedModelPairBlocks : Prop :=
  ∀ (WG : FDRep k B) (WL : FDRep k (B.comap D.subtype))
    (MG : AssociatedProjectiveModel B WG.ρ)
    (ML : AssociatedProjectiveModel (B.comap D.subtype) WL.ρ)
    (hMG : MG.factorSet = ScalarFactorSet.trivial) (hML : ML.factorSet = ScalarFactorSet.trivial),
    Representation.IsIrreducible WG.ρ →
    phiB.val = Representation.brauerCharacterOfRootEmbedding WG.ρ rB →
    Representation.IsIrreducible WL.ρ →
    phiM.val = Representation.brauerCharacterOfRootEmbedding WL.ρ rM →
    EmbeddedModelPairBlocks B D rB rM phiB phiM WG.ρ WL.ρ MG ML hMG hML

theorem every_embedded_model_pair_blocks_apply
    (h : EveryEmbeddedModelPairBlocks B D rB rM phiB phiM)
    (hirrG : Representation.IsIrreducible rhoG)
    (haffordsG : phiB.val = rhoG.brauerCharacterOfRootEmbedding rB)
    (hirrL : Representation.IsIrreducible rhoL)
    (haffordsL : phiM.val = rhoL.brauerCharacterOfRootEmbedding rM) :
    EmbeddedModelPairBlocks B D rB rM phiB phiM rhoG rhoL MG ML hMG hML :=
  h (FDRep.of rhoG) (FDRep.of rhoL) MG ML hMG hML hirrG haffordsG hirrL haffordsL

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierEmbeddedModelBlockRows


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
