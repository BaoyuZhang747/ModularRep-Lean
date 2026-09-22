import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalBaseBlockData
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualIntermediateAssembly
import ModularRep.CyclicBrauerTopBlockFromBaseInduction

/-! Internal cyclic choice from the actual quotient-base induction.
The two individual extensions, specified catalogues and lower principles
determine a global extension with the required top block. No block census
or selected compatible-extension source is used. -/

noncomputable section
open scoped MonoidAlgebra
set_option maxHeartbeats 2000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualCyclicBlockChoice

open ModularRep ModularRep.FDRepSimpleClassKZero
open ModularRep.NavarroBrauerRestrictionCovering
open ModularRep.NavarroCoveringBrauerExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualRadicalPacket
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalBaseBlockData
open Representation.Extension

universe u

local instance subgroupFintype {A : Type u} [Group A] [Finite A] (H : Subgroup A) :
    Fintype H := Fintype.ofFinite H

local instance problemPrime (P : Definition35Problem.{u}) : Fact P.p.Prime := ⟨P.iota.prime⟩

private theorem domCongr_roundtrip
    {k G H : Type u} [Field k] [Group G] [Group H]
    (e : G ≃* H) (f : k[H]) :
    MonoidAlgebra.domCongr k k e (MonoidAlgebra.domCongr k k e.symm f) = f := by
  ext x
  simp only [MonoidAlgebra.coeff_domCongr, MulEquiv.symm_symm, MulEquiv.apply_symm_apply]

theorem exists_global_with_induced_block_of_quotient_base
    (P : Definition35Problem.{u}) {G A : Type u}
    [Group G] [Fintype G] [Group A] [Fintype A]
    (N : Subgroup G) (B D : Subgroup A) [B.Normal]
    (eG : G ≃* B) (eM : N ≃* B.comap D.subtype)
    (square : eG.toMonoidHom.comp N.subtype =
      (localIntersection D B).subtype.comp
        (eM.trans (subgroupIntersectionEquiv D B)).toMonoidHom)
    (rG : PrimeRegularRootEmbedding P.p P.k P.K G)
    (rN : PrimeRegularRootEmbedding P.p P.k P.K N)
    (rA : PrimeRegularRootEmbedding P.p P.k P.K A)
    (rD : PrimeRegularRootEmbedding P.p P.k P.K D)
    (injG : IrreducibleBrauerCharacterInjectivity rG)
    (injN : IrreducibleBrauerCharacterInjectivity rN)
    {BG BN BA BD : Type u}
    [Fintype BG] [Fintype BN] [Fintype BA] [Fintype BD]
    {bG : BG → P.k[G]} {bN : BN → P.k[N]}
    {bA : BA → P.k[A]} {bD : BD → P.k[D]}
    (DG : BlockIdempotentDecomposition bG) (DN : BlockIdempotentDecomposition bN)
    (DA : BlockIdempotentDecomposition bA) (DD : BlockIdempotentDecomposition bD)
    (CG : BlockCentralCharacterCatalogue DG) (CN : BlockCentralCharacterCatalogue DN)
    (CA : BlockCentralCharacterCatalogue DA) (CD : BlockCentralCharacterCatalogue DD)
    (phiG : IBr rG) (phiN : IBr rN)
    (initialGlobal : BrauerCharacterExtensionWitness rA (rG.alongMulEquiv eG)
      (IrreducibleBrauerCharacter.alongMulEquiv rG eG phiG))
    (fixedLocal : BrauerCharacterExtensionWitness rD (rN.alongMulEquiv eM)
      (IrreducibleBrauerCharacter.alongMulEquiv rN eM phiN))
    (globalAgreement : ∀ zeta : rootsOfUnity (primeRegularExponent P.p B) P.k,
      (rG.alongMulEquiv eG).lift (((zeta : P.kˣ) : P.k)) = rA.lift (((zeta : P.kˣ) : P.k)))
    (localAgreement : ∀ zeta : rootsOfUnity (primeRegularExponent P.p (B.comap D.subtype)) P.k,
      (rN.alongMulEquiv eM).lift (((zeta : P.kˣ) : P.k)) = rD.lift (((zeta : P.kˣ) : P.k)))
    (fieldSource : SpathCoefficientField P.p P.k P.iota.prime)
    (hcyclic : IsCyclic (A ⧸ B))
    (Q : Subgroup A) (interval : CentralBrauerInterval (p := P.p) Q D)
    (S414 : Navarro414IntervalCentralCharacterSource interval DD CD)
    (S9295 : Navarro9295BrauerRestrictionCoveringPrinciple P.p P.k P.K)
    (S9495 : Navarro9495BrauerCoveringPrinciple P.p P.k P.K)
    (S820 : Navarro820CyclicBrauerTwistPrinciple P.p P.k P.K)
    (hInd : BlockInducesTo N CN CG
      (irreducibleBrauerCharacterBlock rN injN DN phiN)
      (irreducibleBrauerCharacterBlock rG injG DG phiG)) :
    ∃ chosenGlobal : BrauerCharacterExtensionWitness rA (rG.alongMulEquiv eG)
        (IrreducibleBrauerCharacter.alongMulEquiv rG eG phiG),
      BlockInducesTo D CD CA
        (irreducibleBrauerCharacterBlock rD (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _)
          DD fixedLocal.1)
        (irreducibleBrauerCharacterBlock rA (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _)
          DA chosenGlobal.1) := by
  let rB := rG.alongMulEquiv eG
  let phiB := IrreducibleBrauerCharacter.alongMulEquiv rG eG phiG
  let rM := rN.alongMulEquiv eM
  let phiM := IrreducibleBrauerCharacter.alongMulEquiv rN eM phiN
  let initialBase := baseBlockDataOfExtensions
    P N B D eG eM square rG rN rA rD injG injN
    DG DN CG CN phiG phiN initialGlobal fixedLocal fieldSource hInd
  let d := subgroupIntersectionEquiv D B
  let intersectionBlocks := initialBase.localBlocks.alongMulEquiv d.symm
  let intersectionCatalogue := initialBase.localCentralCharacters.alongMulEquiv d.symm
  let injM := irreducibleBrauerCharacterInjectivity_of_rootEmbedding rM
  have hblock : irreducibleBrauerCharacterBlock rM injM intersectionBlocks phiM =
      irreducibleBrauerCharacterBlock initialBase.localRoot initialBase.localBrauerInjective
        initialBase.localBlocks initialBase.localBrauer := by
    apply irreducibleBrauerCharacterBlock_alongMulEquiv_of_lift_eq
      initialBase.localRoot initialBase.localBrauerInjective rM injM d.symm
      initialBase.localBlocks initialBase.localBrauer phiM
    · funext z
      change (rN.alongMulEquiv eM).lift z = (rN.alongMulEquiv (eM.trans d)).lift z
      simp only [PrimeRegularRootEmbedding.alongMulEquiv_lift]
    · apply PrimeRegularClassFunction.ext
      intro x
      rfl
  have hcatalogue (b : initialBase.LocalBlock) :
      (intersectionCatalogue.alongMulEquiv d).centralCharacter b =
        initialBase.localCentralCharacters.centralCharacter b := by
    apply centralCharacterAlongMulEquiv_eq_of_blockIdempotent
      d intersectionCatalogue initialBase.localCentralCharacters
    apply Subtype.ext
    exact domCongr_roundtrip d (show P.k[D.comap B.subtype] from initialBase.localBlockIdempotent b)
  have hbase : BlockInducesTo (D.comap B.subtype)
      (intersectionCatalogue.alongMulEquiv d) initialBase.globalCentralCharacters
      (irreducibleBrauerCharacterBlock rM injM intersectionBlocks phiM)
      (irreducibleBrauerCharacterBlock rB initialBase.globalBrauerInjective
        initialBase.globalBlocks phiB) := by
    unfold BlockInducesTo
    rw [hblock, hcatalogue]
    exact initialBase.inductionEquality
  exact ModularRep.CyclicBrauerTopBlockFromBaseInduction.exists_global_extension_with_induced_block
    S9295 S9495 S820 B D rA rB rD rM globalAgreement localAgreement fieldSource hcyclic
    DA initialBase.globalBlocks DD intersectionBlocks
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) initialBase.globalBrauerInjective
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) injM
    CA initialBase.globalCentralCharacters CD intersectionCatalogue
    phiB phiM initialGlobal fixedLocal Q interval S414 hbase

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualCyclicBlockChoice


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
