import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalAmbientBlockData
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalQuotientData
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorIndividualExtensions
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualCyclicBlockChoice
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalExtensionRestrictions

/-! The actual original-cover packet for a nontrivial radical in the
trivial central sector. Individual extensions, base induction, cyclic top
choice, all intermediate records and original restrictions are constructed. -/

noncomputable section
set_option maxHeartbeats 4000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorNontrivialPacket

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.NavarroBrauerRestrictionCovering ModularRep.NavarroCoveringBrauerExtension
open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalAmbient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCoverGroupFacts
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalActualPacket
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalLocalNormalizer
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalAmbientBlockData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalQuotientData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorActualAmbient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorIndividualExtensions
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualCyclicBlockChoice
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalExtensionRestrictions
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalBaseBlockData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalTopBlockData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualIntermediateAssembly
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnQuotientBlockInduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnNormalizerBrauer
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnCentralQuotient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientRoot
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction

universe u

local instance problemPrime (P : Definition35Problem.{u}) : Fact P.p.Prime := ⟨P.iota.prime⟩
local instance quotientFintype (P : Definition35Problem.{u}) (psi : Definition35Brauer P) :
    Fintype (CentralCharacterQuotient P psi) := Fintype.ofFinite _

theorem exists_trivialSectorPacket_nontrivial
    (P : Definition35Problem.{u}) (psi : Definition35Brauer P)
    (V : CharacterWeight P.p P.K P.H) (hV : V.subgroup ≠ ⊥)
    {S : Type u} [Group S] (q : P.H →* S) (hq : IsUniversalCentralExtension q)
    (hs : IsSimpleGroup S) (hna : ¬ IsMulCommutative S)
    (hcenter : ¬ P.p ∣ Nat.card (Subgroup.center P.H))
    (hglobal : ∀ z : PrimeRegularElement (G := Subgroup.center P.H) P.p,
      psi.1.1 (PrimeRegularElement.map (Subgroup.center P.H).subtype z) =
        psi.1.1 ⟨1, isPrimeRegular_one⟩)
    (source : CanonicalRawReduction P.iota V)
    (compatibility : CanonicalLocalBlockCompatibility P.iota P.blockSource.operations)
    (hrawBlock :
      letI := P.blockSource.operations.ambientBlockData.fintypeBlock
      P.blockSource.operations.rawWeightBlock V =
        irreducibleBrauerCharacterBlock P.iota P.irreducibleBrauerInjective
          P.blockSource.operations.ambientBlockData.blocks psi.1)
    (quotientData : OriginalQuotientData P psi V hcenter)
    (ambientData : OriginalAmbientBlockData P psi V
      (trivialSectorOriginalAmbient P psi q hq hs hna hcenter hglobal)
      (actualLocalNormalizerData P psi V q hq hs hna hcenter hglobal))
    (Omega : IBr P.iota ≃ ConjugacyClass (p := P.p) (K := P.K) (G := P.H))
    (hOmega : ∀ (a : (MulAut P.H)ᵐᵒᵖ) (chi : IBr P.iota), Omega (a • chi) = a • Omega chi)
    (hclass : (Quotient.mk'' (Quotient.mk'' V) :
      ConjugacyClass (p := P.p) (K := P.K) (G := P.H)) = Omega psi.1)
    (hOuter : Nat.card (LiteralOuterQuotient (CentralCharacterQuotient P psi)) = 2)
    (extensionPrinciple : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} P.p P.k)
    (seed : PrimeRegularRootEmbedding P.p P.k P.K
      (trivialSectorOriginalAmbient P psi q hq hs hna hcenter hglobal).A)
    (fieldSource : SpathCoefficientField P.p P.k P.iota.prime)
    (S9295 : Navarro9295BrauerRestrictionCoveringPrinciple P.p P.k P.K)
    (S9495 : Navarro9495BrauerCoveringPrinciple P.p P.k P.K)
    (S820 : Navarro820CyclicBrauerTwistPrinciple P.p P.k P.K) :
    Nonempty (OriginalActualWeightPacket P psi V) := by
  let : Group.IsPerfect P.H := ⟨perfect_of_universalCentralExtension q hq⟩
  let B := trivialSectorOriginalAmbient P psi q hq hs hna hcenter hglobal
  let C := actualLocalNormalizerData P psi V q hq hs hna hcenter hglobal
  let hprimeTo := centralKernel_primeTo P psi hcenter
  let Nbar := Subgroup.normalizer (V.subgroup.map (centralCharacterQuotientMap P psi) :
    Set (CentralCharacterQuotient P psi))
  let rG := quotientRoot P.iota (centralCharacterKernel P psi)
  let rN := ownNormalizerRoot P psi V source hprimeTo quotientData.normalizers
  let phiG := ownQuotientBrauer P psi
  let phiN := ownNormalizerBrauer P psi V source compatibility hrawBlock hprimeTo quotientData.normalizers
  let injG := irreducibleBrauerCharacterInjectivity_of_rootEmbedding rG
  let injN := irreducibleBrauerCharacterInjectivity_of_rootEmbedding rN
  obtain ⟨rA, rD, globalAgreement, localAgreement, ⟨initialGlobal⟩, ⟨fixedLocal⟩⟩ :=
    exists_actualIndividualExtensions P psi V q hq hs hna hcenter hglobal hprimeTo
      quotientData.normalizers source compatibility hrawBlock Omega hOmega hclass
      hOuter extensionPrinciple seed
  have square := baseSquare_of_localEmbedding Nbar B.base C.D B.baseEquiv C.eM
    (fun n => DFunLike.congr_fun C.eM_natural n)
  have hInd := own_quotient_block_induction P psi V source compatibility hrawBlock hprimeTo
    quotientData.normalizers quotientData.globalBlocks quotientData.localBlocks
    quotientData.globalCatalogue quotientData.localCatalogue quotientData.intervalLaw
    quotientData.globalImageLaw quotientData.localImageLaw
  have hcyclic : IsCyclic (B.A ⧸ B.base) := actual_quotient_isCyclic rG phiG hOuter
  have hcard : Nat.card (B.A ⧸ B.base) ≤ 2 := actual_quotient_card_le_two rG phiG hOuter
  obtain ⟨chosenGlobal, htop⟩ := exists_global_with_induced_block_of_quotient_base
    P Nbar B.base C.D B.baseEquiv C.eM square rG rN rA rD injG injN
    quotientData.globalBlocks quotientData.localBlocks ambientData.ambientBlocks ambientData.localBlocks
    quotientData.globalCatalogue quotientData.localCatalogue ambientData.ambientCatalogue ambientData.localCatalogue
    phiG phiN initialGlobal fixedLocal globalAgreement localAgreement fieldSource hcyclic
    (V.subgroup.map B.rawMap) (originalNormalizerInterval P psi V B C) ambientData.intervalLaw
    S9295 S9495 S820 hInd
  let atBase := baseBlockDataOfExtensions P Nbar B.base C.D B.baseEquiv C.eM square
    rG rN rA rD injG injN quotientData.globalBlocks quotientData.localBlocks
    quotientData.globalCatalogue quotientData.localCatalogue phiG phiN
    chosenGlobal fixedLocal fieldSource hInd
  let atTop := topBlockData P C.D rA rD
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _)
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _)
    ambientData.ambientBlocks ambientData.localBlocks ambientData.ambientCatalogue ambientData.localCatalogue
    chosenGlobal.1 fixedLocal.1 fieldSource htop
  exact ⟨{
    quotient := ownCentralQuotientBrauerSource P psi
    ambient := B
    localGroup := C.D
    localGroup_eq := C.D_eq
    localMap := C.localMap
    localMap_natural := C.localMap_natural
    localMap_range := C.localMap_range hprimeTo quotientData.normalizers
    globalRoot := rA
    globalCharacter := chosenGlobal.1
    globalRestriction := globalExtension_restriction P psi B rA chosenGlobal
    localRoot := rD
    localCharacter := fixedLocal.1
    localRestriction := localExtension_restriction P psi V source compatibility hrawBlock
      hprimeTo quotientData.normalizers B C rD fixedLocal
    intermediateBlocks := actualIntermediateOfBaseOrTop P B.base C.D chosenGlobal.1.1 fixedLocal.1.1
      hcard atBase atTop
    qOne := fun h => (hV h).elim }⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorNontrivialPacket


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
