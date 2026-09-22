import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalQOneBlocks
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalAmbientBlockData
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalQuotientData
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorBaseInvariance
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualCyclicBrauerExtensions
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualOuterQuotient

/-! The Q=1 packet uses one global extension on both sides. Local character,
specified catalogues, self-induction and all intermediate records are
constructed without the cyclic block chooser. -/

noncomputable section
set_option maxHeartbeats 4000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorQOnePacket

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
  (DefectZeroReductionSource TrivialWeightSource GlobalDefectZeroCharacter)
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCoverGroupFacts
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalActualPacket
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalLocalNormalizer
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalAmbientBlockData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalQuotientData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorActualAmbient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorBaseInvariance
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualCyclicBrauerExtensions
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalExtensionRestrictions
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalQOneExtension
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalQOneGroups.OriginalLocalNormalizerData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalQOneBlocks
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualIntermediateAssembly
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnCentralQuotient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientRoot
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction

universe u

local instance quotientFintype (P : Definition35Problem.{u}) (psi : Definition35Brauer P) :
    Fintype (CentralCharacterQuotient P psi) := Fintype.ofFinite _
local instance subgroupFintype {A : Type u} [Group A] [Finite A] (H : Subgroup A) :
    Fintype H := Fintype.ofFinite H

theorem exists_trivialSectorPacket_atOne
    (P : Definition35Problem.{u}) (psi : Definition35Brauer P)
    (V : CharacterWeight P.p P.K P.H) (hV : V.subgroup = ⊥)
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
    (Dzero : DefectZeroReductionSource P.iota)
    (T : TrivialWeightSource (p := P.p) (X := P.H))
    (hOne : ∀ d : GlobalDefectZeroCharacter (p := P.p) (K := P.K) (X := P.H),
      Omega (Dzero.reduce (iota := P.iota) d) = T.atOne d)
    (hclass : (Quotient.mk'' (Quotient.mk'' V) :
      ConjugacyClass (p := P.p) (K := P.K) (G := P.H)) = Omega psi.1)
    (hOuter : Nat.card (LiteralOuterQuotient (CentralCharacterQuotient P psi)) = 2)
    (extensionPrinciple : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} P.p P.k)
    (seed : PrimeRegularRootEmbedding P.p P.k P.K
      (trivialSectorOriginalAmbient P psi q hq hs hna hcenter hglobal).A)
    (fieldSource : SpathCoefficientField P.p P.k P.iota.prime) :
    Nonempty (OriginalActualWeightPacket P psi V) := by
  let : Group.IsPerfect P.H := ⟨perfect_of_universalCentralExtension q hq⟩
  let : Fact P.p.Prime := ⟨P.iota.prime⟩
  let B := trivialSectorOriginalAmbient P psi q hq hs hna hcenter hglobal
  let C := actualLocalNormalizerData P psi V q hq hs hna hcenter hglobal
  let hprimeTo := centralKernel_primeTo P psi hcenter
  let rG := quotientRoot P.iota (centralCharacterKernel P psi)
  let phiG := ownQuotientBrauer P psi
  let rB := rG.alongMulEquiv B.baseEquiv
  let phiB := IrreducibleBrauerCharacter.alongMulEquiv rG B.baseEquiv phiG
  have hcyclic : IsCyclic (B.A ⧸ B.base) := actual_quotient_isCyclic rG phiG hOuter
  have hcard : Nat.card (B.A ⧸ B.base) ≤ 2 := actual_quotient_card_le_two rG phiG hOuter
  obtain ⟨rA, _, ⟨globalW⟩⟩ := exists_extensionWitness_with_retained_agreement
    B.base extensionPrinciple rB phiB hcyclic
    (originalGlobalBaseFixed P psi q hq hs hna hcenter hglobal) seed
  let eD := qOneLocalEquiv C hV
  have heD := qOneLocalEquiv_toMonoidHom C hV
  let rD := rA.alongMulEquiv eD.symm
  let localW := qOneLocalExtension P psi V source compatibility hrawBlock hprimeTo
    quotientData.normalizers B C rA globalW Omega Dzero T hOne hclass hV
  let atBase := qOneActualIntermediate P C.D eD heD rA globalW.1 B.base rB phiB globalW.2
    (quotientData.globalBlocks.alongMulEquiv B.baseEquiv)
    (quotientData.globalCatalogue.alongMulEquiv B.baseEquiv) fieldSource
  let eTop : B.A ≃* (⊤ : Subgroup B.A) := Subgroup.topEquiv.symm
  let rTop := rA.alongMulEquiv eTop
  let phiTop := IrreducibleBrauerCharacter.alongMulEquiv rA eTop globalW.1
  have hTopRestriction : PrimeRegularClassFunction.pullback (⊤ : Subgroup B.A).subtype
      globalW.1.1 = phiTop.1 := by
    apply PrimeRegularClassFunction.ext
    intro x
    rfl
  let atTop := qOneActualIntermediate P C.D eD heD rA globalW.1 (⊤ : Subgroup B.A)
    rTop phiTop hTopRestriction (ambientData.ambientBlocks.alongMulEquiv eTop)
    (ambientData.ambientCatalogue.alongMulEquiv eTop) fieldSource
  exact ⟨{
    quotient := ownCentralQuotientBrauerSource P psi
    ambient := B
    localGroup := C.D
    localGroup_eq := C.D_eq
    localMap := C.localMap
    localMap_natural := C.localMap_natural
    localMap_range := C.localMap_range hprimeTo quotientData.normalizers
    globalRoot := rA
    globalCharacter := globalW.1
    globalRestriction := globalExtension_restriction P psi B rA globalW
    localRoot := rD
    localCharacter := localW.1
    localRestriction := localExtension_restriction P psi V source compatibility hrawBlock
      hprimeTo quotientData.normalizers B C rD localW
    intermediateBlocks := actualIntermediateOfBaseOrTop P B.base C.D globalW.1.1 localW.1.1
      hcard atBase atTop
    qOne := fun _ => qOneLocalExtension_equality P psi V source compatibility hrawBlock hprimeTo
      quotientData.normalizers B C rA globalW Omega Dzero T hOne hclass hV }⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorQOnePacket


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
