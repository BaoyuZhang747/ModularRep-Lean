import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorPacket
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierStabilizerInnerPacket
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPrimeCenterKernel
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierLiteralOuterTransport

/-! Exhaustive actual central-kernel branches on a prime-order centre.
Both packet constructions retain one original match. Ambient catalogues
and one root seed are supplied only as unselected lower data. -/

noncomputable section
set_option maxHeartbeats 4000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPrimeCenterPacket

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.NavarroBrauerRestrictionCovering ModularRep.NavarroCoveringBrauerExtension
open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
  (DefectZeroReductionSource TrivialWeightSource GlobalDefectZeroCharacter)
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalActualPacket
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalLocalNormalizer
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalAmbientBlockData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalQuotientData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorActualAmbient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorPacket
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierStabilizerInnerPacket
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPrimeCenterKernel
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierLiteralOuterTransport
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCoverGroupFacts

universe u

local instance quotientFintype (P : Definition35Problem.{u}) (psi : Definition35Brauer P) :
    Fintype (CentralCharacterQuotient P psi) := Fintype.ofFinite _
local instance subgroupFintype {A : Type u} [Group A] [Finite A] (H : Subgroup A) :
    Fintype H := Fintype.ofFinite H

def primeCenterOriginalPacket
    (P : Definition35Problem.{u}) (psi : Definition35Brauer P)
    (V : CharacterWeight P.p P.K P.H)
    {S : Type u} [Group S] (q : P.H →* S) (hq : IsUniversalCentralExtension q)
    (hs : IsSimpleGroup S) (hna : ¬ IsMulCommutative S)
    (hcenter : ¬ P.p ∣ Nat.card (Subgroup.center P.H))
    (hcardCenter : (Nat.card (Subgroup.center P.H)).Prime)
    (source : CanonicalRawReduction P.iota V)
    (compatibility : CanonicalLocalBlockCompatibility P.iota P.blockSource.operations)
    (hrawBlock :
      letI := P.blockSource.operations.ambientBlockData.fintypeBlock
      P.blockSource.operations.rawWeightBlock V =
        irreducibleBrauerCharacterBlock P.iota P.irreducibleBrauerInjective
          P.blockSource.operations.ambientBlockData.blocks psi.1)
    (quotientData : OriginalQuotientData P psi V hcenter)
    (ambientData :
      ∀ hglobal : (∀ z : PrimeRegularElement (G := Subgroup.center P.H) P.p,
        psi.1.1 (PrimeRegularElement.map (Subgroup.center P.H).subtype z) =
          psi.1.1 ⟨1, isPrimeRegular_one⟩),
        OriginalAmbientBlockData P psi V
          (trivialSectorOriginalAmbient P psi q hq hs hna hcenter hglobal)
          (actualLocalNormalizerData P psi V q hq hs hna hcenter hglobal))
    (Omega : IBr P.iota ≃ ConjugacyClass (p := P.p) (K := P.K) (G := P.H))
    (hOmega : ∀ (a : (MulAut P.H)ᵐᵒᵖ) (chi : IBr P.iota), Omega (a • chi) = a • Omega chi)
    (Dzero : DefectZeroReductionSource P.iota)
    (T : TrivialWeightSource (p := P.p) (X := P.H))
    (hOne : ∀ d : GlobalDefectZeroCharacter (p := P.p) (K := P.K) (X := P.H),
      Omega (Dzero.reduce (iota := P.iota) d) = T.atOne d)
    (hclass : (Quotient.mk'' (Quotient.mk'' V) :
      ConjugacyClass (p := P.p) (K := P.K) (G := P.H)) = Omega psi.1)
    (hOuterS : Nat.card (LiteralOuterQuotient S) = 2)
    (tau : MulAut P.H)
    (decomposition : ∀ a : MulAut P.H, ∃ x : P.H,
      a = MulAut.conj x ∨ a = MulAut.conj x * tau)
    (movesCenter : ∃ z : Subgroup.center P.H, tau (z : P.H) ≠ z)
    (extensionPrinciple : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} P.p P.k)
    (seed :
      ∀ hglobal : (∀ z : PrimeRegularElement (G := Subgroup.center P.H) P.p,
        psi.1.1 (PrimeRegularElement.map (Subgroup.center P.H).subtype z) =
          psi.1.1 ⟨1, isPrimeRegular_one⟩),
        PrimeRegularRootEmbedding P.p P.k P.K
          (trivialSectorOriginalAmbient P psi q hq hs hna hcenter hglobal).A)
    (fieldSource : SpathCoefficientField P.p P.k P.iota.prime)
    (S9295 : Navarro9295BrauerRestrictionCoveringPrinciple P.p P.k P.K)
    (S9495 : Navarro9495BrauerCoveringPrinciple P.p P.k P.K)
    (S820 : Navarro820CyclicBrauerTwistPrinciple P.p P.k P.K) :
    OriginalActualWeightPacket P psi V :=
  Classical.choice (by
    let : Group.IsPerfect P.H := ⟨perfect_of_universalCentralExtension q hq⟩
    rcases centralKernel_eq_bot_or_center P psi hcardCenter with hbot | hfull
    · exact ⟨identityPacket_of_faithfulCenter
        P psi V source compatibility hrawBlock hcenter
        quotientData.normalizers quotientData.globalBlocks quotientData.localBlocks
        quotientData.globalCatalogue quotientData.localCatalogue quotientData.intervalLaw
        quotientData.globalImageLaw quotientData.localImageLaw
        hbot tau decomposition movesCenter Omega Dzero T hOne hclass fieldSource⟩
    · let hglobal := brauerCenterTrivial_of_kernel_eq_center P psi hfull
      have hOuter := ownOuterCardTwo_of_centerKernel P psi q hq hs hna hfull hOuterS
      exact ⟨trivialSectorOriginalPacket P psi V q hq hs hna hcenter hglobal
        source compatibility hrawBlock quotientData (ambientData hglobal)
        Omega hOmega Dzero T hOne hclass hOuter extensionPrinciple (seed hglobal)
        fieldSource S9295 S9495 S820⟩)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPrimeCenterPacket


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
