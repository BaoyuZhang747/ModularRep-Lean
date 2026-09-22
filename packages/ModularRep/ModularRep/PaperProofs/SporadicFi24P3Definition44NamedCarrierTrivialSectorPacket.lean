import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorNontrivialPacket
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorQOnePacket

/-! The complete conditional original-cover packet in the trivial central
sector. Both radical branches retain the same original correspondence and
raw weight; Q=1 uses a common extension instead of the cyclic block chooser. -/

noncomputable section
set_option maxHeartbeats 4000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorPacket

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
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorNontrivialPacket
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorQOnePacket
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction

universe u

def trivialSectorOriginalPacket
    (P : Definition35Problem.{u}) (psi : Definition35Brauer P)
    (V : CharacterWeight P.p P.K P.H)
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
    (fieldSource : SpathCoefficientField P.p P.k P.iota.prime)
    (S9295 : Navarro9295BrauerRestrictionCoveringPrinciple P.p P.k P.K)
    (S9495 : Navarro9495BrauerCoveringPrinciple P.p P.k P.K)
    (S820 : Navarro820CyclicBrauerTwistPrinciple P.p P.k P.K) :
    OriginalActualWeightPacket P psi V :=
  Classical.choice (by
    classical
    by_cases hV : V.subgroup = ⊥
    · exact exists_trivialSectorPacket_atOne P psi V hV q hq hs hna hcenter hglobal
        source compatibility hrawBlock quotientData ambientData Omega Dzero T hOne hclass
        hOuter extensionPrinciple seed fieldSource
    · exact exists_trivialSectorPacket_nontrivial P psi V hV q hq hs hna hcenter hglobal
        source compatibility hrawBlock quotientData ambientData Omega hOmega hclass
        hOuter extensionPrinciple seed fieldSource S9295 S9495 S820)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorPacket


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
