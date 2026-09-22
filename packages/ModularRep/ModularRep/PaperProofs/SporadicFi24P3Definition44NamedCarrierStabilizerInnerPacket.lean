import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierStabilizerInnerAmbient
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulCentralStabilizer
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulCentralSector
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalTopBlockData
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnQuotientBlockInduction
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnQuotientQOne

/-! Actual block induction on the own central quotient for the same raw
match. The two specified block images and upstairs induction are derived.
Only unselected quotient catalogues and generic primitive-image/interval
source laws are additional inputs. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierStabilizerInnerPacket

open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierStabilizerInnerAmbient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulCentralStabilizer
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulCentralSector
open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRawReduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnCentralQuotient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnNormalizerBrauer
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnQuotientGroupFacts
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientRoot
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSurjectiveRoot
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientBlockAlgebra
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage

open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalAmbient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalActualPacket
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalTopBlockData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnQuotientBlockInduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnQuotientQOne
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
  (DefectZeroReductionSource TrivialWeightSource GlobalDefectZeroCharacter)

universe u
variable (P : Definition35Problem.{u}) (psi : Definition35Brauer P)
variable (V : CharacterWeight P.p P.K P.H) (source : CanonicalRawReduction P.iota V)
variable (compatibility : CanonicalLocalBlockCompatibility P.iota P.blockSource.operations)
variable (hrawBlock :
  letI := P.blockSource.operations.ambientBlockData.fintypeBlock
  P.blockSource.operations.rawWeightBlock V =
    irreducibleBrauerCharacterBlock P.iota P.irreducibleBrauerInjective
      P.blockSource.operations.ambientBlockData.blocks psi.1)
variable (hcenter : ¬ P.p ∣ Nat.card (Subgroup.center P.H))

local instance problemPrime : Fact P.p.Prime := ⟨P.iota.prime⟩
local instance quotientFintype : Fintype (CentralCharacterQuotient P psi) := Fintype.ofFinite _
local instance subgroupFintype {G : Type u} [Group G] [Finite G] (H : Subgroup G) :
    Fintype H := Fintype.ofFinite H

variable (normalizers : NavarroTiep23cFixedCentralQuotientSource
  (centralCharacterKernel P psi) (show centralCharacterKernel P psi ≤ Subgroup.center P.H from inf_le_left)
  (centralKernel_primeTo P psi hcenter) V.subgroup V.radical)

variable {BG BN : Type u} [Fintype BG] [Fintype BN]
variable {eGbar : BG → P.k[CentralCharacterQuotient P psi]}
variable {eNbar : BN → P.k[Subgroup.normalizer
  (V.subgroup.map (centralCharacterQuotientMap P psi) : Set (CentralCharacterQuotient P psi))]}
variable (DGbar : BlockIdempotentDecomposition eGbar) (DNbar : BlockIdempotentDecomposition eNbar)
variable (CGbar : BlockCentralCharacterCatalogue DGbar) (CNbar : BlockCentralCharacterCatalogue DNbar)
variable (S414 : Navarro414IntervalCentralCharacterSource
  (ownNormalizerInterval P psi V (centralKernel_primeTo P psi hcenter) normalizers) DNbar CNbar)
variable (Sglobal : CentralPrimeToPrimitiveImageSource (k := P.k)
  (centralCharacterQuotientMap P psi) (QuotientGroup.mk'_surjective _) P.iota.prime
  (own_quotient_ker_central P psi) (own_quotient_ker_primeTo P psi (centralKernel_primeTo P psi hcenter)))
variable (Slocal : CentralPrimeToPrimitiveImageSource (k := P.k)
  (ownNormalizerMap P psi V) (ownNormalizerMap_surjective P psi V (centralKernel_primeTo P psi hcenter) normalizers) P.iota.prime
  (own_normalizer_ker_central P psi V) (own_normalizer_ker_primeTo P psi V (centralKernel_primeTo P psi hcenter)))

def identityPacket_of_stabilizerInner [Group.IsPerfect P.H]
    (stabilizerInner : ∀ a : MulAction.stabilizer (MulAut P.H)ᵐᵒᵖ psi.1,
      ∃ x : P.H, a.1.unop = MulAut.conj x)
    (Omega : IBr P.iota ≃ ConjugacyClass (p := P.p) (K := P.K) (G := P.H))
    (D : DefectZeroReductionSource P.iota) (T : TrivialWeightSource (p := P.p) (X := P.H))
    (hOne : ∀ d : GlobalDefectZeroCharacter (p := P.p) (K := P.K) (X := P.H),
      Omega (D.reduce (iota := P.iota) d) = T.atOne d)
    (hclass : (Quotient.mk'' (Quotient.mk'' V) :
      ConjugacyClass (p := P.p) (K := P.K) (G := P.H)) = Omega psi.1)
    (fieldSource : SpathCoefficientField P.p P.k P.iota.prime) :
    OriginalActualWeightPacket P psi V := by
  let A := identityAmbient_of_stabilizerInner P psi hcenter stabilizerInner
  let Nbar := Subgroup.normalizer (V.subgroup.map (centralCharacterQuotientMap P psi) :
    Set (CentralCharacterQuotient P psi))
  let rG := quotientRoot P.iota (centralCharacterKernel P psi)
  let rN := ownNormalizerRoot P psi V source (centralKernel_primeTo P psi hcenter) normalizers
  let phiG := ownQuotientBrauer P psi
  let phiN := ownNormalizerBrauer P psi V source compatibility hrawBlock (centralKernel_primeTo P psi hcenter) normalizers
  have hInd := own_quotient_block_induction P psi V source compatibility hrawBlock
    (centralKernel_primeTo P psi hcenter) normalizers DGbar DNbar CGbar CNbar S414 Sglobal Slocal
  refine {
    quotient := ownCentralQuotientBrauerSource P psi
    ambient := A
    localGroup := Nbar
    localGroup_eq := rfl
    localMap := ownNormalizerMap P psi V
    localMap_natural := rfl
    localMap_range := ?_
    globalRoot := rG
    globalCharacter := phiG
    globalRestriction := ownQuotientBrauer_inflation P psi
    localRoot := rN
    localCharacter := phiN
    localRestriction := ?_
    intermediateBlocks := ?_
    qOne := ownNormalizerBrauer_atOne P psi V source compatibility hrawBlock
      (centralKernel_primeTo P psi hcenter) normalizers Omega D T hOne hclass }
  · change (ownNormalizerMap P psi V).range = (⊤ : Subgroup (CentralCharacterQuotient P psi)).comap Nbar.subtype
    rw [Subgroup.comap_top]
    exact MonoidHom.range_eq_top.mpr (ownNormalizerMap_surjective P psi V (centralKernel_primeTo P psi hcenter) normalizers)
  · intro n
    have h := congrArg (fun chi : PrimeRegularClassFunction P.K
        (Subgroup.normalizer (V.subgroup : Set P.H)) P.p => chi n)
      (ownNormalizerBrauer_pullback P psi V source compatibility hrawBlock (centralKernel_primeTo P psi hcenter) normalizers)
    exact h.trans (source.localBrauer_reduction n).symm
  · intro J hJ
    have htop : J = ⊤ := top_unique hJ
    subst J
    exact topBlockData P Nbar rG rN
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _)
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _)
      DGbar DNbar CGbar CNbar phiG phiN fieldSource hInd

def identityPacket_of_faithfulCenter [Group.IsPerfect P.H]
    (hfaithful : centralCharacterKernel P psi = ⊥)
    (tau : MulAut P.H)
    (decomposition : ∀ a : MulAut P.H, ∃ x : P.H,
      a = MulAut.conj x ∨ a = MulAut.conj x * tau)
    (movesCenter : ∃ z : Subgroup.center P.H, tau (z : P.H) ≠ z)
    (Omega : IBr P.iota ≃ ConjugacyClass (p := P.p) (K := P.K) (G := P.H))
    (D : DefectZeroReductionSource P.iota) (T : TrivialWeightSource (p := P.p) (X := P.H))
    (hOne : ∀ d : GlobalDefectZeroCharacter (p := P.p) (K := P.K) (X := P.H),
      Omega (D.reduce (iota := P.iota) d) = T.atOne d)
    (hclass : (Quotient.mk'' (Quotient.mk'' V) :
      ConjugacyClass (p := P.p) (K := P.K) (G := P.H)) = Omega psi.1)
    (fieldSource : SpathCoefficientField P.p P.k P.iota.prime) :
    OriginalActualWeightPacket P psi V :=
  identityPacket_of_stabilizerInner P psi V source compatibility hrawBlock
    hcenter normalizers DGbar DNbar CGbar CNbar S414 Sglobal Slocal
    (stabilizerInner_of_faithful_center P psi hfaithful tau decomposition movesCenter)
    Omega D T hOne hclass fieldSource

def identityPacket_of_faithfulCentralSector [Group.IsPerfect P.H]
    (lambda : OrdinaryIrreducibleCharacter.Irr P.K (Subgroup.center P.H))
    (hLambda : ∀ z, lambda z = lambda 1 → z = 1)
    (hglobal : ∀ z : PrimeRegularElement (G := Subgroup.center P.H) P.p,
      psi.1.1 (PrimeRegularElement.map (Subgroup.center P.H).subtype z) =
        psi.1.1 ⟨1, isPrimeRegular_one⟩ * lambda z.1)
    (tau : MulAut P.H)
    (decomposition : ∀ a : MulAut P.H, ∃ x : P.H,
      a = MulAut.conj x ∨ a = MulAut.conj x * tau)
    (movesCenter : ∃ z : Subgroup.center P.H, tau (z : P.H) ≠ z)
    (Omega : IBr P.iota ≃ ConjugacyClass (p := P.p) (K := P.K) (G := P.H))
    (D : DefectZeroReductionSource P.iota) (T : TrivialWeightSource (p := P.p) (X := P.H))
    (hOne : ∀ d : GlobalDefectZeroCharacter (p := P.p) (K := P.K) (X := P.H),
      Omega (D.reduce (iota := P.iota) d) = T.atOne d)
    (hclass : (Quotient.mk'' (Quotient.mk'' V) :
      ConjugacyClass (p := P.p) (K := P.K) (G := P.H)) = Omega psi.1)
    (fieldSource : SpathCoefficientField P.p P.k P.iota.prime) :
    OriginalActualWeightPacket P psi V :=
  identityPacket_of_faithfulCenter P psi V source compatibility hrawBlock
    hcenter normalizers DGbar DNbar CGbar CNbar S414 Sglobal Slocal
    (centralCharacterKernel_eq_bot_of_faithful_liesOver P psi hcenter lambda hLambda hglobal)
    tau decomposition movesCenter Omega D T hOne hclass fieldSource

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierStabilizerInnerPacket


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
