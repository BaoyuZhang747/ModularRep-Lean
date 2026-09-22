import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalQOneGroups
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnQuotientQOne
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalExtensionRestrictions

/-! At Q=1, transport one global extension to the existing actual local
group. Its local restriction is derived from the same normalized Omega,
and its ambient character equality is literal. -/

noncomputable section
set_option maxHeartbeats 2000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalQOneExtension

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open Representation.Extension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
  (DefectZeroReductionSource TrivialWeightSource GlobalDefectZeroCharacter)
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalAmbient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalLocalNormalizer
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalQOneGroups
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalQOneGroups.OriginalLocalNormalizerData
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnNormalizerBrauer
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnCentralQuotient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientRoot
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnQuotientQOne

universe u

variable (P : Definition35Problem.{u}) (psi : Definition35Brauer P)
variable (V : CharacterWeight P.p P.K P.H) (source : CanonicalRawReduction P.iota V)
variable (compatibility : CanonicalLocalBlockCompatibility P.iota P.blockSource.operations)
variable (hrawBlock :
  letI := P.blockSource.operations.ambientBlockData.fintypeBlock
  P.blockSource.operations.rawWeightBlock V =
    irreducibleBrauerCharacterBlock P.iota P.irreducibleBrauerInjective
      P.blockSource.operations.ambientBlockData.blocks psi.1)
variable (hprimeTo : ¬ P.p ∣ Nat.card (centralCharacterKernel P psi))
local instance problemPrime : Fact P.p.Prime := ⟨P.iota.prime⟩
variable (normalizers : NavarroTiep23cFixedCentralQuotientSource
  (centralCharacterKernel P psi)
  (show centralCharacterKernel P psi ≤ Subgroup.center P.H from inf_le_left)
  hprimeTo V.subgroup V.radical)
variable (B : OriginalSpathAmbient P psi) (C : OriginalLocalNormalizerData P psi V B)
variable (rA : PrimeRegularRootEmbedding P.p P.k P.K B.A)
variable (globalW : BrauerCharacterExtensionWitness rA
  ((quotientRoot P.iota (centralCharacterKernel P psi)).alongMulEquiv B.baseEquiv)
  (IrreducibleBrauerCharacter.alongMulEquiv
    (quotientRoot P.iota (centralCharacterKernel P psi)) B.baseEquiv (ownQuotientBrauer P psi)))
variable (Omega : IBr P.iota ≃ ConjugacyClass (p := P.p) (K := P.K) (G := P.H))
variable (Dzero : DefectZeroReductionSource P.iota)
variable (T : TrivialWeightSource (p := P.p) (X := P.H))
variable (hOne : ∀ d : GlobalDefectZeroCharacter (p := P.p) (K := P.K) (X := P.H),
  Omega (Dzero.reduce (iota := P.iota) d) = T.atOne d)
variable (hclass : (Quotient.mk'' (Quotient.mk'' V) :
  ConjugacyClass (p := P.p) (K := P.K) (G := P.H)) = Omega psi.1)
variable (hV : V.subgroup = ⊥)

include Omega Dzero T hOne hclass hV in
theorem globalExtension_localBase_atOne :
    PrimeRegularClassFunction.pullback C.localBase.subtype
      (PrimeRegularClassFunction.pullback C.D.subtype globalW.1.1) =
      (IrreducibleBrauerCharacter.alongMulEquiv
        (ownNormalizerRoot P psi V source hprimeTo normalizers) C.eM
        (ownNormalizerBrauer P psi V source compatibility hrawBlock hprimeTo normalizers)).1 := by
  let Nbar := Subgroup.normalizer (V.subgroup.map (centralCharacterQuotientMap P psi) :
    Set (CentralCharacterQuotient P psi))
  let phiN := ownNormalizerBrauer P psi V source compatibility hrawBlock hprimeTo normalizers
  apply PrimeRegularClassFunction.ext
  intro x
  let n : PrimeRegularElement (G := Nbar) P.p := PrimeRegularElement.map C.eM.symm.toMonoidHom x
  let b : PrimeRegularElement (G := B.base) P.p :=
    PrimeRegularElement.map B.baseEquiv.toMonoidHom (PrimeRegularElement.map Nbar.subtype n)
  have hx : PrimeRegularElement.map C.D.subtype
      (PrimeRegularElement.map C.localBase.subtype x) = PrimeRegularElement.map B.base.subtype b := by
    apply Subtype.ext
    change ((x.1 : C.D) : B.A) = B.quotientEmbedding (n.1 : CentralCharacterQuotient P psi)
    have hs := DFunLike.congr_fun C.eM_natural n.1
    change (((C.eM (C.eM.symm x.1)) : C.D) : B.A) =
      B.quotientEmbedding (n.1 : CentralCharacterQuotient P psi) at hs
    simpa only [MulEquiv.apply_symm_apply] using hs
  have hb : PrimeRegularElement.map B.baseEquiv.symm.toMonoidHom b =
      PrimeRegularElement.map Nbar.subtype n := by
    apply Subtype.ext
    exact B.baseEquiv.symm_apply_apply _
  have hg := congrArg (fun chi : PrimeRegularClassFunction P.K B.base P.p => chi b) globalW.2
  change globalW.1.1 (PrimeRegularElement.map B.base.subtype b) =
    (ownQuotientBrauer P psi).1 (PrimeRegularElement.map B.baseEquiv.symm.toMonoidHom b) at hg
  have hn := congrArg (fun chi : PrimeRegularClassFunction P.K Nbar P.p => chi n)
    (ownNormalizerBrauer_atOne P psi V source compatibility hrawBlock hprimeTo normalizers
      Omega Dzero T hOne hclass hV)
  change globalW.1.1 (PrimeRegularElement.map C.D.subtype
    (PrimeRegularElement.map C.localBase.subtype x)) = phiN.1 n
  exact (congrArg globalW.1.1 hx).trans
    (hg.trans ((congrArg (ownQuotientBrauer P psi).1 hb).trans hn))

include Omega Dzero T hOne hclass in
def qOneLocalExtension :
    BrauerCharacterExtensionWitness (rA.alongMulEquiv (qOneLocalEquiv C hV).symm)
      ((ownNormalizerRoot P psi V source hprimeTo normalizers).alongMulEquiv C.eM)
      (IrreducibleBrauerCharacter.alongMulEquiv
        (ownNormalizerRoot P psi V source hprimeTo normalizers) C.eM
        (ownNormalizerBrauer P psi V source compatibility hrawBlock hprimeTo normalizers)) :=
  ⟨IrreducibleBrauerCharacter.alongMulEquiv rA (qOneLocalEquiv C hV).symm globalW.1,
    globalExtension_localBase_atOne P psi V source compatibility hrawBlock hprimeTo normalizers
      B C rA globalW Omega Dzero T hOne hclass hV⟩

theorem qOneLocalExtension_equality :
    PrimeRegularClassFunction.pullback C.D.subtype globalW.1.1 =
      (qOneLocalExtension P psi V source compatibility hrawBlock hprimeTo normalizers
        B C rA globalW Omega Dzero T hOne hclass hV).1.1 := by
  apply PrimeRegularClassFunction.ext
  intro x
  rfl

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalQOneExtension


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
