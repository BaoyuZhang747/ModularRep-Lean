import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalLocalNormalizer
import ModularRep.BrauerCharacterHomPullback

/-! Individual base extensions have the literal restrictions required by
the original packet. These are deductions through the actual maps. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalExtensionRestrictions

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open Representation.Extension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalAmbient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalLocalNormalizer
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnNormalizerBrauer
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnCentralQuotient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientRoot
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction

universe u

theorem globalExtension_restriction
    (P : Definition35Problem.{u}) (psi : Definition35Brauer P)
    (B : OriginalSpathAmbient P psi)
    (rA : PrimeRegularRootEmbedding P.p P.k P.K B.A)
    (W : BrauerCharacterExtensionWitness rA
      ((quotientRoot P.iota (centralCharacterKernel P psi)).alongMulEquiv B.baseEquiv)
      (IrreducibleBrauerCharacter.alongMulEquiv
        (quotientRoot P.iota (centralCharacterKernel P psi)) B.baseEquiv (ownQuotientBrauer P psi))) :
    PrimeRegularClassFunction.pullback B.rawMap W.1.1 = psi.1.1 := by
  apply PrimeRegularClassFunction.ext
  intro n
  let y := PrimeRegularElement.map (centralCharacterQuotientMap P psi) n
  let b := PrimeRegularElement.map B.baseEquiv.toMonoidHom y
  have hb : PrimeRegularElement.map B.baseEquiv.symm.toMonoidHom b = y := by
    apply Subtype.ext
    exact B.baseEquiv.symm_apply_apply _
  have hw := congrArg (fun chi : PrimeRegularClassFunction P.K B.base P.p => chi b) W.2
  change W.1.1 (PrimeRegularElement.map B.rawMap n) =
    (ownQuotientBrauer P psi).1 (PrimeRegularElement.map B.baseEquiv.symm.toMonoidHom b) at hw
  have hy := congrArg (fun chi : PrimeRegularClassFunction P.K P.H P.p => chi n)
    (ownQuotientBrauer_inflation P psi)
  exact hw.trans ((congrArg (ownQuotientBrauer P psi).1 hb).trans hy)

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

theorem localExtension_restriction
    (B : OriginalSpathAmbient P psi) (C : OriginalLocalNormalizerData P psi V B)
    (rD : PrimeRegularRootEmbedding P.p P.k P.K C.D)
    (W : BrauerCharacterExtensionWitness rD
      ((ownNormalizerRoot P psi V source hprimeTo normalizers).alongMulEquiv C.eM)
      (IrreducibleBrauerCharacter.alongMulEquiv
        (ownNormalizerRoot P psi V source hprimeTo normalizers) C.eM
        (ownNormalizerBrauer P psi V source compatibility hrawBlock hprimeTo normalizers))) :
    ∀ n : PrimeRegularElement (G := Subgroup.normalizer (V.subgroup : Set P.H)) P.p,
      W.1.1 (PrimeRegularElement.map C.localMap n) = V.localCharacter (QuotientGroup.mk n.1) := by
  intro n
  let phiN := ownNormalizerBrauer P psi V source compatibility hrawBlock hprimeTo normalizers
  let y := PrimeRegularElement.map (ownNormalizerMap P psi V) n
  have he : PrimeRegularElement.map C.eM.symm.toMonoidHom
      (PrimeRegularElement.map C.eM.toMonoidHom y) = y := by
    apply Subtype.ext
    exact C.eM.symm_apply_apply _
  have hm := congrArg (fun chi : PrimeRegularClassFunction P.K C.localBase P.p =>
    chi (PrimeRegularElement.map C.eM.toMonoidHom y)) W.2
  change W.1.1 (PrimeRegularElement.map C.localMap n) = phiN.1
    (PrimeRegularElement.map C.eM.symm.toMonoidHom
      (PrimeRegularElement.map C.eM.toMonoidHom y)) at hm
  have hn := congrArg (fun chi : PrimeRegularClassFunction P.K
      (Subgroup.normalizer (V.subgroup : Set P.H)) P.p => chi n)
    (ownNormalizerBrauer_pullback P psi V source compatibility hrawBlock hprimeTo normalizers)
  exact hm.trans ((congrArg phiN.1 he).trans (hn.trans (source.localBrauer_reduction n).symm))

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalExtensionRestrictions


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
