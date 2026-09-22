import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnCentralQuotient
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnQuotientGroupFacts

/-! Q=1 normalization in the actual own central quotient. The equality
is derived from the same correspondence and original raw representative,
then descended by injectivity of prime regular pullback. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnQuotientQOne

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.IrreducibleBrauerCharacterSurjectiveDescent
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
  (DefectZeroReductionSource TrivialWeightSource GlobalDefectZeroCharacter)
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRawReduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnCentralQuotient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnNormalizerBrauer
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnQuotientGroupFacts

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
  (centralCharacterKernel P psi) (show centralCharacterKernel P psi ≤ Subgroup.center P.H from inf_le_left)
  hprimeTo V.subgroup V.radical)

theorem ownNormalizerBrauer_atOne
    (Omega : IBr P.iota ≃ ConjugacyClass (p := P.p) (K := P.K) (G := P.H))
    (D : DefectZeroReductionSource P.iota) (T : TrivialWeightSource (p := P.p) (X := P.H))
    (hOne : ∀ d : GlobalDefectZeroCharacter (p := P.p) (K := P.K) (X := P.H),
      Omega (D.reduce (iota := P.iota) d) = T.atOne d)
    (hclass : (Quotient.mk'' (Quotient.mk'' V) :
      ConjugacyClass (p := P.p) (K := P.K) (G := P.H)) = Omega psi.1)
    (hV : V.subgroup = ⊥) :
    PrimeRegularClassFunction.pullback
      (Subgroup.normalizer (V.subgroup.map (centralCharacterQuotientMap P psi) :
        Set (CentralCharacterQuotient P psi))).subtype
      (ownQuotientBrauer P psi).1 =
        (ownNormalizerBrauer P psi V source compatibility hrawBlock hprimeTo normalizers).1 := by
  let N := Subgroup.normalizer (V.subgroup : Set P.H)
  let Nbar := Subgroup.normalizer (V.subgroup.map (centralCharacterQuotientMap P psi) :
    Set (CentralCharacterQuotient P psi))
  let f := ownNormalizerMap P psi V
  have hcoprime : (Nat.card f.ker).Coprime P.p :=
    (P.iota.prime.coprime_iff_not_dvd.mpr
      (own_normalizer_ker_primeTo P psi V hprimeTo)).symm
  apply primeRegularClassFunction_pullback_injective_of_ker_card_coprime
    f (ownNormalizerMap_surjective P psi V hprimeTo normalizers) hcoprime
  calc
    PrimeRegularClassFunction.pullback f
        (PrimeRegularClassFunction.pullback Nbar.subtype (ownQuotientBrauer P psi).1) =
      PrimeRegularClassFunction.pullback N.subtype
        (PrimeRegularClassFunction.pullback (centralCharacterQuotientMap P psi)
          (ownQuotientBrauer P psi).1) := by
            apply PrimeRegularClassFunction.ext
            intro n
            rfl
    _ = PrimeRegularClassFunction.pullback N.subtype psi.1.1 :=
      congrArg (PrimeRegularClassFunction.pullback N.subtype)
        (ownQuotientBrauer_inflation P psi)
    _ = source.localBrauer.1 :=
      localBrauer_atOne P.iota Omega D T hOne psi.1 V hclass source.toRaw hV
    _ = PrimeRegularClassFunction.pullback f
        (ownNormalizerBrauer P psi V source compatibility hrawBlock hprimeTo normalizers).1 :=
      (ownNormalizerBrauer_pullback P psi V source compatibility hrawBlock hprimeTo normalizers).symm

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnQuotientQOne


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
