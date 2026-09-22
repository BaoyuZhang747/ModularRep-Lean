import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIdentityAmbient
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalIdentityBlocks
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction

/-! Actual identity extensions and their single intermediate block relation.
The matched raw pair and normalized Omega are internal construction inputs;
the complete-collapse source endpoint constructs them from numerical AWC. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalIdentityPacket

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZCentrelessCentralKernel
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
  (DefectZeroReductionSource TrivialWeightSource GlobalDefectZeroCharacter)
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualRadicalPacket
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIdentityAmbient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalIdentityBlocks
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRawReduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction

universe u

def identityPacket (P : Definition35Problem.{u})
    (hc : Subgroup.center P.H = ⊥) (psi : Definition35Brauer P)
    (allInner : ∀ a : MulAut P.H, ∃ x : P.H, a = MulAut.conj x)
    (Omega : IBr P.iota ≃ ConjugacyClass (p := P.p) (K := P.K) (G := P.H))
    (D : DefectZeroReductionSource P.iota) (T : TrivialWeightSource (p := P.p) (X := P.H))
    (hOne : ∀ d : GlobalDefectZeroCharacter (p := P.p) (K := P.K) (X := P.H),
      Omega (D.reduce (iota := P.iota) d) = T.atOne d)
    (V : CharacterWeight P.p P.K P.H)
    (hclass : (Quotient.mk'' (Quotient.mk'' V) : ConjugacyClass (p := P.p) (K := P.K) (G := P.H)) = Omega psi.1)
    (source : CanonicalRawReduction P.iota V)
    (compatibility : CanonicalLocalBlockCompatibility P.iota P.blockSource.operations)
    (fieldSource : SpathCoefficientField P.p P.k P.iota.prime)
    (hrawBlock :
      letI := P.blockSource.operations.ambientBlockData.fintypeBlock
      P.blockSource.operations.rawWeightBlock V =
        irreducibleBrauerCharacterBlock P.iota P.irreducibleBrauerInjective
          P.blockSource.operations.ambientBlockData.blocks psi.1) :
    ActualWeightPacket P psi V := by
  let q := centerlessCentralQuotientBrauerSource P hc psi
  let A := identityAmbient P hc psi q allInner
  let embed : P.H →* P.H := (quotientToAmbient P psi psi q A).comp (centralCharacterQuotientMap P psi)
  have hemb : embed = MonoidHom.id P.H := identityAmbient_embedding P hc psi q allInner
  let N := Subgroup.normalizer (V.subgroup : Set P.H)
  refine {
    quotient := q
    ambient := A
    embeddingInjective := ?_
    localGroup := N
    localGroup_eq := ?_
    localMap := MonoidHom.id N
    localMap_natural := ?_
    localMap_range := ?_
    globalRoot := P.iota
    globalCharacter := psi.1
    globalRestriction := ?_
    localRoot := source.normalizerRoot
    localCharacter := source.localBrauer
    localRestriction := ?_
    intermediateBlocks := fun J hJ => allIntermediateBlockData P psi.1 V
      source
      compatibility fieldSource hrawBlock J hJ
    qOne := fun hV => localBrauer_atOne P.iota Omega D T hOne psi.1 V hclass source.toRaw hV }
  · change Function.Injective embed
    rw [hemb]
    exact Function.injective_id
  · change N = Subgroup.normalizer (V.subgroup.map embed : Set P.H)
    rw [hemb, Subgroup.map_id]
  · change N.subtype.comp (MonoidHom.id N) = embed.comp N.subtype
    rw [hemb]
    rfl
  · change (MonoidHom.id N).range = (⊤ : Subgroup P.H).comap N.subtype
    rw [Subgroup.comap_top]
    exact MonoidHom.range_eq_top.mpr Function.surjective_id
  · intro x
    change psi.1.1 (PrimeRegularElement.map embed x) = psi.1.1 x
    rw [hemb]
    rfl
  · intro n
    exact (source.localBrauer_reduction n).symm

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalIdentityPacket


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
