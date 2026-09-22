import ModularRep.PaperProofs.CyclicOuterEmbeddedPairNormalizer
import ModularRep.PaperProofs.EvenFieldFLZCentrelessLocalPackets
import ModularRep.PaperProofs.SporadicFi24SelectedOuterLocalCarrier
import ModularRep.PaperProofs.SporadicFi24SelectedOuterLocalRepresentationExtension

/-!
# The selected Fischer pair-level Brauer-character extension

This module compares the literal selected pair base with the normaliser in
the centreless central quotient.  It then upgrades the already constructed
representation extension to a Brauer-character extension.  The only new
inputs are three compatibility conditions on the characteristic polynomial
roots used along the relevant homomorphisms.  No block equality, BAW, or
iBAW conclusion is used or proved here.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24SelectedOuterPairLocalCharacterExtension

open ModularRep
open ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterEmbeddedPairNormalizer
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZ318SelfCover
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZCentrelessLocalPackets
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicFi24SelectedOuterC2
open ModularRep.PaperProofs.SporadicFi24SelectedOuterLocalCarrier
open ModularRep.PaperProofs.SporadicFi24SelectedOuterLocalRepresentationExtension
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual

universe u

noncomputable local instance selectedOuterFiniteForPairCharacterExtension
    {k X : Type u} [Field k] [Group X] [Finite X]
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :
    Finite (SelectedOuterGroup S) :=
  Finite.of_injective
    (fun e : SelectedOuterGroup S ↦ (e.1.unop : X → X))
    (fun _a _b h ↦ Subtype.ext
      (MulOpposite.unop_injective (DFunLike.coe_injective h)))

/-- The selected pair base is the normaliser of the image of its radical in
the centreless central quotient. -/
def selectedPairBaseEquivQuotientNormalizer
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference : Definition35Brauer P)
    (w : Definition35Weight P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H)) :
    SelectedPairBase P S w ≃*
      Subgroup.normalizer
        (quotientRadical P reference w :
          Set (CentralCharacterQuotient P reference)) :=
  (embeddedPairHStabilizerEquivNormalizer
      (selectedOuterField S) P.blockSource P.block w).trans
    (normalizerEquiv
      (centerlessCentralCharacterQuotientMapEquiv
        P hcenter reference)
      (selectedRadical P w))

theorem selectedPairBaseEquivQuotientNormalizer_coe
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference : Definition35Brauer P)
    (w : Definition35Weight P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (h : SelectedPairBase P S w) :
    ((selectedPairBaseEquivQuotientNormalizer
          P hcenter reference w S h :
        Subgroup.normalizer
          (quotientRadical P reference w :
            Set (CentralCharacterQuotient P reference))) :
      CentralCharacterQuotient P reference) =
    centralCharacterQuotientMap P reference
      (((h : SelectedPairStabilizer P S w) :
        SelectedOuterAmbient S).left) := by
  calc
    ((selectedPairBaseEquivQuotientNormalizer
          P hcenter reference w S h :
        Subgroup.normalizer
          (quotientRadical P reference w :
            Set (CentralCharacterQuotient P reference))) :
      CentralCharacterQuotient P reference) =
        centerlessCentralCharacterQuotientMapEquiv
          P hcenter reference
          (embeddedPairHStabilizerEquivNormalizer
            (selectedOuterField S) P.blockSource P.block w h) := rfl
    _ = centralCharacterQuotientMap P reference
        (((h : SelectedPairStabilizer P S w) :
          SelectedOuterAmbient S).left) := by
      rw [centerlessCentralCharacterQuotientMapEquiv_apply,
        embeddedPairHStabilizerEquivNormalizer_coe]

private theorem quotientNormalizerMap_mk_centerless
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference : Definition35Brauer P)
    (w : Definition35Weight P)
    (n : Subgroup.normalizer (selectedRadical P w : Set P.H)) :
    quotientNormalizerMap P reference w (QuotientGroup.mk n) =
      quotientLocalInflationMap P reference w
        (normalizerEquiv
          (centerlessCentralCharacterQuotientMapEquiv
            P hcenter reference)
          (selectedRadical P w) n) := by
  let Q := selectedRadical P w
  let f := centralCharacterQuotientMap P reference
  let NG := Subgroup.normalizer (Q : Set P.H)
  let NH := Subgroup.normalizer
    ((Q.map f : Subgroup (CentralCharacterQuotient P reference)) :
      Set (CentralCharacterQuotient P reference))
  let R : Subgroup NG := Q.subgroupOf NG
  let T : Subgroup NH := (Q.map f).subgroupOf NH
  let fN : NG →* NH := normalizerMap f Q
  have hmap : R ≤ T.comap fN := by
    intro q hq
    change f q.1 ∈ Q.map f
    exact ⟨q.1, hq, rfl⟩
  change
    (QuotientGroup.map R T fN hmap)
        (QuotientGroup.mk' R n) =
      QuotientGroup.mk' T
        (normalizerEquiv
          (centerlessCentralCharacterQuotientMapEquiv
            P hcenter reference)
          (selectedRadical P w) n)
  rw [QuotientGroup.map_mk']
  apply congrArg
  apply Subtype.ext
  rw [normalizerMap_coe, normalizerEquiv_coe]
  rfl

/-- The two canonical routes from the selected pair base to the normaliser
quotient in the centreless central quotient agree. -/
theorem selectedPairBase_quotientNormalizer_square
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference : Definition35Brauer P)
    (w : Definition35Weight P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H)) :
    let quotientInput := canonicalRawNormalizerQuotientInput
      (p := P.p) (K := P.K) (H := P.H)
    letI : (EmbeddedRadical (selectedOuterField S)
      P.blockSource P.block quotientInput w).Normal :=
      embeddedRadical_normal
        (phi := selectedOuterField S)
        (blockSource := P.blockSource)
        (block := P.block) quotientInput w
    (quotientLocalInflationMap P reference w).comp
        (selectedPairBaseEquivQuotientNormalizer
          P hcenter reference w S).toMonoidHom =
      (quotientNormalizerMap P reference w).comp
        ((normalizerQuotientEquivLocalBase
          (selectedOuterField S) P.blockSource P.block
          quotientInput w).symm.toMonoidHom.comp
            (subgroupToQuotientImage
              (EmbeddedRadical (selectedOuterField S)
                P.blockSource P.block quotientInput w)
              (SelectedPairBase P S w))) := by
  dsimp only
  let quotientInput := canonicalRawNormalizerQuotientInput
    (p := P.p) (K := P.K) (H := P.H)
  letI : (EmbeddedRadical (selectedOuterField S)
      P.blockSource P.block quotientInput w).Normal :=
    embeddedRadical_normal
      (phi := selectedOuterField S)
      (blockSource := P.blockSource)
      (block := P.block) quotientInput w
  let eD := embeddedPairHStabilizerEquivNormalizer
    (selectedOuterField S) P.blockSource P.block w
  let eLocal := normalizerQuotientEquivLocalBase
    (selectedOuterField S) P.blockSource P.block quotientInput w
  let f := subgroupToQuotientImage
    (EmbeddedRadical (selectedOuterField S)
      P.blockSource P.block quotientInput w)
    (SelectedPairBase P S w)
  apply MonoidHom.ext
  intro h
  have hlocal : eLocal.symm (f h) = QuotientGroup.mk (eD h) := by
    apply eLocal.injective
    rw [eLocal.apply_symm_apply]
    change f h = eLocal (QuotientGroup.mk (eD h))
    simpa only [f, eLocal, eD, MulEquiv.symm_apply_apply] using
      (subgroupToQuotientImage_embeddedEquiv_symm
        (selectedOuterField S) P.blockSource P.block
        quotientInput w (eD h))
  change quotientLocalInflationMap P reference w
      (normalizerEquiv
        (centerlessCentralCharacterQuotientMapEquiv
          P hcenter reference)
        (selectedRadical P w) (eD h)) =
    quotientNormalizerMap P reference w (eLocal.symm (f h))
  rw [hlocal]
  exact (quotientNormalizerMap_mk_centerless
    P hcenter reference w (eD h)).symm

/-- Root compatibility for inflation from the quotient local group to the
normaliser of the quotient radical. -/
def SelectedQuotientInflationRootCompatibility
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference : Definition35Brauer P)
    (w : Definition35Weight P)
    (iotaBarN : PrimeRegularRootEmbedding P.p P.k P.K
      (Subgroup.normalizer
        (quotientRadical P reference w :
          Set (CentralCharacterQuotient P reference)))) : Prop :=
  let weight :=
    centerlessQuotientWeightBrauerSource P hcenter reference w
  Representation.BrauerRootLiftCompatibleAlong
    (chosenIBrRepresentation weight.iota weight.brauer).ρ
    weight.iota iotaBarN
    (quotientLocalInflationMap P reference w)

/-- The quotient local inflation selected from the compatible root data. -/
def selectedQuotientLocalInflation
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference : Definition35Brauer P)
    (w : Definition35Weight P)
    (iotaBarN : PrimeRegularRootEmbedding P.p P.k P.K
      (Subgroup.normalizer
        (quotientRadical P reference w :
          Set (CentralCharacterQuotient P reference))))
    (compatible : SelectedQuotientInflationRootCompatibility
      P hcenter reference w iotaBarN) :
    QuotientLocalInflationSource P reference w
      (centerlessQuotientWeightBrauerSource
        P hcenter reference w) :=
  quotientLocalInflationSourceOfCompatible
    P reference w
    (centerlessQuotientWeightBrauerSource P hcenter reference w)
    iotaBarN compatible

/-- The root embedding on the selected pair base obtained by transport from
the quotient normaliser. -/
def selectedPairBaseRoot
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference : Definition35Brauer P)
    (w : Definition35Weight P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (iotaBarN : PrimeRegularRootEmbedding P.p P.k P.K
      (Subgroup.normalizer
        (quotientRadical P reference w :
          Set (CentralCharacterQuotient P reference)))) :
    PrimeRegularRootEmbedding P.p P.k P.K (SelectedPairBase P S w) :=
  iotaBarN.alongMulEquiv
    (selectedPairBaseEquivQuotientNormalizer
      P hcenter reference w S).symm

/-- The inflated local Brauer character transported to the selected pair
base. -/
def selectedPairBaseCharacter
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference : Definition35Brauer P)
    (w : Definition35Weight P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (iotaBarN : PrimeRegularRootEmbedding P.p P.k P.K
      (Subgroup.normalizer
        (quotientRadical P reference w :
          Set (CentralCharacterQuotient P reference))))
    (compatible : SelectedQuotientInflationRootCompatibility
      P hcenter reference w iotaBarN) :
    IBr (selectedPairBaseRoot P hcenter reference w S iotaBarN) := by
  let localInflation := selectedQuotientLocalInflation
    P hcenter reference w iotaBarN compatible
  exact IrreducibleBrauerCharacter.alongMulEquiv
    localInflation.iota
    (selectedPairBaseEquivQuotientNormalizer
      P hcenter reference w S).symm
    localInflation.brauer

/-- Root compatibility for pulling a local representation back to the
selected pair base. -/
def SelectedPairBaseRootCompatibility
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference : Definition35Brauer P)
    (w : Definition35Weight P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (iotaBarN : PrimeRegularRootEmbedding P.p P.k P.K
      (Subgroup.normalizer
        (quotientRadical P reference w :
          Set (CentralCharacterQuotient P reference)))) : Prop :=
  let quotientInput := canonicalRawNormalizerQuotientInput
    (p := P.p) (K := P.K) (H := P.H)
  letI : (EmbeddedRadical (selectedOuterField S)
      P.blockSource P.block quotientInput w).Normal :=
    embeddedRadical_normal
      (phi := selectedOuterField S)
      (blockSource := P.blockSource)
      (block := P.block) quotientInput w
  let f := subgroupToQuotientImage
    (EmbeddedRadical (selectedOuterField S)
      P.blockSource P.block quotientInput w)
    (SelectedPairBase P S w)
  ∀ W : FDRep P.k
      (LocalBase (selectedOuterField S)
        P.blockSource P.block quotientInput w),
    Representation.BrauerRootLiftCompatibleAlong W.ρ
      (transportedLocalRootEmbedding
        (selectedOuterField S) P.blockSource P.block
        quotientInput w (P.localReduction w))
      (selectedPairBaseRoot P hcenter reference w S iotaBarN) f

/-- Root compatibility for restricting a representation of the pair
stabiliser to the selected pair base. -/
def SelectedPairRestrictionRootCompatibility
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference : Definition35Brauer P)
    (w : Definition35Weight P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (iotaBarN : PrimeRegularRootEmbedding P.p P.k P.K
      (Subgroup.normalizer
        (quotientRadical P reference w :
          Set (CentralCharacterQuotient P reference))))
    (pairRoot : PrimeRegularRootEmbedding P.p P.k P.K
      (SelectedPairStabilizer P S w)) : Prop :=
  let quotientInput := canonicalRawNormalizerQuotientInput
    (p := P.p) (K := P.K) (H := P.H)
  letI : (EmbeddedRadical (selectedOuterField S)
      P.blockSource P.block quotientInput w).Normal :=
    embeddedRadical_normal
      (phi := selectedOuterField S)
      (blockSource := P.blockSource)
      (block := P.block) quotientInput w
  let f := subgroupToQuotientImage
    (EmbeddedRadical (selectedOuterField S)
      P.blockSource P.block quotientInput w)
    (SelectedPairBase P S w)
  ∀ (W : FDRep P.k
        (LocalBase (selectedOuterField S)
          P.blockSource P.block quotientInput w))
      (extension : Representation.Extension
        (SelectedPairBase P S w)
        (Representation.pullback W.ρ f)),
    Representation.BrauerRootLiftCompatibleAlong
      extension.representation pairRoot
      (selectedPairBaseRoot P hcenter reference w S iotaBarN)
      (SelectedPairBase P S w).subtype

/-- The selected representation extension determines an actual Brauer
character extension on the pair stabiliser.  The three additional premises
compare root lifts only along the homomorphisms not handled by transport
along a group equivalence. -/
theorem selectedPairLocalBrauerCharacterExtension
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference : Definition35Brauer P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (principle :
      Representation.BrauerCyclicExtensionPrinciple.{u, u, u} P.p P.k)
    (w : Definition35Weight P)
    (iotaBarN : PrimeRegularRootEmbedding P.p P.k P.K
      (Subgroup.normalizer
        (quotientRadical P reference w :
          Set (CentralCharacterQuotient P reference))))
    (pairRoot : PrimeRegularRootEmbedding P.p P.k P.K
      (SelectedPairStabilizer P S w))
    (quotientInflationCompatible :
      SelectedQuotientInflationRootCompatibility
        P hcenter reference w iotaBarN)
    (localInflationCompatible :
      SelectedPairBaseRootCompatibility
        P hcenter reference w S iotaBarN)
    (pairRestrictionCompatible :
      SelectedPairRestrictionRootCompatibility
        P hcenter reference w S iotaBarN pairRoot) :
    Nonempty
      (Representation.Extension.BrauerCharacterExtensionWitness
        pairRoot
        (selectedPairBaseRoot P hcenter reference w S iotaBarN)
        (selectedPairBaseCharacter
          P hcenter reference w S iotaBarN
            quotientInflationCompatible)) := by
  let weight :=
    centerlessQuotientWeightBrauerSource P hcenter reference w
  let localInflation :=
    selectedQuotientLocalInflation
      P hcenter reference w iotaBarN quotientInflationCompatible
  let eN := selectedPairBaseEquivQuotientNormalizer
    P hcenter reference w S
  let pairBaseRoot := localInflation.iota.alongMulEquiv eN.symm
  let pairBaseCharacter :=
    IrreducibleBrauerCharacter.alongMulEquiv
      localInflation.iota eN.symm localInflation.brauer
  change Nonempty
    (Representation.Extension.BrauerCharacterExtensionWitness
      pairRoot pairBaseRoot pairBaseCharacter)
  let quotientInput := canonicalRawNormalizerQuotientInput
    (p := P.p) (K := P.K) (H := P.H)
  letI : (EmbeddedRadical (selectedOuterField S)
      P.blockSource P.block quotientInput w).Normal :=
    embeddedRadical_normal
      (phi := selectedOuterField S)
      (blockSource := P.blockSource)
      (block := P.block) quotientInput w
  let eLocal := normalizerQuotientEquivLocalBase
    (selectedOuterField S) P.blockSource P.block quotientInput w
  let f := subgroupToQuotientImage
    (EmbeddedRadical (selectedOuterField S)
      P.blockSource P.block quotientInput w)
    (SelectedPairBase P S w)
  rcases selectedPairLocalRepresentationExtension P S principle w with
    ⟨W, hW, hcharacter, _hreduction, ⟨extension⟩⟩
  have hf : Function.Surjective f := by
    intro y
    rcases y.2 with ⟨x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hxy
  have hsquare :=
    selectedPairBase_quotientNormalizer_square
      P hcenter reference w S
  have hbridge :
      pairBaseCharacter.1 =
        PrimeRegularClassFunction.pullback f
          (transportedLocalBrauer
            (selectedOuterField S) P.blockSource P.block
            quotientInput w (P.localReduction w)).1 := by
    rw [IrreducibleBrauerCharacter.alongMulEquiv_val]
    change
      PrimeRegularClassFunction.pullback eN.toMonoidHom
          localInflation.brauer.1 =
        PrimeRegularClassFunction.pullback f
          (PrimeRegularClassFunction.pullback
            eLocal.symm.toMonoidHom
            (P.localReduction w).brauer.1)
    rw [← localInflation.inflation, ← weight.brauerDescends]
    apply PrimeRegularClassFunction.ext
    intro x
    simp only [PrimeRegularClassFunction.pullback_apply]
    apply congrArg (fun y => weight.brauer.1 y)
    apply Subtype.ext
    exact congrArg
      (fun g : SelectedPairBase P S w →*
          NormalizerQuotient (quotientRadical P reference w) => g x.1)
      hsquare
  have haffords :
      Representation.brauerCharacterOfRootEmbedding
          (Representation.pullback W.ρ f) pairBaseRoot =
        pairBaseCharacter.1 := by
    calc
      _ = PrimeRegularClassFunction.pullback f
          (Representation.brauerCharacterOfRootEmbedding W.ρ
            (transportedLocalRootEmbedding
              (selectedOuterField S) P.blockSource P.block
              quotientInput w (P.localReduction w))) :=
        Representation.brauerCharacterOfRootEmbedding_pullback_of_compatible
          W.ρ
          (transportedLocalRootEmbedding
            (selectedOuterField S) P.blockSource P.block
            quotientInput w (P.localReduction w))
          pairBaseRoot f (localInflationCompatible W)
      _ = PrimeRegularClassFunction.pullback f
          (transportedLocalBrauer
            (selectedOuterField S) P.blockSource P.block
            quotientInput w (P.localReduction w)).1 :=
        congrArg (PrimeRegularClassFunction.pullback f) hcharacter.symm
      _ = pairBaseCharacter.1 := hbridge.symm
  exact ⟨
    Representation.Extension.brauerCharacterExtensionWitnessOfCompatible
      extension
      (hW.pullback f hf)
      pairRoot pairBaseRoot pairBaseCharacter
      haffords (pairRestrictionCompatible W extension)
  ⟩

end ModularRep.PaperProofs.SporadicFi24SelectedOuterPairLocalCharacterExtension


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
