import ModularRep.BrauerCharacterExtensionWitnessTransport
import ModularRep.PaperProofs.CanonicalLocalBaseTransport
import ModularRep.PaperProofs.SporadicFi24SelectedOuterPairLocalCharacterExtension

/-!
# Transport of the selected Fischer local character extension

The pair level Brauer character extension is transported to the local
normaliser in the selected Spath ambient group.  The comparison between the
direct quotient normaliser and the ambient local base is proved internally.
This module contains no block equality, BAW, or iBAW conclusion.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24SelectedOuterAmbientLocalCharacterExtension

open ModularRep
open ModularRep.CharacterWeight
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterEmbeddedPairNormalizer
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZCentrelessLocalPackets
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicFi24SelectedOuterC2
open ModularRep.PaperProofs.SporadicFi24SelectedOuterLocalCarrier
open ModularRep.PaperProofs.SporadicFi24SelectedOuterPairLocalCharacterExtension
open ModularRep.PaperProofs.SporadicFi24SelectedOuterSpathAmbient
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual

universe u

noncomputable local instance selectedOuterFiniteForAmbientCharacterExtension
    {k X : Type u} [Field k] [Group X] [Finite X]
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :
    Finite (SelectedOuterGroup S) :=
  Finite.of_injective
    (fun e : SelectedOuterGroup S ↦ (e.1.unop : X → X))
    (fun _a _b h ↦ Subtype.ext
      (MulOpposite.unop_injective (DFunLike.coe_injective h)))

private theorem selectedPairBaseEquivQuotientNormalizer_toAmbient
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P)
    (w : Definition35Weight P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (Omega : IBr P.iota ≃ GlobalWeight P)
    (hOmega : ∀ alpha : (MulAut P.H)ᵐᵒᵖ, ∀ chi : IBr P.iota,
      Omega (alpha • chi) = alpha • Omega chi)
    (hmatch : w.1 = Omega psi.1)
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S)))
    (h : SelectedPairBase P S w) :
    quotientToAmbient P reference psi
        (SelectedCentralQuotient P hcenter reference psi)
        (SelectedSpathAmbient P hcenter reference psi S haut)
        (selectedPairBaseEquivQuotientNormalizer
          P hcenter reference w S h).1 =
      (selectedPairBaseEquivAmbientLocalBase
        P hcenter reference psi w S Omega hOmega hmatch haut h).1.1 := by
  apply Subtype.ext
  rw [selectedPairBaseEquivQuotientNormalizer_coe,
    selectedQuotientToAmbient_mk_coe,
    selectedPairBaseEquivAmbientLocalBase_apply_outer_coe]
  apply SemidirectProduct.ext
  · rfl
  · exact ((mem_selectedPairBase_iff_right_eq_one
      P S w h.1).mp h.2).symm

/-- The direct pair-base equivalence with the quotient normaliser agrees with
the route through the selected ambient local base. -/
theorem selectedPairBaseEquivQuotientNormalizer_eq_ambient
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P)
    (w : Definition35Weight P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (Omega : IBr P.iota ≃ GlobalWeight P)
    (hOmega : ∀ alpha : (MulAut P.H)ᵐᵒᵖ, ∀ chi : IBr P.iota,
      Omega (alpha • chi) = alpha • Omega chi)
    (hmatch : w.1 = Omega psi.1)
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S))) :
    selectedPairBaseEquivQuotientNormalizer
        P hcenter reference w S =
      (selectedPairBaseEquivAmbientLocalBase
        P hcenter reference psi w S Omega hOmega hmatch haut).trans
        (canonicalLocalBaseEquiv
          (w := w)
          (SelectedSpathAmbient
            P hcenter reference psi S haut)).symm := by
  apply MulEquiv.ext
  intro h
  simp only [MulEquiv.trans_apply]
  apply Subtype.ext
  apply quotientToAmbient_injective
    (SelectedSpathAmbient P hcenter reference psi S haut)
  rw [canonicalLocalBaseEquiv_symm_natural,
    selectedPairBaseEquivQuotientNormalizer_toAmbient]

/-- The selected pair level extension transports to the local normaliser in
the selected Spath ambient group.  The only root comparisons required are the
three pointwise compatibility conditions already used at pair level. -/
theorem selectedAmbientLocalBrauerCharacterExtension
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P)
    (w : Definition35Weight P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (Omega : IBr P.iota ≃ GlobalWeight P)
    (hOmega : ∀ alpha : (MulAut P.H)ᵐᵒᵖ, ∀ chi : IBr P.iota,
      Omega (alpha • chi) = alpha • Omega chi)
    (hmatch : w.1 = Omega psi.1)
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S)))
    (principle :
      Representation.BrauerCyclicExtensionPrinciple.{u, u, u} P.p P.k)
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
    let localInflation :=
      selectedQuotientLocalInflation
        P hcenter reference w iotaBarN quotientInflationCompatible
    let ambient :=
      SelectedSpathAmbient P hcenter reference psi S haut
    Nonempty
      (Representation.Extension.BrauerCharacterExtensionWitness
        (pairRoot.alongMulEquiv
          (selectedPairStabilizerEquivAmbientLocalGroup
            P hcenter reference psi w S Omega hOmega hmatch haut))
        (localInflation.iota.alongMulEquiv
          (canonicalLocalBaseEquiv (w := w) ambient))
        (IrreducibleBrauerCharacter.alongMulEquiv
          localInflation.iota
          (canonicalLocalBaseEquiv (w := w) ambient)
          localInflation.brauer)) := by
  let localInflation :=
    selectedQuotientLocalInflation
      P hcenter reference w iotaBarN quotientInflationCompatible
  let ambient :=
    SelectedSpathAmbient P hcenter reference psi S haut
  let eA :=
    selectedPairStabilizerEquivAmbientLocalGroup
      P hcenter reference psi w S Omega hOmega hmatch haut
  let eBase :=
    selectedPairBaseEquivAmbientLocalBase
      P hcenter reference psi w S Omega hOmega hmatch haut
  let eN :=
    selectedPairBaseEquivQuotientNormalizer
      P hcenter reference w S
  let eCanonical :=
    canonicalLocalBaseEquiv (w := w) ambient
  change Nonempty
    (Representation.Extension.BrauerCharacterExtensionWitness
      (pairRoot.alongMulEquiv eA)
      (localInflation.iota.alongMulEquiv eCanonical)
      (IrreducibleBrauerCharacter.alongMulEquiv
        localInflation.iota eCanonical localInflation.brauer))
  have heN : eN = eBase.trans eCanonical.symm := by
    simpa only [eN, eBase, eCanonical, ambient] using
      (selectedPairBaseEquivQuotientNormalizer_eq_ambient
        P hcenter reference psi w S Omega hOmega hmatch haut)
  rcases selectedPairLocalBrauerCharacterExtension
      P hcenter reference S principle w iotaBarN pairRoot
      quotientInflationCompatible localInflationCompatible
      pairRestrictionCompatible with
    ⟨pairWitness⟩
  refine ⟨pairWitness.alongMulEquivOfBase
    eA eBase ?_
    (localInflation.iota.alongMulEquiv eCanonical)
    (IrreducibleBrauerCharacter.alongMulEquiv
      localInflation.iota eCanonical localInflation.brauer)
    ?_⟩
  · simpa only [eA, eBase] using
      (selectedPairBaseEquivAmbientLocalBase_symm_square
        P hcenter reference psi w S Omega hOmega hmatch haut)
  · change
      PrimeRegularClassFunction.pullback eBase.symm.toMonoidHom
          (PrimeRegularClassFunction.pullback eN.toMonoidHom
            localInflation.brauer.1) =
        PrimeRegularClassFunction.pullback
          eCanonical.symm.toMonoidHom localInflation.brauer.1
    apply PrimeRegularClassFunction.ext
    intro x
    simp only [PrimeRegularClassFunction.pullback_apply]
    apply congrArg (fun y => localInflation.brauer.1 y)
    apply Subtype.ext
    change eN (eBase.symm x.1) = eCanonical.symm x.1
    simpa only [heN, MulEquiv.trans_apply,
      eBase.apply_symm_apply]

end ModularRep.PaperProofs.SporadicFi24SelectedOuterAmbientLocalCharacterExtension


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
