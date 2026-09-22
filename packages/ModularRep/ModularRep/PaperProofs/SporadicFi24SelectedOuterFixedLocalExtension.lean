import ModularRep.PaperProofs.SpathPositiveQTopBlockChoice
import ModularRep.PaperProofs.SporadicFi24SelectedOuterAmbientLocalCharacterExtension

/-!
# Fixed local extension data for the selected Fischer carrier

The ambient local Brauer character extension is packaged as the fixed local
half of the positive radical Spath data.  This is only a change of carrier.  It
does not choose a global extension or prove a block-induction equality.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24SelectedOuterFixedLocalExtension

open ModularRep
open ModularRep.CharacterWeight
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SpathPositiveQTopBlockChoice
open ModularRep.PaperProofs.SporadicFi24SelectedOuterAmbientLocalCharacterExtension
open ModularRep.PaperProofs.SporadicFi24SelectedOuterC2
open ModularRep.PaperProofs.SporadicFi24SelectedOuterLocalCarrier
open ModularRep.PaperProofs.SporadicFi24SelectedOuterPairLocalCharacterExtension
open ModularRep.PaperProofs.SporadicFi24SelectedOuterSpathAmbient
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual

universe u

noncomputable local instance selectedOuterFiniteForFixedLocalExtension
    {k X : Type u} [Field k] [Group X] [Finite X]
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :
    Finite (SelectedOuterGroup S) :=
  Finite.of_injective
    (fun e : SelectedOuterGroup S ↦ (e.1.unop : X → X))
    (fun _a _b h ↦ Subtype.ext
      (MulOpposite.unop_injective (DFunLike.coe_injective h)))

/-- Package the selected ambient local extension as the fixed local input for
the positive radical Spath construction. -/
theorem selectedFixedLocalExtensionData
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
    Nonempty (FixedLocalExtensionData localInflation ambient) := by
  let localInflation :=
    selectedQuotientLocalInflation
      P hcenter reference w iotaBarN quotientInflationCompatible
  let ambient :=
    SelectedSpathAmbient P hcenter reference psi S haut
  let eA :=
    selectedPairStabilizerEquivAmbientLocalGroup
      P hcenter reference psi w S Omega hOmega hmatch haut
  let localAmbientRoot := pairRoot.alongMulEquiv eA
  change Nonempty (FixedLocalExtensionData localInflation ambient)
  have hW :
      Nonempty
        (Representation.Extension.BrauerCharacterExtensionWitness
          localAmbientRoot
          (localInflation.iota.alongMulEquiv
            (canonicalLocalBaseEquiv (w := w) ambient))
          (IrreducibleBrauerCharacter.alongMulEquiv
            localInflation.iota
            (canonicalLocalBaseEquiv (w := w) ambient)
            localInflation.brauer)) := by
    simpa only [localInflation, ambient, localAmbientRoot, eA] using
      selectedAmbientLocalBrauerCharacterExtension
        P hcenter reference psi w S Omega hOmega hmatch haut
        principle iotaBarN pairRoot quotientInflationCompatible
        localInflationCompatible pairRestrictionCompatible
  exact Nonempty.map
    (fun W =>
      ({ localAmbientRoot := localAmbientRoot
         localExtension := W } :
        FixedLocalExtensionData localInflation ambient))
    hW

end ModularRep.PaperProofs.SporadicFi24SelectedOuterFixedLocalExtension


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
