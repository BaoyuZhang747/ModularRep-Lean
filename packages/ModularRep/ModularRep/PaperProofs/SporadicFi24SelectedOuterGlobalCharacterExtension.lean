import ModularRep.PrimeRegularRootEmbeddingSubgroup
import ModularRep.PaperProofs.SpathPositiveQTopBlockChoice
import ModularRep.PaperProofs.SporadicFi24SelectedOuterBareGlobalExtension
import ModularRep.PaperProofs.SporadicFi24SelectedOuterSpathAmbient

/-!
# Global character extension for the selected Fischer carrier

The cyclic outer action supplies a representation extension from the selected
embedded base to the selected Brauer stabiliser.  This module transports its
Brauer character to the canonical central quotient and packages the resulting
global character extension.  It contains no block induction, BAW, or iBAW
conclusion.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24SelectedOuterGlobalCharacterExtension

open Formalisation
open ModularRep
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZCentrelessCentralKernel
open ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SpathPositiveQTopBlockChoice
open ModularRep.PaperProofs.SporadicFi24SelectedOuterC2
open ModularRep.PaperProofs.SporadicFi24SelectedOuterBareGlobalExtension
open ModularRep.PaperProofs.SporadicFi24SelectedOuterSpathAmbient
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual

universe u

/-- Forget the block and permutation data, retaining only the selected
square-one outer automorphism. -/
def outerInvolutionCarrierOfFi24Source
    {k X : Type u} [Field k] [Group X]
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :
    SporadicFi24SelectedOuterInvolutionCarrier.SelectedOuterInvolutionCarrier X where
  outer := S.outer
  outer_square := S.outer_square

noncomputable local instance selectedOuterFiniteForGlobalCharacterExtension
    {k X : Type u} [Field k] [Group X] [Finite X]
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :
    Finite (SelectedOuterGroup S) :=
  Finite.of_injective
    (fun e : SelectedOuterGroup S ↦ (e.1.unop : X → X))
    (fun _a _b h ↦ Subtype.ext
      (MulOpposite.unop_injective (DFunLike.coe_injective h)))

noncomputable local instance selectedAmbientFiniteForGlobalCharacterExtension
    {k X : Type u} [Field k] [Group X] [Finite X]
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :
    Finite (SelectedOuterAmbient S) :=
  Finite.of_injective
    (fun g : SelectedOuterAmbient S ↦ (g.left, g.right)) (by
      intro a b hab
      exact SemidirectProduct.ext
        (congrArg Prod.fst hab) (congrArg Prod.snd hab))

/-- Transport through the centreless quotient cancels before passage to the
selected embedded base. -/
theorem pullbackPrimeRegularAlongEquiv_eq_selectedBaseBrauer
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H)) :
    pullbackPrimeRegularAlongEquiv
        (@canonicalHToEmbeddedEquiv P.H (SelectedOuterGroup S) (IBr P.iota)
          _ _ (selectedOuterField S)
          (selectedBrauerSemidirectAction P.iota S)
          psi.1 (selectedBrauer_inner_fixed P.iota S psi.1))
        psi.1.1 =
      (IrreducibleBrauerCharacter.alongMulEquiv
        (SelectedCentralQuotient P hcenter reference psi).iota
        (selectedBaseEquiv P hcenter reference psi S)
        (SelectedCentralQuotient P hcenter reference psi).brauer).1 := by
  let eQ : CentralCharacterQuotient P reference ≃* P.H :=
    centerlessCentralCharacterQuotientEquiv P hcenter reference
  let eH :=
    @canonicalHToEmbeddedEquiv P.H (SelectedOuterGroup S) (IBr P.iota)
      _ _ (selectedOuterField S)
      (selectedBrauerSemidirectAction P.iota S)
      psi.1 (selectedBrauer_inner_fixed P.iota S psi.1)
  change
    pullbackPrimeRegularAlongEquiv eH psi.1.1 =
      (IrreducibleBrauerCharacter.alongMulEquiv
        (P.iota.alongMulEquiv eQ.symm) (eQ.trans eH)
        (IrreducibleBrauerCharacter.alongMulEquiv
          P.iota eQ.symm psi.1)).1
  apply PrimeRegularClassFunction.ext
  intro x
  simp only [pullbackPrimeRegularAlongEquiv_apply,
    IrreducibleBrauerCharacter.alongMulEquiv_val,
    PrimeRegularClassFunction.pullback_apply]
  apply congrArg (fun y ↦ psi.1.1 y)
  apply Subtype.ext
  change eH.symm x.1 = eQ ((eQ.trans eH).symm x.1)
  have happly :=
    congrArg eH.symm ((eQ.trans eH).apply_symm_apply x.1)
  simpa only [MulEquiv.trans_apply, eH.symm_apply_apply] using happly.symm

/-- Agreement of the selected ambient root with the transported base root on
the prime regular roots of the embedded base. -/
def SelectedGlobalRestrictionRootCompatibility
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (ambientRoot : PrimeRegularRootEmbedding P.p P.k P.K
      (SelectedBrauerAmbient P.iota S psi.1)) : Prop :=
  let quotient := SelectedCentralQuotient P hcenter reference psi
  let baseRoot := quotient.iota.alongMulEquiv
    (selectedBaseEquiv P hcenter reference psi S)
  ∀ zeta : rootsOfUnity
      (primeRegularExponent P.p
        (SelectedBrauerBase P.iota S psi.1)) P.k,
    baseRoot.lift (((zeta : P.kˣ) : P.k)) =
      ambientRoot.lift (((zeta : P.kˣ) : P.k))

/-- Starting from any selected ambient root embedding, reselect one that
agrees with the transported base convention on all roots required by the
embedded base. -/
theorem exists_selectedGlobalRestrictionRootCompatibility
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (seedAmbientRoot : PrimeRegularRootEmbedding P.p P.k P.K
      (SelectedBrauerAmbient P.iota S psi.1)) :
    ∃ ambientRoot : PrimeRegularRootEmbedding P.p P.k P.K
        (SelectedBrauerAmbient P.iota S psi.1),
      SelectedGlobalRestrictionRootCompatibility
        P hcenter reference psi S ambientRoot := by
  let quotient := SelectedCentralQuotient P hcenter reference psi
  let baseRoot := quotient.iota.alongMulEquiv
    (selectedBaseEquiv P hcenter reference psi S)
  exact PrimeRegularRootEmbedding.exists_ambient_agreeing_on_subgroup
    (SelectedBrauerBase P.iota S psi.1) baseRoot ⟨seedAmbientRoot⟩

/-- The cyclic extension theorem and a supplied ambient root embedding
construct the bare global character extension.  The ambient root convention
is reselected internally to agree with the transported base convention.  No
relation with the fixed local block is asserted here. -/
theorem selectedChosenGlobalExtensionData
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference psi : Definition35Brauer P)
    (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
    (haut : Function.Bijective
      (semidirectToMulAut (selectedOuterField S)))
    (principle :
      Representation.BrauerCyclicExtensionPrinciple.{u, u, u} P.p P.k)
    (seedAmbientRoot : PrimeRegularRootEmbedding P.p P.k P.K
      (SelectedBrauerAmbient P.iota S psi.1)) :
    let ambient :=
      selectedOuterSpathAmbientCore P hcenter reference psi S haut
    Nonempty (ChosenGlobalExtensionData ambient) := by
  let quotient := SelectedCentralQuotient P hcenter reference psi
  let ambient :=
    selectedOuterSpathAmbientCore P hcenter reference psi S haut
  let eH : P.H ≃* SelectedBrauerBase P.iota S psi.1 :=
    @canonicalHToEmbeddedEquiv P.H (SelectedOuterGroup S) (IBr P.iota)
      _ _ (selectedOuterField S)
      (selectedBrauerSemidirectAction P.iota S)
      psi.1 (selectedBrauer_inner_fixed P.iota S psi.1)
  let baseRoot := quotient.iota.alongMulEquiv ambient.baseEquiv
  let baseBrauer := IrreducibleBrauerCharacter.alongMulEquiv
    quotient.iota ambient.baseEquiv quotient.brauer
  have hbase :
      pullbackPrimeRegularAlongEquiv eH psi.1.1 = baseBrauer.1 := by
    exact pullbackPrimeRegularAlongEquiv_eq_selectedBaseBrauer
      P hcenter reference psi S
  let _ : MulAction (SelectedOuterAmbient S) (IBr P.iota) :=
    selectedBrauerSemidirectAction P.iota S
  let carrier := outerInvolutionCarrierOfFi24Source S
  obtain ⟨ambientRoot, rootCompatible⟩ :=
    exists_selectedGlobalRestrictionRootCompatibility
      P hcenter reference psi S seedAmbientRoot
  obtain ⟨globalExtension⟩ :=
    selectedGlobalCharacterExtensionWitness
      P.iota carrier principle psi.1
        baseRoot baseBrauer hbase ambientRoot rootCompatible
  exact ⟨{
    ambientRoot := ambientRoot
    globalExtension := globalExtension }⟩

end ModularRep.PaperProofs.SporadicFi24SelectedOuterGlobalCharacterExtension


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
