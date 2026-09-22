import ModularRep.PaperProofs.SporadicFi24SelectedOuterGlobalCharacterExtension
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSpathIntervals

/-!
# A global extension retaining its root agreement

Reselect the supplied ambient root to agree with the prescribed base root,
then apply the cyclic extension principle. The agreement is exported with
the extension because the subsequent covering argument uses that same root.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierGlobalExtension

open Formalisation ModularRep
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SpathPositiveQTopBlockChoice
open ModularRep.PaperProofs.SporadicFi24SelectedOuterC2
open ModularRep.PaperProofs.SporadicFi24SelectedOuterBareGlobalExtension
open ModularRep.PaperProofs.SporadicFi24SelectedOuterGlobalCharacterExtension
open ModularRep.PaperProofs.SporadicFi24SelectedOuterSpathAmbient
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual

universe u

variable (P : Definition35Problem.{u})
variable (hcenter : Subgroup.center P.H = ⊥)
variable (reference psi : Definition35Brauer P)
variable (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
variable (haut : Function.Bijective (semidirectToMulAut (selectedOuterField S)))

local instance outerFinite : Finite (SelectedOuterGroup S) :=
  Finite.of_injective (fun e : SelectedOuterGroup S ↦ (e.1.unop : P.H → P.H))
    (fun _ _ h ↦ Subtype.ext
      (MulOpposite.unop_injective (DFunLike.coe_injective h)))

theorem exists_global_extension_with_root_agreement
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} P.p P.k)
    (seed : PrimeRegularRootEmbedding P.p P.k P.K (SelectedBrauerAmbient P.iota S psi.1)) :
    ∃ global : ChosenGlobalExtensionData
        (selectedOuterSpathAmbientCore P hcenter reference psi S haut),
      SelectedGlobalRestrictionRootCompatibility P hcenter reference psi S global.ambientRoot := by
  let q := SelectedCentralQuotient P hcenter reference psi
  let A := selectedOuterSpathAmbientCore P hcenter reference psi S haut
  let rB := q.iota.alongMulEquiv A.baseEquiv
  let cB := IrreducibleBrauerCharacter.alongMulEquiv q.iota A.baseEquiv q.brauer
  obtain ⟨rA, hr⟩ :=
    exists_selectedGlobalRestrictionRootCompatibility P hcenter reference psi S seed
  obtain ⟨ext⟩ := selectedGlobalCharacterExtensionWitness
    P.iota (outerInvolutionCarrierOfFi24Source S) principle psi.1 rB cB
    (pullbackPrimeRegularAlongEquiv_eq_selectedBaseBrauer P hcenter reference psi S) rA hr
  exact ⟨{ ambientRoot := rA, globalExtension := ext }, hr⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierGlobalExtension


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
