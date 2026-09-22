import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierGlobalExtension
import ModularRep.PaperProofs.SpathQOneCharacterExtensions

/-!
# One actual global extension supplies both Q=1 extension characters

Transport an already constructed global Brauer-character extension to the
canonically equal local ambient group. Only the Q=1 base-character identity
is needed. No equality of root lifts on the entire coefficient field is
assumed; the global extension already includes its exact restriction proof.
The equality exported below concerns the extensions in this very packet.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQOneExtensions

open ModularRep
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SpathPositiveQTopBlockChoice
open ModularRep.PaperProofs.SpathQOneCharacterExtensions

universe u

variable {P : Definition35Problem.{u}}
variable {reference psi : Definition35Brauer P} {w : Definition35Weight P}
variable {quotient : CentralQuotientBrauerSource P reference psi}
variable {weight : QuotientWeightBrauerSource P reference w}
variable {localInflation : QuotientLocalInflationSource P reference w weight}
variable {ambient : SpathAmbientGroup P reference psi quotient}

def characterExtensionsOfGlobal
    (global : ChosenGlobalExtensionData ambient)
    (localData : QOneLocalTransportData localInflation ambient) :
    SpathCharacterExtensions P reference psi w quotient weight localInflation ambient := by
  let eA := (qOneAmbientLocalEquiv ambient localData.quotientRadical_eq_bot).symm
  let eBase := qOneAmbientBaseEquiv ambient localData.quotientRadical_eq_bot
  let localWitness := global.globalExtension.alongMulEquivOfBase eA eBase
    (qOneAmbientBase_square ambient localData.quotientRadical_eq_bot)
    (localInflation.iota.alongMulEquiv (canonicalLocalBaseEquiv ambient))
    (IrreducibleBrauerCharacter.alongMulEquiv localInflation.iota
      (canonicalLocalBaseEquiv ambient) localInflation.brauer)
    localData.localBrauerCompatibility
  exact {
    ambientRoot := global.ambientRoot
    globalExtension := global.globalExtension
    localBaseEquiv := canonicalLocalBaseEquiv ambient
    localBaseEquiv_natural := canonicalLocalBaseEquiv_natural ambient
    localAmbientRoot := global.ambientRoot.alongMulEquiv eA
    localExtension := localWitness }

theorem global_restriction_eq_local
    (global : ChosenGlobalExtensionData ambient)
    (localData : QOneLocalTransportData localInflation ambient) :
    PrimeRegularClassFunction.pullback
        (AmbientLocalGroup P reference psi w quotient ambient).subtype
        (characterExtensionsOfGlobal global localData).globalExtension.1.1 =
      (characterExtensionsOfGlobal global localData).localExtension.1.1 := by
  apply PrimeRegularClassFunction.ext
  intro x
  rfl

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQOneExtensions


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
