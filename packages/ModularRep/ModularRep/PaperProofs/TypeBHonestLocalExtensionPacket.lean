import ModularRep.PaperProofs.TypeBButterflyHonestTargetRoots
import ModularRep.PaperProofs.TypeBSpathHonestLocalExtensionSource
import ModularRep.PaperProofs.SpathPositiveQTopBlockChoice

/-!
# Extension data after the fixed global character

The global extension is supplied first. A single local extension on the
prescribed honest target is then supplied, and the two witnesses are retained
literally in the Späth extension record. This pointwise construction makes no
choice and uses the canonical local-base equivalence.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBHonestLocalExtensionPacket

open ModularRep Representation.Extension
open EvenFieldFLZSourceConditions EvenFieldFLZBAWGoodFamily
open TypeBLocalReductionInstantiation TypeBCentralKernelTripleRootFamily
open TypeBButterflyHonestTargetRoots
open SpathPositiveQTopBlockChoice

variable (P : Definition35Problem.{0})
  (reference psi : Definition35Brauer P) (w : Definition35Weight P)
  (quotient : CentralQuotientBrauerSource P reference psi)
  (weight : QuotientWeightBrauerSource P reference w)
  (localInflation : QuotientLocalInflationSource P reference w weight)
  (ambient : SpathAmbientGroup P reference psi quotient)
  {O : Type} [CommRing O] [IsDomain O] [Algebra O P.K]
  (Msys : ModularSystem P.p P.K O P.k)
  (quotientCalibration : RootResidueCompatible Msys quotient.iota)
  (localCalibration : RootResidueCompatible Msys localInflation.iota)
  (blocks : PhysicalBlockFamily (k := P.k) ambient.base
    (AmbientLocalGroup P reference psi w quotient ambient))
  (global : ChosenGlobalExtensionData ambient)
  (eta : BrauerCharacterExtensionWitness
    (TypeBSpathHonestLocalExtensionSource.localAmbientRoot
      (targetData P reference psi w quotient weight localInflation ambient Msys
        quotientCalibration localCalibration blocks))
    (targetData P reference psi w quotient weight localInflation ambient Msys
      quotientCalibration localCalibration blocks).localData.iota
    (localPhi P reference psi w quotient weight localInflation ambient Msys
      quotientCalibration localCalibration blocks))

/-- Combine the two given witnesses in their actual order, preserving the
global fields and the one local extension on the prescribed honest target. -/
def characterExtensions :
    SpathCharacterExtensions P reference psi w quotient weight localInflation ambient where
  ambientRoot := global.ambientRoot
  globalExtension := global.globalExtension
  localBaseEquiv := canonicalLocalBaseEquiv (w := w) ambient
  localBaseEquiv_natural := canonicalLocalBaseEquiv_natural ambient
  localAmbientRoot := TypeBSpathHonestLocalExtensionSource.localAmbientRoot
    (targetData P reference psi w quotient weight localInflation ambient Msys
      quotientCalibration localCalibration blocks)
  localExtension := eta

@[simp] theorem characterExtensions_ambientRoot :
    (characterExtensions P reference psi w quotient weight localInflation ambient Msys
      quotientCalibration localCalibration blocks global eta).ambientRoot =
      global.ambientRoot := rfl

@[simp] theorem characterExtensions_global_value :
    (characterExtensions P reference psi w quotient weight localInflation ambient Msys
      quotientCalibration localCalibration blocks global eta).globalExtension.val.val =
      global.globalExtension.val.val := rfl

@[simp] theorem characterExtensions_local_value :
    (characterExtensions P reference psi w quotient weight localInflation ambient Msys
      quotientCalibration localCalibration blocks global eta).localExtension.val.val =
      eta.val.val := rfl

end ModularRep.PaperProofs.TypeBHonestLocalExtensionPacket


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
