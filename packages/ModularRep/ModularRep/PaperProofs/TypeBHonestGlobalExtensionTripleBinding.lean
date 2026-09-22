import ModularRep.PaperProofs.TypeBButterflyHonestTargetRoots
import ModularRep.PaperProofs.SpathPositiveQTopBlockChoice

/-!
# The chosen global extension on the prescribed target triple

The fixed global extension has the same ambient root as the target data.
Transporting its irreducibility proof retains its exact class function and
restriction to the prescribed base character along the literal inclusion.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBHonestGlobalExtensionTripleBinding

open ModularRep TypeBLocalReductionInstantiation TypeBModularGroupRootBinding
open TypeBCentralKernelTripleRootFamily TypeBButterflyHonestTargetRoots
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family
open EvenFieldFLZBAWGoodFamily SpathPositiveQTopBlockChoice

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
  (globalRoot : global.ambientRoot = groupRoot Msys ambient.A)

include globalRoot in
/-- The root equation concerns the same chosen ambient and its target data. -/
theorem globalRoot_eq_target :
    global.ambientRoot =
      (targetData P reference psi w quotient weight localInflation ambient Msys
        quotientCalibration localCalibration blocks).ambientRoot :=
  globalRoot

/-- Retain the chosen global character while transporting only its root proof. -/
def globalExtension :
    Representation.Extension.BrauerCharacterExtensionWitness
      (targetData P reference psi w quotient weight localInflation ambient Msys
        quotientCalibration localCalibration blocks).ambientRoot
      (targetData P reference psi w quotient weight localInflation ambient Msys
        quotientCalibration localCalibration blocks).base.iota
      (baseTheta P reference psi w quotient weight localInflation ambient Msys
        quotientCalibration localCalibration blocks) := by
  have rootEquality : global.ambientRoot =
      (targetData P reference psi w quotient weight localInflation ambient Msys
        quotientCalibration localCalibration blocks).ambientRoot :=
    globalRoot_eq_target P reference psi w quotient weight localInflation ambient Msys
      quotientCalibration localCalibration blocks global globalRoot
  exact ⟨⟨global.globalExtension.1.val,
    rootEquality ▸ global.globalExtension.1.property⟩, global.globalExtension.2⟩

/-- The target witness has exactly the already chosen ambient class function. -/
@[simp] theorem globalExtension_val :
    (globalExtension P reference psi w quotient weight localInflation ambient Msys
      quotientCalibration localCalibration blocks global globalRoot).1.val =
        global.globalExtension.1.val := rfl

end ModularRep.PaperProofs.TypeBHonestGlobalExtensionTripleBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
