import ModularRep.PaperProofs.TypeBButterflyHonestTargetRoots
import ModularRep.PaperProofs.TypeBSpathHonestLocalExtensionSource
import ModularRep.PaperProofs.TypeBFullBlockCondition

/-!
# Finite root agreements for the chosen honest target

The quotient convention agrees with the chosen ambient convention through
the literal base equivalence. The local ambient and both intermediate roots
are restrictions of that same ambient root. Each comparison is confined to
the finite root domain of its first group.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBHonestRootAgreementBinding

open ModularRep
open EvenFieldFLZSourceConditions EvenFieldFLZBAWGoodFamily
open TypeBLocalReductionInstantiation TypeBModularGroupRootBinding
open TypeBCentralKernelTripleRootFamily TypeBButterflyHonestTargetRoots
open TypeBFullBlockCondition

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

include quotientCalibration in
/-- The reference quotient and its literal ambient base use the same finite
root domain, so the calibrated base agreement gives the quotient agreement. -/
theorem quotientAmbient_roots :
    RootLiftAgreement quotient.iota (groupRoot Msys ambient.A) := by
  intro z
  have exponentEquality :
      primeRegularExponent P.p (CentralCharacterQuotient P reference) =
        primeRegularExponent P.p ambient.base :=
    congrArg (fun n : ℕ => ordCompl[P.p] n)
      (Nat.card_congr ambient.baseEquiv.toEquiv)
  let baseRoot : rootsOfUnity (primeRegularExponent P.p ambient.base) P.k :=
    ⟨z.val, by
      change z.val ^ _ = 1
      rw [← exponentEquality]
      exact z.property⟩
  exact (quotient.iota.alongMulEquiv_lift ambient.baseEquiv _).symm.trans
    (baseRoot_agrees P reference psi quotient ambient Msys quotientCalibration baseRoot)

/-- The local ambient root is the restriction to the full actual normalizer. -/
theorem localAmbient_roots :
    RootLiftAgreement
      (TypeBSpathHonestLocalExtensionSource.localAmbientRoot
        (targetData P reference psi w quotient weight localInflation ambient Msys
          quotientCalibration localCalibration blocks))
      (groupRoot Msys ambient.A) := by
  intro z
  exact TypeBSpathHonestLocalExtensionSource.localAmbientRoot_agrees
    (targetData P reference psi w quotient weight localInflation ambient Msys
      quotientCalibration localCalibration blocks) z

/-- Every global intermediate root retains the chosen ambient convention. -/
theorem intermediate_roots (J : Subgroup ambient.A) (hNJ : ambient.base ≤ J) :
    RootLiftAgreement
      ((targetData P reference psi w quotient weight localInflation ambient Msys
        quotientCalibration localCalibration blocks).intermediate J hNJ).iota
      (groupRoot Msys ambient.A) := by
  intro z
  exact (targetData P reference psi w quotient weight localInflation ambient Msys
    quotientCalibration localCalibration blocks).intermediateRoots J hNJ z

/-- The literal local intermediate root retains the same ambient convention
through both subgroup inclusions. -/
theorem localIntermediate_roots (J : Subgroup ambient.A) (hNJ : ambient.base ≤ J) :
    RootLiftAgreement
      ((targetData P reference psi w quotient weight localInflation ambient Msys
        quotientCalibration localCalibration blocks).localIntermediateData J hNJ).iota
      (groupRoot Msys ambient.A) := by
  intro z
  exact (targetData P reference psi w quotient weight localInflation ambient Msys
    quotientCalibration localCalibration blocks).localIntermediateRoots J hNJ z

end ModularRep.PaperProofs.TypeBHonestRootAgreementBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
