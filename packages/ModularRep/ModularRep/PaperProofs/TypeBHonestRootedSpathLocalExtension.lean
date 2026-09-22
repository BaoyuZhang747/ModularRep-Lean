import ModularRep.PaperProofs.TypeBHonestSpathLocalExtension

/-!
# Retaining the prescribed roots of one local extension

The fixed global character determines one local extension through the given
source. Each intermediate block record is selected together with its two
root identities, so these identities remain part of the resulting packet.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBHonestRootedSpathLocalExtension

open ModularRep Representation.Extension
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family
open EvenFieldFLZBAWGoodFamily SpathPositiveQTopBlockChoice
open TypeBLocalReductionInstantiation TypeBModularGroupRootBinding
open TypeBCentralKernelTripleCertificate TypeBCentralKernelTripleRootFamily
open TypeBButterflyHonestTargetRoots

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
  (fieldSource : SpathCoefficientField P.p P.k P.iota.prime)
  (certificate : TypeBSpathHonestLocalExtensionSource.HonestLocalExtensionCertificate
    P.p P.k P.K)

include globalRoot fieldSource certificate in
/-- The same local character supplies all intermediate block records, retaining
the prescribed local and intermediate roots and the centralizer support clause. -/
theorem exists_extensions_all_intermediate
    (witness : BlockTripleWitness
      (targetData P reference psi w quotient weight localInflation ambient Msys
        quotientCalibration localCalibration blocks)
      (baseTheta P reference psi w quotient weight localInflation ambient Msys
        quotientCalibration localCalibration blocks)
      (localPhi P reference psi w quotient weight localInflation ambient Msys
        quotientCalibration localCalibration blocks)) :
    ∃ extensions : SpathCharacterExtensions P reference psi w quotient weight
        localInflation ambient,
      extensions.ambientRoot = global.ambientRoot ∧
      extensions.globalExtension.val.val = global.globalExtension.val.val ∧
      extensions.localAmbientRoot =
        TypeBSpathHonestLocalExtensionSource.localAmbientRoot
          (targetData P reference psi w quotient weight localInflation ambient Msys
            quotientCalibration localCalibration blocks) ∧
      ∃ intermediate : IntermediateBlockSource P reference psi w quotient weight
          localInflation ambient extensions,
        (∀ (J : Subgroup ambient.A) (hNJ : ambient.base ≤ J),
          (intermediate.equalityAt J hNJ).globalRoot =
            ((targetData P reference psi w quotient weight localInflation ambient Msys
              quotientCalibration localCalibration blocks).intermediate J hNJ).iota ∧
          (intermediate.equalityAt J hNJ).localRoot =
            ((targetData P reference psi w quotient weight localInflation ambient Msys
              quotientCalibration localCalibration blocks).localIntermediateData J hNJ).iota) ∧
      ∀ nu : IBr (TypeBSpathHonestLocalExtensionSource.centralizerRoot
          (targetData P reference psi w quotient weight localInflation ambient Msys
            quotientCalibration localCalibration blocks)),
        OccursAlong (Subgroup.centralizer (ambient.base : Set ambient.A)).subtype
            global.ambientRoot
            (TypeBSpathHonestLocalExtensionSource.centralizerRoot
              (targetData P reference psi w quotient weight localInflation ambient Msys
                quotientCalibration localCalibration blocks))
            global.globalExtension.val nu ↔
          OccursAlong (TypeBHonestCentralizerLocalBinding.centralizerToLocal w ambient)
            extensions.localAmbientRoot
            (TypeBSpathHonestLocalExtensionSource.centralizerRoot
              (targetData P reference psi w quotient weight localInflation ambient Msys
                quotientCalibration localCalibration blocks))
            extensions.localExtension.val nu := by
  let D := targetData P reference psi w quotient weight localInflation ambient Msys
    quotientCalibration localCalibration blocks
  let chi := TypeBHonestGlobalExtensionTripleBinding.globalExtension
    P reference psi w quotient weight localInflation ambient Msys
    quotientCalibration localCalibration blocks global globalRoot
  have calibration : RootResidueCompatible Msys D.ambientRoot :=
    targetData_ambient_residue P reference psi w quotient weight localInflation ambient Msys
      quotientCalibration localCalibration blocks
  obtain ⟨eta, support, intermediate⟩ :=
    certificate.exists_local ambient.A ambient.base
      (AmbientLocalGroup P reference psi w quotient ambient) D
      (baseTheta P reference psi w quotient weight localInflation ambient Msys
        quotientCalibration localCalibration blocks)
      (localPhi P reference psi w quotient weight localInflation ambient Msys
        quotientCalibration localCalibration blocks)
      witness fieldSource O Msys calibration chi
  let extensions := TypeBHonestLocalExtensionPacket.characterExtensions
    P reference psi w quotient weight localInflation ambient Msys
    quotientCalibration localCalibration blocks global eta
  have each : ∀ (J : Subgroup ambient.A) (hNJ : ambient.base ≤ J),
      Nonempty {entry : IntermediateBlockEqualityAt P reference psi w quotient weight
        localInflation ambient extensions J //
          entry.globalRoot = (D.intermediate J hNJ).iota ∧
          entry.localRoot = (D.localIntermediateData J hNJ).iota} := by
    intro J hNJ
    obtain ⟨chiJ, etaJ, globalRestriction, localRestriction, inductionEquality⟩ :=
      intermediate J hNJ
    exact ⟨⟨TypeBHonestIntermediateBlockBinding.intermediateBlockEqualityAt
      fieldSource extensions D J hNJ chiJ etaJ
      globalRestriction localRestriction inductionEquality, rfl, rfl⟩⟩
  let selected (J : Subgroup ambient.A) (hNJ : ambient.base ≤ J) :=
    Classical.choice (each J hNJ)
  let all : IntermediateBlockSource P reference psi w quotient weight
      localInflation ambient extensions :=
    ⟨fun J hNJ => (selected J hNJ).val⟩
  refine ⟨extensions, rfl, rfl, rfl, all, ?_, ?_⟩
  · intro J hNJ
    exact (selected J hNJ).property
  · intro nu
    have actualMap := TypeBHonestCentralizerLocalBinding.centralizerToLocal_eq_witness
      w ambient D witness
    have result := support nu
    rw [← actualMap] at result
    have globalValue := TypeBHonestGlobalExtensionTripleBinding.globalExtension_val
      P reference psi w quotient weight localInflation ambient Msys
      quotientCalibration localCalibration blocks global globalRoot
    have localValue := TypeBHonestLocalExtensionPacket.characterExtensions_local_value
      P reference psi w quotient weight localInflation ambient Msys
      quotientCalibration localCalibration blocks global eta
    change chi.val.val = global.globalExtension.val.val at globalValue
    change extensions.localExtension.val.val = eta.val.val at localValue
    dsimp only [OccursAlong] at result ⊢
    rw [globalValue] at result
    rw [localValue]
    exact result

end ModularRep.PaperProofs.TypeBHonestRootedSpathLocalExtension


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
