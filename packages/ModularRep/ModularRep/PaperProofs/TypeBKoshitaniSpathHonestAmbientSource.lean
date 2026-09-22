import ModularRep.PaperProofs.SpathPositiveQTopBlockChoice
import ModularRep.PaperProofs.TypeBCentralKernelPairSplittingBinding
import ModularRep.BrauerCharacterHomPullback

/-!
# The narrow KS3.4 modular ambient and its same-system Brauer character

Koshitani--Spath (2016), Lemma 3.4, pp. 783--784, local primary
extraction lines 299--339, constructs a finite ambient and an honest
modular representation extension of a centrally faithful Brauer character
of a finite p'-covering group. The source has no odd-prime, cyclic-defect,
weight, local-extension, intermediate-block or iBAW hypothesis/conclusion.

`ModularExistenceCertificate` is an exact one-way source TYPE, with no
inhabitant or added logical primitive. The covering map and its group hypotheses are
literal. Its output reuses `SpathAmbientGroup`, including the natural
conjugation quotient, and extends the character's already chosen modular
representation. It neither supplies nor assumes a Brauer extension root.

The paper's sufficiently large modular system (lines 151--155) and its
modular-representation/character interpretation remain the stated E1
dictionary for the E2 theorem. `SpathCoefficientField` retains the modular
field scope. The deductions below construct the characteristic-zero
Brauer values from the SAME actual `Msys` roots. No ordinary algebraic
closure or new-ambient ordinary splitting instance is introduced.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBKoshitaniSpathHonestAmbientSource

open ModularRep
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family
open EvenFieldFLZBAWGoodFamily SpathPositiveQTopBlockChoice
open TypeBLocalReductionInstantiation TypeBModularGroupRootBinding

variable (P : Definition35Problem.{0})
  (reference psi : Definition35Brauer P)
  (quotient : CentralQuotientBrauerSource P reference psi)

/-- The base representation is the existing chosen representation, through
the SAME quotient-to-base equivalence used by the natural ambient action. -/
def baseRepresentation (ambient : SpathAmbientGroup P reference psi quotient) :
    FDRep P.k ambient.base :=
  FDRep.of (Representation.pullback
    (chosenIBrRepresentation quotient.iota quotient.brauer).ρ
    ambient.baseEquiv.symm.toMonoidHom)

/-- Irreducibility is extracted from the character and transported formally. -/
theorem baseRepresentation_irreducible
    (ambient : SpathAmbientGroup P reference psi quotient) :
    Representation.IsIrreducible
      (baseRepresentation P reference psi quotient ambient).ρ := by
  change Representation.IsIrreducible
    (Representation.pullback (chosenIBrRepresentation quotient.iota quotient.brauer).ρ
      ambient.baseEquiv.symm.toMonoidHom)
  have hirr : Representation.IsIrreducible
      (chosenIBrRepresentation quotient.iota quotient.brauer).ρ :=
    (Classical.choose_spec quotient.brauer.2).1
  exact Representation.IsIrreducible.pullback hirr
    ambient.baseEquiv.symm.toMonoidHom ambient.baseEquiv.symm.surjective

/-- The transported chosen representation affords the prescribed base
character, rather than a new independently selected Brauer character. -/
theorem baseRepresentation_affords
    (ambient : SpathAmbientGroup P reference psi quotient) :
    Representation.brauerCharacterOfRootEmbedding
        (baseRepresentation P reference psi quotient ambient).ρ
        (quotient.iota.alongMulEquiv ambient.baseEquiv) =
      (IrreducibleBrauerCharacter.alongMulEquiv
        quotient.iota ambient.baseEquiv quotient.brauer).val := by
  change Representation.brauerCharacterOfRootEmbedding
      (Representation.pullback (chosenIBrRepresentation quotient.iota quotient.brauer).ρ
        ambient.baseEquiv.symm.toMonoidHom)
      (quotient.iota.alongMulEquiv ambient.baseEquiv) =
    PrimeRegularClassFunction.pullback ambient.baseEquiv.symm.toMonoidHom
      quotient.brauer.val
  rw [Representation.brauerCharacterOfRootEmbedding_pullback_mulEquiv,
    ← chosenIBrRepresentation_character quotient.iota quotient.brauer]

/-- KS2016 Lemma 3.4 at modular-representation level. The simple quotient
need not be a new maximal-cover object. The centre-faithfulness hypothesis
uses exactly the representation extended in the output. All fields of the
natural ambient action are retained through the existing output carrier. -/
structure ModularExistenceCertificate : Prop where
  exists_ambient : ∀ (P : Definition35Problem.{0})
      (reference psi : Definition35Brauer P)
      (quotient : CentralQuotientBrauerSource P reference psi)
      (fieldScope : SpathCoefficientField P.p P.k P.iota.prime)
      (S : Type) [Group S] [Finite S]
      (nu : CentralCharacterQuotient P reference →* S)
      (surjective : Function.Surjective nu)
      (kernel : nu.ker = Subgroup.center (CentralCharacterQuotient P reference))
      (perfect : commutator (CentralCharacterQuotient P reference) = ⊤)
      (simple : IsSimpleGroup S) (nonabelian : ¬ IsMulCommutative S)
      (centerPrimeTo : ¬ P.p ∣ Nat.card
        (Subgroup.center (CentralCharacterQuotient P reference)))
      (centralFaithful :
        Subgroup.center (CentralCharacterQuotient P reference) ⊓
          (chosenIBrRepresentation quotient.iota quotient.brauer).ρ.ker = ⊥),
    ∃ ambient : SpathAmbientGroup P reference psi quotient,
      Nonempty (Representation.Extension ambient.base
        (baseRepresentation P reference psi quotient ambient).ρ)

variable {O : Type} [CommRing O] [IsDomain O] [Algebra O P.K]
  (Msys : ModularSystem P.p P.K O P.k)
  (calibration : RootResidueCompatible Msys quotient.iota)

include calibration in
/-- The actual transported base root is the same modular-system convention. -/
theorem baseRoot_eq_groupRoot
    (ambient : SpathAmbientGroup P reference psi quotient) :
    quotient.iota.alongMulEquiv ambient.baseEquiv =
      groupRoot Msys ambient.base := by
  apply eq_groupRoot_of_residue Msys ambient.base
  exact TypeBCentralKernelPairSplittingBinding.alongMulEquiv_residue
    Msys quotient.iota calibration ambient.baseEquiv

include calibration in
/-- Compatibility for any modular extension on the literal base inclusion.
It is proved after the ambient is obtained, not placed in the source type. -/
theorem extensionRoot_compatible
    (ambient : SpathAmbientGroup P reference psi quotient)
    (extension : Representation.Extension ambient.base
      (baseRepresentation P reference psi quotient ambient).ρ) :
    Representation.BrauerRootLiftCompatibleAlong extension.representation
      (groupRoot Msys ambient.A)
      (quotient.iota.alongMulEquiv ambient.baseEquiv) ambient.base.subtype := by
  rw [baseRoot_eq_groupRoot P reference psi quotient Msys calibration ambient]
  exact groupRoot_compatible_along Msys extension.representation ambient.base.subtype

/-- An honest modular extension yields the existing global output packet
at the constructed ambient root, with the prescribed base character. -/
def globalExtensionData
    (ambient : SpathAmbientGroup P reference psi quotient)
    (extension : Representation.Extension ambient.base
      (baseRepresentation P reference psi quotient ambient).ρ) :
    ChosenGlobalExtensionData ambient where
  ambientRoot := groupRoot Msys ambient.A
  globalExtension := Representation.Extension.brauerCharacterExtensionWitnessOfCompatible
    extension (baseRepresentation_irreducible P reference psi quotient ambient)
    (groupRoot Msys ambient.A) (quotient.iota.alongMulEquiv ambient.baseEquiv)
    (IrreducibleBrauerCharacter.alongMulEquiv
      quotient.iota ambient.baseEquiv quotient.brauer)
    (baseRepresentation_affords P reference psi quotient ambient)
    (extensionRoot_compatible P reference psi quotient Msys calibration ambient extension)

theorem globalExtensionData_root
    (ambient : SpathAmbientGroup P reference psi quotient)
    (extension : Representation.Extension ambient.base
      (baseRepresentation P reference psi quotient ambient).ρ) :
    (globalExtensionData P reference psi quotient Msys calibration ambient extension).ambientRoot =
      groupRoot Msys ambient.A := rfl

/-- Inflation along the original quotient-to-ambient embedding is literal. -/
theorem globalExtensionData_restricts
    (ambient : SpathAmbientGroup P reference psi quotient)
    (extension : Representation.Extension ambient.base
      (baseRepresentation P reference psi quotient ambient).ρ) :
    PrimeRegularClassFunction.pullback (quotientToAmbient P reference psi quotient ambient)
        (globalExtensionData P reference psi quotient Msys calibration ambient extension).globalExtension.1.val =
      quotient.brauer.val := by
  apply PrimeRegularClassFunction.ext
  intro x
  have h := congrArg
    (fun f : PrimeRegularClassFunction P.K ambient.base P.p =>
      f (PrimeRegularElement.map ambient.baseEquiv.toMonoidHom x))
    (globalExtensionData P reference psi quotient Msys calibration ambient extension).globalExtension.2
  change
    (globalExtensionData P reference psi quotient Msys calibration ambient extension).globalExtension.1.val
        (PrimeRegularElement.map (quotientToAmbient P reference psi quotient ambient) x) = _
  change
    (globalExtensionData P reference psi quotient Msys calibration ambient extension).globalExtension.1.val
        (PrimeRegularElement.map (quotientToAmbient P reference psi quotient ambient) x) =
      quotient.brauer.val
        (PrimeRegularElement.map ambient.baseEquiv.symm.toMonoidHom
          (PrimeRegularElement.map ambient.baseEquiv.toMonoidHom x)) at h
  have hx : PrimeRegularElement.map ambient.baseEquiv.symm.toMonoidHom
      (PrimeRegularElement.map ambient.baseEquiv.toMonoidHom x) = x := by
    apply Subtype.ext
    exact ambient.baseEquiv.symm_apply_apply x.val
  rw [hx] at h
  exact h

include calibration in
/-- Root agreement on the original quotient's finite domain. No equality
of full lift functions on groups of different orders is assumed. -/
theorem quotientRoot_agrees
    (ambient : SpathAmbientGroup P reference psi quotient)
    (zeta : rootsOfUnity
      (primeRegularExponent P.p (CentralCharacterQuotient P reference)) P.k) :
    quotient.iota.lift ((zeta : P.kˣ) : P.k) =
      (groupRoot Msys ambient.A).lift ((zeta : P.kˣ) : P.k) := by
  rw [eq_groupRoot_of_residue Msys
    (CentralCharacterQuotient P reference) quotient.iota calibration]
  apply groupRoot_agrees_of_dvd Msys ambient.A
    (CentralCharacterQuotient P reference)
  change ordCompl[P.p] (Nat.card (CentralCharacterQuotient P reference)) ∣
    ordCompl[P.p] (Nat.card ambient.A)
  apply Nat.ordCompl_dvd_ordCompl_of_dvd
  rw [Nat.card_congr ambient.baseEquiv.toEquiv]
  exact Subgroup.card_subgroup_dvd_card ambient.base

include calibration in
/-- Apply the modular source and construct its Brauer-root dictionary. -/
theorem exists_ambient_global
    (certificate : ModularExistenceCertificate)
    (fieldScope : SpathCoefficientField P.p P.k P.iota.prime)
    (S : Type) [Group S] [Finite S]
    (nu : CentralCharacterQuotient P reference →* S)
    (surjective : Function.Surjective nu)
    (kernel : nu.ker = Subgroup.center (CentralCharacterQuotient P reference))
    (perfect : commutator (CentralCharacterQuotient P reference) = ⊤)
    (simple : IsSimpleGroup S) (nonabelian : ¬ IsMulCommutative S)
    (centerPrimeTo : ¬ P.p ∣ Nat.card
      (Subgroup.center (CentralCharacterQuotient P reference))) :
    ∃ ambient : SpathAmbientGroup P reference psi quotient,
      ∃ global : ChosenGlobalExtensionData ambient,
        global.ambientRoot = groupRoot Msys ambient.A := by
  obtain ⟨ambient, ⟨extension⟩⟩ := certificate.exists_ambient P reference psi quotient
    fieldScope S nu surjective kernel perfect simple nonabelian centerPrimeTo
    quotient.centralFaithful
  exact ⟨ambient,
    globalExtensionData P reference psi quotient Msys calibration ambient extension, rfl⟩

/-- The existing fixed-quotient cover packet supplies exactly the raw
covering hypotheses. Its original cover's maximality is not consumed. -/
theorem exists_ambient_global_of_quotientCover
    {p : ℕ} (family : Definition35Family.{0} p)
    (cover : EllPrimeCoverSource p family.H) (block : family.Block)
    (reference psi : Definition35Brauer (family.problem block))
    (quotient : CentralQuotientBrauerSource (family.problem block) reference psi)
    (quotientCover : CentralQuotientCoverSource family cover block reference)
    {O : Type} [CommRing O] [IsDomain O] [Algebra O family.K]
    (Msys : ModularSystem p family.K O family.k)
    (calibration : RootResidueCompatible Msys quotient.iota)
    (fieldScope : SpathCoefficientField p family.k family.ellPrime)
    (certificate : ModularExistenceCertificate) :
    ∃ ambient : SpathAmbientGroup (family.problem block) reference psi quotient,
      ∃ global : ChosenGlobalExtensionData ambient,
        global.ambientRoot = groupRoot Msys ambient.A := by
  letI : Algebra O (family.problem block).K :=
    (inferInstance : Algebra O family.K)
  exact exists_ambient_global (family.problem block) reference psi quotient Msys calibration
    certificate fieldScope cover.S quotientCover.quotientToSimple
    quotientCover.quotientToSimple_surjective quotientCover.quotient_kernel
    quotientCover.perfect cover.simple cover.nonabelian quotientCover.centerPrimeTo

end ModularRep.PaperProofs.TypeBKoshitaniSpathHonestAmbientSource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
