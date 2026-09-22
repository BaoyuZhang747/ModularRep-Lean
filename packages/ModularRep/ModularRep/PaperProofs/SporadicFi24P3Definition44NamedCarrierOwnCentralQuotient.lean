import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientRoot
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBrauerKernel
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralKernelGroup
import ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily

/-! Each character's own central quotient and actual deflated Brauer character.
The quotient is fixed by centre intersect kernel of its own chosen affording
representation. No quotient character, root agreement or central-faithfulness
source is assumed. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnCentralQuotient

open ModularRep ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientRoot
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBrauerKernel
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralKernelGroup

universe u
variable (P : Definition35Problem.{u}) (psi : Definition35Brauer P)

def ownQuotientRepresentation :=
  QuotientGroup.lift (centralCharacterKernel P psi) (chosenBrauerRepresentation P psi).ρ
    (show centralCharacterKernel P psi ≤ (chosenBrauerRepresentation P psi).ρ.ker from inf_le_right)

theorem ownQuotientRepresentation_pullback :
    Representation.pullback (ownQuotientRepresentation P psi) (centralCharacterQuotientMap P psi) =
      (chosenBrauerRepresentation P psi).ρ := by
  ext x v
  rfl

theorem ownQuotientRepresentation_irreducible :
    Representation.IsIrreducible (ownQuotientRepresentation P psi) := by
  apply (Representation.isIrreducible_pullback_iff (ownQuotientRepresentation P psi)
    (centralCharacterQuotientMap P psi) (QuotientGroup.mk'_surjective _)).mp
  rw [ownQuotientRepresentation_pullback]
  exact (Classical.choose_spec psi.1.2).1

def ownQuotientBrauer : IBr (quotientRoot P.iota (centralCharacterKernel P psi)) :=
  ⟨Representation.brauerCharacterOfRootEmbedding (ownQuotientRepresentation P psi)
      (quotientRoot P.iota (centralCharacterKernel P psi)),
    ⟨FDRep.of (ownQuotientRepresentation P psi),
      by simpa only [FDRep.of_ρ'] using ownQuotientRepresentation_irreducible P psi, rfl⟩⟩

theorem ownQuotientBrauer_inflation :
    PrimeRegularClassFunction.pullback (centralCharacterQuotientMap P psi)
      (ownQuotientBrauer P psi).1 = psi.1.1 := by
  change PrimeRegularClassFunction.pullback (centralCharacterQuotientMap P psi)
      (Representation.brauerCharacterOfRootEmbedding (ownQuotientRepresentation P psi)
        (quotientRoot P.iota (centralCharacterKernel P psi))) = psi.1.1
  rw [← Representation.brauerCharacterOfRootEmbedding_pullback_of_compatible
    (ownQuotientRepresentation P psi) (quotientRoot P.iota (centralCharacterKernel P psi))
    P.iota (centralCharacterQuotientMap P psi)
    (quotientRoot_compatible P.iota (centralCharacterKernel P psi) (ownQuotientRepresentation P psi))]
  rw [ownQuotientRepresentation_pullback]
  exact (chosenBrauerRepresentation_character P psi).symm

theorem ownQuotientBrauer_centralFaithful [Group.IsPerfect P.H] :
    Subgroup.center (CentralCharacterQuotient P psi) ⊓
      (chosenIBrRepresentation (quotientRoot P.iota (centralCharacterKernel P psi))
        (ownQuotientBrauer P psi)).ρ.ker = ⊥ := by
  have hker := fdRep_ker_eq_of_brauer_eq
    (quotientRoot P.iota (centralCharacterKernel P psi))
    (chosenIBrRepresentation (quotientRoot P.iota (centralCharacterKernel P psi))
      (ownQuotientBrauer P psi))
    (FDRep.of (ownQuotientRepresentation P psi))
    (Classical.choose_spec (ownQuotientBrauer P psi).2).1
    (by simpa only [FDRep.of_ρ'] using ownQuotientRepresentation_irreducible P psi)
    (chosenIBrRepresentation_character (quotientRoot P.iota (centralCharacterKernel P psi))
      (ownQuotientBrauer P psi)).symm
  rw [hker]
  exact centralFaithful_of_factorization (chosenBrauerRepresentation P psi).ρ
    (centralCharacterKernel P psi) rfl (ownQuotientRepresentation P psi) (fun _ => rfl)

def ownCentralQuotientBrauerSource [Group.IsPerfect P.H] :
    CentralQuotientBrauerSource P psi psi where
  iota := quotientRoot P.iota (centralCharacterKernel P psi)
  brauer := ownQuotientBrauer P psi
  irreducibleBrauerInjective := irreducibleBrauerCharacterInjectivity_of_rootEmbedding _
  centralFaithful := ownQuotientBrauer_centralFaithful P psi
  inflation := ownQuotientBrauer_inflation P psi

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnCentralQuotient


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
