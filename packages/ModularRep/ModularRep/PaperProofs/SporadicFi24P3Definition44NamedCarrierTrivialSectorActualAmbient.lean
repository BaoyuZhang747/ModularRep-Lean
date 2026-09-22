import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorAmbientTransport

/-! Construct the trivial-sector ambient on the literal automorphism
stabilizer of the own quotient, then derive its original-cover interpretation.
Only structural cover data and the actual central-sector equation enter. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorActualAmbient

open ModularRep
open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCoverGroupFacts
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialCentralSector
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralKernelGroup
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnCentralQuotient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientRoot
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalAmbient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorAutomorphismTransport
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorAmbientTransport

universe u

theorem ownQuotient_center_eq_bot
    (P : Definition35Problem.{u}) (psi : Definition35Brauer P) [Group.IsPerfect P.H]
    (hZ0 : centralCharacterKernel P psi = Subgroup.center P.H) :
    Subgroup.center (CentralCharacterQuotient P psi) = ⊥ := by
  rw [center_eq_map_center_of_le_center (centralCharacterKernel P psi) inf_le_left,
    ← hZ0, QuotientGroup.map_mk'_self]

def ownActualAutAmbient
    (P : Definition35Problem.{u}) (psi : Definition35Brauer P) [Group.IsPerfect P.H]
    (hZ0 : centralCharacterKernel P psi = Subgroup.center P.H) :
    SpathAmbientGroup P psi psi (ownCentralQuotientBrauerSource P psi) where
  A := ActualAutAmbient (quotientRoot P.iota (centralCharacterKernel P psi))
    (ownQuotientBrauer P psi)
  fintypeA := Fintype.ofFinite _
  base := actualBase _ (ownQuotientBrauer P psi)
  baseEquiv := actualBaseEquiv _ (ownQuotientBrauer P psi)
    (ownQuotient_center_eq_bot P psi hZ0)
  baseCentralizer_eq_center := by
    rw [actualBase_centralizer_eq_bot _ _ (ownQuotient_center_eq_bot P psi hZ0),
      actualAmbient_center_eq_bot _ _ (ownQuotient_center_eq_bot P psi hZ0)]
  centerPrimeTo := by
    rw [actualAmbient_center_eq_bot _ _ (ownQuotient_center_eq_bot P psi hZ0),
      Subgroup.card_bot]
    exact P.iota.prime.not_dvd_one
  conjugation := actualConjugation _ (ownQuotientBrauer P psi)
  conjugation_on_base := by
    intro a x
    exact innerEmbedding_conjugation _ (ownQuotientBrauer P psi) a x
  automorphismQuotientEquiv := actualAutomorphismQuotientEquiv _
    (ownQuotientBrauer P psi) (ownQuotient_center_eq_bot P psi hZ0)
  automorphismQuotientEquiv_natural :=
    actualAutomorphismQuotientEquiv_natural _ (ownQuotientBrauer P psi)
      (ownQuotient_center_eq_bot P psi hZ0)

def trivialSectorOriginalAmbient
    (P : Definition35Problem.{u}) (psi : Definition35Brauer P)
    {S : Type u} [Group S] (q : P.H →* S)
    (hq : IsUniversalCentralExtension q)
    (hs : IsSimpleGroup S) (hna : ¬ IsMulCommutative S)
    (hcenter : ¬ P.p ∣ Nat.card (Subgroup.center P.H))
    (hglobal : ∀ z : PrimeRegularElement (G := Subgroup.center P.H) P.p,
      psi.1.1 (PrimeRegularElement.map (Subgroup.center P.H).subtype z) =
        psi.1.1 ⟨1, isPrimeRegular_one⟩) : OriginalSpathAmbient P psi :=
  let : Group.IsPerfect P.H := ⟨perfect_of_universalCentralExtension q hq⟩
  ambientOfOwnAut P psi
    (trivialSectorAutEquiv P psi q hq hs hna hcenter hglobal)
    (trivialSectorAutEquiv_square P psi q hq hs hna hcenter hglobal) hcenter
    (ownActualAutAmbient P psi
      (centralCharacterKernel_eq_center_of_trivial_sector P psi hcenter hglobal))

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorActualAmbient


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
