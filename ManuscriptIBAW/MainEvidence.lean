import ManuscriptIBAW.FamilyCertificate
import ModularRep.CurrentManuscriptReduction

/-!
# Evidence for the main theorem and finite group reduction

The classical alternative contains a full covering family. The sporadic
alternative retains the actual named group, model and Definition 4.1
condition. The finite group reduction is assumed only on these conclusions
and the prime-to-order case for the same actual simple sections.
-/

noncomputable section
set_option autoImplicit false

namespace ManuscriptIBAW.Main

open ModularRep ModularRep.PaperProofs
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family
open SporadicFi24P3Definition44NamedCarrierAcceleratedNamedModels
open ModularRep.CurrentManuscriptReduction (SimpleSection BlockwiseAWC)

/-- Complete classical or sporadic evidence on the specified simple group. -/
inductive MainCertificate (S : Type) [Group S] : ℕ → Type 1
  | established {ell : ℕ} (certificate : FamilyCertificate S ell) : MainCertificate S ell
  | sporadic {ell : ℕ} (base : NamedBase.{0}) (model : CaseModel base ell)
      (coordinate : base.S ≃* S) (certificate : CaseConclusion model) : MainCertificate S ell

def MainCertificate.along {S T : Type} [Group S] [Group T] {ell : ℕ}
    (e : S ≃* T) (certificate : MainCertificate S ell) : MainCertificate T ell := by
  cases certificate with
  | established c => exact .established (c.along e)
  | sporadic base model coordinate witness =>
    exact .sporadic base model (coordinate.trans e) witness

/-- Compatibility preserves the sporadic model and uses the classical family. -/
def MainCertificate.toLegacy {S : Type} [Group S] {ell : ℕ}
    (certificate : MainCertificate S ell) :
    ModularRep.CurrentManuscriptReduction.MainCertificate S ell := by
  cases certificate with
  | established c => exact .established c.toLegacy
  | sporadic base model coordinate witness => exact .sporadic base model coordinate witness

def AllPrimeMain (S : Type) [Group S] : Prop :=
  ∀ ell : ℕ, Nat.Prime ell → ell ∣ Nat.card S → Nonempty (MainCertificate S ell)

theorem AllPrimeMain.along {S T : Type} [Group S] [Group T]
    (e : S ≃* T) (complete : AllPrimeMain S) : AllPrimeMain T := by
  intro ell prime divides
  have order : Nat.card S = Nat.card T := Nat.card_congr e.toEquiv
  obtain ⟨certificate⟩ := complete ell prime (order.symm ▸ divides)
  exact ⟨certificate.along e⟩

/-- Evidence on an actual nonabelian simple quotient of a subgroup. -/
inductive SectionEvidence {H : Type} [Group H] (piece : SimpleSection H)
    (ell : ℕ) : Type 1
  | supported (certificate : MainCertificate piece.Group ell) : SectionEvidence piece ell
  | primeTo (order : ¬ ell ∣ Nat.card piece.Group) : SectionEvidence piece ell

def SectionEvidence.toLegacy {H : Type} [Group H] {piece : SimpleSection H} {ell : ℕ}
    (evidence : SectionEvidence piece ell) :
    ModularRep.CurrentManuscriptReduction.SectionEvidence piece ell := by
  cases evidence with
  | supported certificate => exact .supported certificate.toLegacy
  | primeTo order => exact .primeTo order

/-- Späth's finite group reduction and the prime-to-order case, interpreted
on the specified family and these full simple-section conclusions. -/
structure FiniteGroupReductionSource {ell : ℕ} (family : Definition35Family.{0} ell)
    (physical : CurrentSpathDescent.PhysicalFamilySource family)
    (field : SpathCoefficientField ell family.k family.ellPrime) : Prop where
  reduce : (∀ piece : SimpleSection family.H, Nonempty (SectionEvidence piece ell)) →
    BlockwiseAWC family

/-- The retained, stronger external requirement suffices for this narrower
source. No converse transport is assumed. -/
theorem FiniteGroupReductionSource.ofLegacy {ell : ℕ} (family : Definition35Family.{0} ell)
    (physical : CurrentSpathDescent.PhysicalFamilySource family)
    (field : SpathCoefficientField ell family.k family.ellPrime)
    (source : ModularRep.CurrentManuscriptReduction.SpathReductionSource family physical field) :
    FiniteGroupReductionSource family physical field where
  reduce hypotheses := source.reduce fun piece => (hypotheses piece).map SectionEvidence.toLegacy

end ManuscriptIBAW.Main

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
this package's formalisation report and source records.
-/
