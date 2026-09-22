import ModularRep.PaperProofs.TypeBCurrentCertificate

/-!
# The full inductive condition on a specified covering family

Every certificate contains the complete family witness on its stated
universal prime-to-ell cover. Changing the simple group coordinate preserves
the covering group, characters, roots and witness. The compatibility map to
the retained certificate uses only its constructor carrying the full family.
-/

noncomputable section
set_option autoImplicit false

namespace ManuscriptIBAW

open ModularRep.PaperProofs
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family TypeBFullBlockCondition

/-- The full inductive condition with its actual simple group coordinate. -/
structure FamilyCertificate (S : Type) [Group S] (ell : ℕ) where
  family : Definition35Family ell
  cover : EllPrimeCoverSource ell family.H
  base : cover.S ≃* S
  witness : FamilyWitness family cover

namespace FamilyCertificate

/-- Change only the simple group coordinate. -/
def along {S T : Type} [Group S] [Group T] {ell : ℕ}
    (e : S ≃* T) (certificate : FamilyCertificate S ell) : FamilyCertificate T ell where
  family := certificate.family
  cover := certificate.cover
  base := certificate.base.trans e
  witness := certificate.witness

/-- Compatibility with the retained certificate, through its full family. -/
def toLegacy {S : Type} [Group S] {ell : ℕ}
    (certificate : FamilyCertificate S ell) : TypeBCurrentCertificate.IBAWCertificate S ell :=
  .family certificate.family certificate.cover certificate.base certificate.witness

end FamilyCertificate

/-- The full family condition at every prime dividing the actual group order. -/
def AllPrimeFamily (S : Type) [Group S] : Prop :=
  ∀ ell : ℕ, Nat.Prime ell → ell ∣ Nat.card S → Nonempty (FamilyCertificate S ell)

theorem AllPrimeFamily.along {S T : Type} [Group S] [Group T]
    (e : S ≃* T) (complete : AllPrimeFamily S) : AllPrimeFamily T := by
  intro ell prime divides
  have order : Nat.card S = Nat.card T := Nat.card_congr e.toEquiv
  obtain ⟨certificate⟩ := complete ell prime (order.symm ▸ divides)
  exact ⟨certificate.along e⟩

/-- Forget the stronger certificate type for a retained consumer. -/
theorem AllPrimeFamily.toLegacy {S : Type} [Group S] (complete : AllPrimeFamily S) :
    TypeBCurrentCertificate.AllPrimeIBAW S := by
  intro ell prime divides
  obtain ⟨certificate⟩ := complete ell prime divides
  exact ⟨certificate.toLegacy⟩

end ManuscriptIBAW

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
this package's formalisation report and source records.
-/
