import ModularRep.PaperProofs.TypeBFullBlockCondition
import ModularRep.PaperProofs.TypeBCurrentQ3Inputs

/-!
# Fixed complete iBAW certificates on an actual simple carrier

The two constructors retain the two complete presentations already proved
in the current Type B work: a full Definition 3.5 family witness on its
specified universal prime-to-ell cover, or the exceptional q=3 nine-block
certificate in its original natural quotient presentations. No conversion
between these presentations and no arbitrary result predicate is assumed.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBCurrentCertificate

open ModularRep
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family TypeBFullBlockCondition
open TypeBQ3TripleCoverCarrier

/-- Complete evidence with its exact simple-group coordinate. The q=3
constructor keeps the original root, modular system and natural block
presentations through BeforeInputs and AllBlocksCertificate. -/
inductive IBAWCertificate (S : Type) [Group S] : ℕ → Type 1
  | family {ell : ℕ} (family : Definition35Family ell)
      (cover : EllPrimeCoverSource ell family.H)
      (base : cover.S ≃* S) (witness : FamilyWitness family cover) : IBAWCertificate S ell
  | q3 {k K O : Type} [Field k] [Field K] [CommRing O] [IsDomain O]
      [Algebra O K] [CharP k 2] [IsAlgClosed k] [CharZero K]
      [Finite X] [HasEnoughRootsOfUnity K (Nat.card X)]
      (matrixSource : MatrixExceptionalSource)
      (freeSource : TypeBExceptionalCanonicalCover.FreePresentationCoverSource)
      (before : TypeBCurrentQ3Inputs.BeforeInputs (k := k) (K := K) (O := O)
        matrixSource freeSource)
      (base : G3 ≃* S) (witness : TypeBCurrentQ3Inputs.AllBlocksCertificate before) :
      IBAWCertificate S 2

namespace IBAWCertificate

/-- Transport only the simple-group coordinate. The covering carrier,
root conventions, complete family or q=3 presentations remain unchanged. -/
def along {S T : Type} [Group S] [Group T] {ell : ℕ}
    (e : S ≃* T) (certificate : IBAWCertificate S ell) : IBAWCertificate T ell := by
  cases certificate with
  | family family cover base witness =>
      exact .family family cover (base.trans e) witness
  | q3 matrixSource freeSource before base witness =>
      exact .q3 matrixSource freeSource before (base.trans e) witness

end IBAWCertificate

/-- Fixed all-prime condition, quantified over the actual finite group
order, with no caller-selected notion of goodness. -/
def AllPrimeIBAW (S : Type) [Group S] : Prop :=
  ∀ ell : ℕ, Nat.Prime ell → ell ∣ Nat.card S → Nonempty (IBAWCertificate S ell)

/-- Isomorphic finite groups have the same prime divisors, and the
complete certificate follows by changing its exact base coordinate. -/
theorem AllPrimeIBAW.along {S T : Type} [Group S] [Group T]
    (e : S ≃* T) (complete : AllPrimeIBAW S) : AllPrimeIBAW T := by
  intro ell prime divides
  have order : Nat.card S = Nat.card T := Nat.card_congr e.toEquiv
  obtain ⟨certificate⟩ := complete ell prime (order.symm ▸ divides)
  exact ⟨certificate.along e⟩

end ModularRep.PaperProofs.TypeBCurrentCertificate


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
