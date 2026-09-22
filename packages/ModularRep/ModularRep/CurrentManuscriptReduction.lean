import ModularRep.PaperProofs.TypeBCurrentCensus
import ModularRep.PaperProofs.TypeBCurrentTheorem
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedSporadicAssembly
import ModularRep.CurrentSpathDescent

/-!
# Current introduction: the three families and the finite group reduction

The common conclusion types retain complete family and exceptional rank
three certificates and sporadic Definition 4.1 certificates with compatible
root conventions. The manuscript application constructs the three family
branches and applies the finite group reduction using these types.

An involved simple group is represented by an actual quotient U/N of a
subgroup U of the finite group. Spath's published reduction is an explicit
E2 source on those concrete sections. Its fixed conclusion is the equality
of the literal Brauer and weight fibre cardinalities in every specified
block. No headline, family-goal, involvedness or AWC predicate is supplied.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.CurrentManuscriptReduction

open Formalisation ModularRep CharacterWeight FDRepSimpleClassKZero
open Formalisation.DependencyCases
open ModularRep.PaperProofs
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family TypeBFullBlockCondition
open TypeBCurrentCertificate
open OddTwoConformalProjectiveRealisation (PSp)
open SporadicFi24P3Definition44NamedCarrierAcceleratedNamedModels

universe v w

/-- The accepted concrete presentations of the complete inductive
condition. Neither constructor changes an existing character/weight map. -/
inductive MainCertificate (S : Type) [Group S] : ℕ → Type 1
  | established {ell : ℕ} (certificate : IBAWCertificate S ell) : MainCertificate S ell
  | sporadic {ell : ℕ} (base : NamedBase.{0}) (model : CaseModel base ell)
      (coordinate : base.S ≃* S) (certificate : CaseConclusion model) : MainCertificate S ell

def MainCertificate.along {S T : Type} [Group S] [Group T] {ell : ℕ}
    (e : S ≃* T) (certificate : MainCertificate S ell) : MainCertificate T ell := by
  cases certificate with
  | established c => exact .established (c.along e)
  | sporadic base model coordinate certificate =>
      exact .sporadic base model (coordinate.trans e) certificate

def AllPrimeMain (S : Type) [Group S] : Prop :=
  ∀ ell : ℕ, Nat.Prime ell → ell ∣ Nat.card S → Nonempty (MainCertificate S ell)

theorem AllPrimeMain.along {S T : Type} [Group S] [Group T]
    (e : S ≃* T) (complete : AllPrimeMain S) : AllPrimeMain T := by
  intro ell prime divides
  have order : Nat.card S = Nat.card T := Nat.card_congr e.toEquiv
  obtain ⟨c⟩ := complete ell prime (order.symm ▸ divides)
  exact ⟨c.along e⟩

/-- Exact theorem argument supplied by the separately proved odd-field
Type B all-prime theorem. The ordinary full-family and exceptional q=3
presentations remain those of its existing certificate type. -/
def TypeBTheorem : Prop :=
  ∀ (n p : ℕ) (F : Type) [Field F] [Finite F] [CharP F p],
    3 ≤ n → Odd p → AllPrimeIBAW (TypeBOrthogonalOmegaCarriers.Omega n F)

/-- Raw original-field/norm/Clifford and prime-branch sources. There is
no completed Type B conclusion in this source telescope. -/
def TypeBInputs : Type 1 :=
  ∀ (n p : ℕ) (F : Type) [Field F] [Finite F] [CharP F p]
    (rank : 3 ≤ n), Odd p → TypeBCurrentTheorem.OddHighInputs n p F rank

/-- Discharge the intermediate theorem argument with the actual current
prime dispatcher. The final user endpoints below call this theorem. -/
theorem typeB_theorem_from_sources (raw : TypeBInputs) : TypeBTheorem := by
  intro n p F _ _ _ rank odd
  exact (raw n p F rank odd).complete

/-- The numerical branch selector determines the subordinate Type C data. -/
def TypeCInputs : Type 1 :=
  ∀ (n p ell : ℕ) (F : Type) [Field F] [Finite F] [CharP F p]
    (prime : Nat.Prime ell) (rank : 2 ≤ n)
    (notSmall : ¬ (n = 2 ∧ Nat.card F = 2)),
    ell ∣ Nat.card (PSp n F) →
      TypeCCurrentAllCaseSourceApplication.SourceInputs n p ell F prime rank notSmall

theorem typeC_complete (sources : TypeCInputs)
    (n p : ℕ) (F : Type) [Field F] [Finite F] [CharP F p]
    (rank : 2 ≤ n) (notSmall : ¬ (n = 2 ∧ Nat.card F = 2)) :
    AllPrimeMain (PSp n F) := by
  intro ell prime divides
  let D := sources n p ell F prime rank notSmall divides
  let target := TypeCCurrentAllCaseSourceApplication.actualTarget n p ell F prime rank notSmall D
  obtain ⟨witness⟩ := TypeCCurrentAllCaseSourceApplication.full_block_condition_source_instantiated
    n p ell F prime rank notSmall D divides
  exact ⟨.established (.family target.family target.cover target.simpleEquiv witness)⟩

theorem typeB_complete (proved : TypeBTheorem)
    (n p : ℕ) (F : Type) [Field F] [Finite F] [CharP F p]
    (rank : 3 ≤ n) (odd : Odd p) :
    AllPrimeMain (TypeBOrthogonalOmegaCarriers.Omega n F) := by
  intro ell prime divides
  obtain ⟨c⟩ := proved n p F rank odd ell prime divides
  exact ⟨.established c⟩

/-- Literal group presentations in the three clauses of the headline.
For a finite field, odd defining characteristic is equivalent to odd field
order. The field, characteristic and rank remain in the presentation. -/
inductive MainPresentation (bases : SporadicGroup → NamedBase.{0})
    (S : Type) [Group S] : Type 1
  | typeC (n p : ℕ) (F : Type) [Field F] [Finite F] [CharP F p]
      (rank : 2 ≤ n) (notSmall : ¬ (n = 2 ∧ Nat.card F = 2))
      (coordinate : PSp n F ≃* S) : MainPresentation bases S
  | typeB (n p : ℕ) (F : Type) [Field F] [Finite F] [CharP F p]
      (rank : 3 ≤ n) (odd : Odd p)
      (coordinate : TypeBOrthogonalOmegaCarriers.Omega n F ≃* S) : MainPresentation bases S
  | sporadic (s : SporadicGroup) (coordinate : (bases s).S ≃* S) : MainPresentation bases S

/-- Concrete nonabelian simple sections, not an arbitrary involvedness
predicate. `N` is a normal subgroup of the actual subgroup `U ≤ H`. -/
structure SimpleSection (H : Type) [Group H] where
  U : Subgroup H
  N : Subgroup U
  [normal : N.Normal]
  simple : IsSimpleGroup (U ⧸ N)
  nonabelian : ¬ IsMulCommutative (U ⧸ N)

attribute [instance] SimpleSection.normal

abbrev SimpleSection.Group {H : Type} [Group H] (piece : SimpleSection H) :=
  piece.U ⧸ piece.N

instance SimpleSection.simpleGroup {H : Type} [_root_.Group H] (piece : SimpleSection H) :
    IsSimpleGroup piece.Group := piece.simple

/-- The Type B census includes rank one, rank two and even fields;
the Type C and sporadic alternatives have their actual headline scope. -/
inductive SupportedPresentation (bases : SporadicGroup → NamedBase.{0})
    (S : Type) [Group S] : Type 1
  | typeC (n p : ℕ) (F : Type) [Field F] [Finite F] [CharP F p]
      (rank : 2 ≤ n) (notSmall : ¬ (n = 2 ∧ Nat.card F = 2))
      (coordinate : PSp n F ≃* S) : SupportedPresentation bases S
  | typeB (n p : ℕ) (F : Type) [Field F] [Finite F] [CharP F p]
      (rank : 1 ≤ n)
      (coordinate : TypeBOrthogonalOmegaCarriers.Omega n F ≃* S) : SupportedPresentation bases S
  | sporadic (s : SporadicGroup) (coordinate : (bases s).S ≃* S) : SupportedPresentation bases S

/-- Only subordinate census sources, restricted to actual simple Omega
groups and their actual prime divisors. The high odd branch is supplied
by `TypeBTheorem`, not repeated as an external census premise. -/
def CensusInputs : Type 1 :=
  ∀ (n p ell : ℕ) (F : Type) [Field F] [Finite F] [CharP F p]
    (rank : 1 ≤ n) [IsSimpleGroup (TypeBOrthogonalOmegaCarriers.Omega n F)],
    (¬ IsMulCommutative (TypeBOrthogonalOmegaCarriers.Omega n F)) →
    ∀ prime : Nat.Prime ell,
      ell ∣ Nat.card (TypeBOrthogonalOmegaCarriers.Omega n F) →
        TypeBCurrentCensus.SourceInputs n p ell F prime rank

/-- The ordinary p-prime-to-order case is retained separately from the
three-family census. It requires no statement about unsupported families. -/
inductive SectionEvidence {H : Type} [Group H] (piece : SimpleSection H)
    (ell : ℕ) : Type 1
  | supported (certificate : MainCertificate piece.Group ell) : SectionEvidence piece ell
  | primeTo (order : ¬ ell ∣ Nat.card piece.Group) : SectionEvidence piece ell

/-- The literal blockwise Alperin weight equality in the fixed finite
specified family. `Definition35Brauer` and `Definition35Weight` are actual
Brauer block fibres and conjugacy classes of ordinary defect-zero weights. -/
def BlockwiseAWC {ell : ℕ} (family : Definition35Family.{0} ell) : Prop :=
  ∀ b : family.Block,
    Nat.card (Definition35Brauer (family.problem b)) =
      Nat.card (Definition35Weight (family.problem b))

/-- Exact E2 composite ending in Spath 2013 Theorem A. The antecedent
interpretation retains the three fixed complete presentations above.
For the q=3 natural all-block criterion, the published block-to-global
passage is Koshitani--Spath 2016 Lemma 3.3 together with Spath 2013
Definition 5.17 and Remark 5.18. It makes fresh compatible global choices,
including the Q=1 normalization; it does NOT assert that the existing
per-block quotient presentations are already one syntactic FamilyWitness.
The other constructors already carry full family/Definition 4.1 data.
The standard defect-zero theorem treats sections of order prime to ell.
After those exact antecedent interpretations, Theorem A yields the
literal blockwise counting equality. No caller-chosen result appears. -/
structure SpathReductionSource {ell : ℕ} (family : Definition35Family.{0} ell)
    (physical : CurrentSpathDescent.PhysicalFamilySource family)
    (field : SpathCoefficientField ell family.k family.ellPrime) : Prop where
  reduce : (∀ piece : SimpleSection family.H, Nonempty (SectionEvidence piece ell)) →
    BlockwiseAWC family

end ModularRep.CurrentManuscriptReduction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
