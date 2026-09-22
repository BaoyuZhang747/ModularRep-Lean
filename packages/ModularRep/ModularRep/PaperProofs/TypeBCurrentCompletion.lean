import ModularRep.PaperProofs.TypeBCurrentTwoInputs
import ModularRep.PaperProofs.TypeBCurrentOddInputs
import ModularRep.PaperProofs.TypeBCurrentDefiningCharacteristic
import ModularRep.PaperProofs.TypeBCurrentPrimeCases
import ModularRep.PaperProofs.TypeBCurrentCertificate

/-!
# Complete prime coverage for the current odd-field type B theorem

The four branches are computed from the actual defining characteristic,
field order, rank and prime. Defining characteristic and odd nondefining
primes use the complete family proofs on their actual chosen covers. At
two, the generic proof constructs the full family on matrix Omega, while
the exceptional q=3 branch retains all nine blocks in their original
central character quotient presentations.

The source package contains each branch's subordinate inputs only under
its numerical guard. All four certificates are outputs of their proofs.
This file neither postulates an all-prime condition nor converts the q=3
natural presentation to an unproved complete-family presentation.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBCurrentCompletion

open ModularRep TypeBCliffordCarriers TypeBCurrentCertificate
open TypeBQ3TripleCoverCarrier TypeBProposition44SelectedCover
open TypeBCliffordOrthogonalSourceBinding

set_option genInjectivity false
set_option genSizeOfSpec false

/-- Coefficients and the exact dependent q=3 construction inputs. The
simple-group coordinate is the actual matrix group used by the caller. -/
structure ExceptionalInputs (S : Type) [Group S] where
  k : Type
  K : Type
  O : Type
  [fieldk : Field k]
  [fieldK : Field K]
  [ringO : CommRing O]
  [domainO : IsDomain O]
  [algebraO : Algebra O K]
  [chark : CharP k 2]
  [closedk : IsAlgClosed k]
  [zeroK : CharZero K]
  [finiteX : Finite X]
  [rootsX : HasEnoughRootsOfUnity K (Nat.card X)]
  matrixSource : MatrixExceptionalSource
  freeSource : TypeBExceptionalCanonicalCover.FreePresentationCoverSource
  data : TypeBCurrentQ3Inputs.Inputs (k := k) (K := K) (O := O)
    (matrixSource := matrixSource) (freeSource := freeSource)
  base : G3 ≃* S

set_option genInjectivity true
set_option genSizeOfSpec true

attribute [instance] ExceptionalInputs.fieldk ExceptionalInputs.fieldK
  ExceptionalInputs.ringO ExceptionalInputs.domainO ExceptionalInputs.algebraO
  ExceptionalInputs.chark ExceptionalInputs.closedk ExceptionalInputs.zeroK
  ExceptionalInputs.rootsX

/-- The nine-block criterion is obtained from the retained proof, then
placed in its own constructor without any change of local presentation. -/
theorem ExceptionalInputs.complete {S : Type} [Group S]
    (inputs : ExceptionalInputs S) : Nonempty (IBAWCertificate S 2) := by
  letI : Finite X := inputs.finiteX
  exact ⟨.q3 inputs.matrixSource inputs.freeSource inputs.data.before inputs.base inputs.data.allBlocks⟩

variable {n p f ell : ℕ} {F : Type} [Field F] [Finite F] [CharP F p]
  [Finite (SpecialClifford n F)] [NeZero f]
  (parameters : OddFieldParameters F p f) (rank : 3 ≤ n)
  (N : NormSource n F)
  (C : TypeBCliffordOrthogonalSourceBinding.Source n F p f parameters rank N)

local instance spinFintype : Fintype (Spin n F N) := Fintype.ofFinite _

set_option genInjectivity false
set_option genSizeOfSpec false

/-- Each source package is required only for its actual numerical case.
The divisor is on the independently defined matrix Omega group. -/
structure Inputs (ell : ℕ) (prime : Nat.Prime ell)
    (divides : ell ∣ Nat.card (TypeBOrthogonalOmegaCarriers.Omega n F)) where
  defining : ell = p → TypeBCurrentDefiningCharacteristic.DefiningInputs parameters rank N C
  odd : ∀ odd : Odd ell, ∀ nondefining : ¬ ell ∣ Nat.card F,
    TypeBCurrentOddInputs.Inputs parameters rank N C ell odd nondefining divides
  twoGeneric : ell = 2 → (n, Nat.card F) ≠ (3, 3) →
    TypeBCurrentTwoInputs.Inputs parameters rank N C
  twoExceptional : ell = 2 → (n, Nat.card F) = (3, 3) →
    ExceptionalInputs (TypeBOrthogonalOmegaCarriers.Omega n F)

set_option genInjectivity true
set_option genSizeOfSpec true

/-- Current Proposition 4.14 directly at two. Both actual all-block
presentations are retained, without imposing a separate order-divisor
premise on this result. -/
theorem primeTwo
    (generic : (n, Nat.card F) ≠ (3, 3) → TypeBCurrentTwoInputs.Inputs parameters rank N C)
    (exceptional : (n, Nat.card F) = (3, 3) →
      ExceptionalInputs (TypeBOrthogonalOmegaCarriers.Omega n F)) :
    Nonempty (IBAWCertificate (TypeBOrthogonalOmegaCarriers.Omega n F) 2) := by
  classical
  by_cases same : (n, Nat.card F) = (3, 3)
  · exact (exceptional same).complete
  · let source := generic same
    obtain ⟨witness⟩ := source.complete same
    exact ⟨.family source.family source.cover (MulEquiv.refl _) witness⟩

/-- Current Theorem 4.1, with the exact four-way prime and cover split.
Every branch calls its established source application. -/
theorem complete (prime : Nat.Prime ell)
    (divides : ell ∣ Nat.card (TypeBOrthogonalOmegaCarriers.Omega n F))
    (inputs : Inputs parameters rank N C ell prime divides) :
    Nonempty (IBAWCertificate (TypeBOrthogonalOmegaCarriers.Omega n F) ell) := by
  classical
  cases TypeBCurrentPrimeCases.classify parameters n prime with
  | defining same =>
      subst ell
      let source := inputs.defining rfl
      obtain ⟨witness⟩ := source.complete
      exact ⟨.family source.family source.facts.actualCover (MulEquiv.refl _) witness⟩
  | oddNondefining odd different nondefining coverCases exceptionalNondefining =>
      exact (inputs.odd odd nondefining).complete
  | twoGeneric same nondefining generic =>
      subst ell
      let source := inputs.twoGeneric rfl generic
      obtain ⟨witness⟩ := source.complete generic
      exact ⟨.family source.family source.cover (MulEquiv.refl _) witness⟩
  | twoExceptional same nondefining exceptional definingPrime exponent =>
      subst ell
      exact (inputs.twoExceptional rfl exceptional).complete

/-- Quantify the proved prime split over precisely the prime divisors of
the same actual matrix group. No additional group-order formula is used. -/
theorem allPrimes
    (sources : ∀ (ell : ℕ) (prime : Nat.Prime ell)
      (divides : ell ∣ Nat.card (TypeBOrthogonalOmegaCarriers.Omega n F)),
      Inputs parameters rank N C ell prime divides) :
    AllPrimeIBAW (TypeBOrthogonalOmegaCarriers.Omega n F) := by
  intro ell prime divides
  exact complete parameters rank N C prime divides (sources ell prime divides)

end ModularRep.PaperProofs.TypeBCurrentCompletion


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
