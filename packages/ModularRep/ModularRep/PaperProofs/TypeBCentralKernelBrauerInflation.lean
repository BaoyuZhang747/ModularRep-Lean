import ModularRep.IrreducibleBrauerCharacterSurjectiveDescent
import ModularRep.PrimeRegularRootEmbeddingPQuotient
import ModularRep.PaperProofs.NormalCoreLemma48SourceInstantiation

/-!
# Literal Brauer inflation for the Type B central-kernel application

The representation input is Navarro Lemma 2.32, p. 39, restricted to the
specified normal p-subgroup. Prime regular lifting is the elementary quotient
fact used in the proof of Navarro Theorem 9.11. These are E1 inputs, not
assumed Brauer correspondences. Inflation, representation descent, the root
comparison and the resulting equivalence are constructed using checked APIs.

Centrality is unnecessary here. It is needed for the separate block step.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBCentralKernelBrauerInflation

open IrreducibleBrauerCharacterSurjectiveDescent
open NormalCoreLemma48SourceInstantiation

universe u

variable {p : ℕ} {k K G : Type u}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
  [Group G] [Finite G]

/-- Exact routine input on actual modular representations, with no selected
character or conclusion predicate. -/
def Navarro232Principle (p : ℕ) (k : Type u)
    [Field k] [CharP k p] [IsAlgClosed k] : Prop :=
  ∀ (X : Type u) [Group X] [Finite X] (P : Subgroup X) [P.Normal],
    p.Prime → IsPGroup p P → ∀ V : FDRep k X,
      Representation.IsIrreducible V.ρ → P ≤ V.ρ.ker

/-- Literal prime regular representatives for a finite normal p-quotient.
This elementary input neither selects nor identifies a character. -/
def PrimeRegularQuotientLiftPrinciple (p : ℕ) : Prop :=
  ∀ (X : Type u) [Group X] [Finite X] (P : Subgroup X) [P.Normal],
    p.Prime → IsPGroup p P →
      Function.Surjective (PrimeRegularElement.map (p := p) (QuotientGroup.mk' P))

variable (P : Subgroup G) [P.Normal] (hP : IsPGroup p P)
  (iotaDown : PrimeRegularRootEmbedding p k K (G ⧸ P))

/-- The prescribed downstairs roots determine the upstairs roots. -/
abbrev upRoot : PrimeRegularRootEmbedding p k K G :=
  PrimeRegularRootEmbeddingPQuotient.ofPQuotient P hP iotaDown

theorem root_compatible (V : FDRep k (G ⧸ P)) :
    Representation.BrauerRootLiftCompatibleAlong V.ρ iotaDown
      (upRoot P hP iotaDown) (QuotientGroup.mk' P) := by
  intro g a
  exact PrimeRegularRootEmbeddingPQuotient.ofPQuotient_lift P hP iotaDown a.1

/-- The affording representation supplied by the definition of `IBr` is
trivial on this actual quotient kernel by the normal p-subgroup theorem. -/
def kernelTrivial (source : Navarro232Principle p k)
    (psi : IBr (upRoot P hP iotaDown)) :
    KernelTrivialIBrAlong (QuotientGroup.mk' P) (upRoot P hP iotaDown) := by
  refine ⟨psi, ?_⟩
  obtain ⟨V, hV, hchar⟩ := psi.2
  refine ⟨V, hV, hchar, ?_⟩
  simpa only [QuotientGroup.ker_mk'] using source G P iotaDown.prime hP V hV

/-- Construct all three fields of the existing checked inflation packet;
no character equivalence or character descent is a source premise. -/
theorem inflationInput (source : Navarro232Principle p k)
    (regular : PrimeRegularQuotientLiftPrinciple.{u} p) :
    BrauerInflationInput P iotaDown (upRoot P hP iotaDown) where
  inflatedIrreducible phi := by
    let inflated := inflateToKernelTrivialIBrAlong (QuotientGroup.mk' P)
      (QuotientGroup.mk'_surjective P) (upRoot P hP iotaDown) iotaDown
      (root_compatible P hP iotaDown) phi
    exact inflated.1.2
  descends psi := by
    let psiK := kernelTrivial P hP iotaDown source psi
    refine ⟨descendIBrAlong (QuotientGroup.mk' P)
      (QuotientGroup.mk'_surjective P) (upRoot P hP iotaDown) iotaDown psiK, ?_⟩
    exact descendIBrAlong_pullback (QuotientGroup.mk' P)
      (QuotientGroup.mk'_surjective P) (upRoot P hP iotaDown) iotaDown
      (root_compatible P hP iotaDown) psiK
  regularLift := regular G P iotaDown.prime hP

/-- Actual function-valued inflation is a constructed equivalence. -/
def brauerEquiv (source : Navarro232Principle p k)
    (regular : PrimeRegularQuotientLiftPrinciple.{u} p) :
    IBr iotaDown ≃ IBr (upRoot P hP iotaDown) :=
  (inflationInput P hP iotaDown source regular).equiv

theorem brauerEquiv_val (source : Navarro232Principle p k)
    (regular : PrimeRegularQuotientLiftPrinciple.{u} p) (phi : IBr iotaDown) :
    (brauerEquiv P hP iotaDown source regular phi).1 =
      PrimeRegularClassFunction.pullback (QuotientGroup.mk' P) phi.1 := rfl

theorem brauerEquiv_twist (source : Navarro232Principle p k)
    (regular : PrimeRegularQuotientLiftPrinciple.{u} p)
    (alpha : MulAut G) (beta : MulAut (G ⧸ P))
    (square : ∀ g, QuotientGroup.mk' P (alpha g) = beta (QuotientGroup.mk' P g))
    (phi : IBr iotaDown) :
    brauerEquiv P hP iotaDown source regular
        (IrreducibleBrauerCharacter.twist iotaDown phi beta) =
      IrreducibleBrauerCharacter.twist (upRoot P hP iotaDown)
        (brauerEquiv P hP iotaDown source regular phi) alpha := by
  apply Subtype.ext
  exact pullback_twist (QuotientGroup.mk' P) alpha beta square phi.1

end ModularRep.PaperProofs.TypeBCentralKernelBrauerInflation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
