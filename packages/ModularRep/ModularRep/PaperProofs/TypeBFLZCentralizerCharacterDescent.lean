import ModularRep.PaperProofs.TypeBFLZCentralizerConjugacy
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import Mathlib.GroupTheory.Coset.Card

/-!
# Ordinary character descent on the actual dual centralizers

Serre, Linear Representations of Finite Groups, Section 12.3, Theorem 24
and its corollary (p. 94), with Section 12.1, Propositions 32--33
(pp. 90--91), supplies the narrowly stated splitting-field descent input.
It concerns every ordinary irreducible character on these actual finite
centralizers, not only the later unipotent labels or a desired block fibre.

The algebraic closure is a separate ordinary coefficient field. There is
no map from it into the modular system's fraction field. The source value
equation uses only the canonical inclusion in the other direction. The
chosen descent, its uniqueness, injectivity and conjugation equation are
deduced. No character/block classification or Type B target is supplied.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBFLZCentralizerCharacterDescent

open ModularRep OrdinaryIrreducibleCharacter
open TypeBConformalDualCarriers TypeBFLZLabelSource TypeBFLZCentralizerConjugacy

universe u

variable {F K : Type u} [Field F] [Field K] {p n : ℕ}

/-- E1 splitting-field descent on the literal actual centralizer family.
Finite base and characteristic zero are explicit constructor binders;
the root hypothesis is on each exact finite group being descended. -/
structure DescentCertificate [finiteBase : Finite F]
    [ordinaryCharacteristic : CharZero K] : Prop where
  descends : ∀ (s : SemisimpleParameter F p n),
    HasEnoughRootsOfUnity K (Nat.card (parameterCentralizer F p n s)) →
      ∀ chi : Irr (AlgebraicClosure K) (parameterCentralizer F p n s),
        ∃ psi : Irr K (parameterCentralizer F p n s),
          ∀ x : parameterCentralizer F p n s,
            algebraMap K (AlgebraicClosure K) (psi x) = chi x

variable [Finite F] [CharZero K]

/-- Lagrange supplies each root guard from the dual group's guard before
an Equation(3.4) source has been chosen. -/
def centralizerRoots (dualRoots : HasEnoughRootsOfUnity K (Nat.card (CSp F n)))
    (s : SemisimpleParameter F p n) :
    HasEnoughRootsOfUnity K (Nat.card (parameterCentralizer F p n s)) := by
  letI := dualRoots
  exact HasEnoughRootsOfUnity.of_dvd K
    (Subgroup.card_subgroup_dvd_card (parameterCentralizer F p n s))

variable (certificate : DescentCertificate (F := F) (K := K) (p := p) (n := n))
variable (dualRoots : HasEnoughRootsOfUnity K (Nat.card (CSp F n)))

/-- Choose a descended ordinary character using the exact source value equation. -/
def DescentCertificate.descend (s : SemisimpleParameter F p n)
    (chi : Irr (AlgebraicClosure K) (parameterCentralizer F p n s)) :
    Irr K (parameterCentralizer F p n s) :=
  Classical.choose (certificate.descends s (centralizerRoots dualRoots s) chi)

theorem DescentCertificate.descend_value (s : SemisimpleParameter F p n)
    (chi : Irr (AlgebraicClosure K) (parameterCentralizer F p n s))
    (x : parameterCentralizer F p n s) :
    algebraMap K (AlgebraicClosure K) (certificate.descend dualRoots s chi x) = chi x :=
  Classical.choose_spec (certificate.descends s (centralizerRoots dualRoots s) chi) x

/-- The chosen character is uniquely fixed by its values in the closure. -/
theorem DescentCertificate.descend_unique (s : SemisimpleParameter F p n)
    (chi : Irr (AlgebraicClosure K) (parameterCentralizer F p n s))
    (psi : Irr K (parameterCentralizer F p n s))
    (hpsi : ∀ x, algebraMap K (AlgebraicClosure K) (psi x) = chi x) :
    certificate.descend dualRoots s chi = psi := by
  apply OrdinaryIrreducibleCharacter.ext
  intro x
  apply (algebraMap K (AlgebraicClosure K)).injective
  exact (certificate.descend_value dualRoots s chi x).trans (hpsi x).symm

theorem DescentCertificate.descend_injective (s : SemisimpleParameter F p n) :
    Function.Injective (certificate.descend dualRoots s) := by
  intro chi psi h
  apply OrdinaryIrreducibleCharacter.ext
  intro x
  rw [← certificate.descend_value dualRoots s chi x,
    ← certificate.descend_value dualRoots s psi x, h]

/-- The same value-conjugation equation descends to K on the actual
centralizer map. No new character action is assumed. -/
theorem DescentCertificate.descend_conjugation_value
    (g : CSp F n) (s : SemisimpleParameter F p n)
    (chi : Irr (AlgebraicClosure K) (parameterCentralizer F p n s))
    (theta : Irr (AlgebraicClosure K)
      (parameterCentralizer F p n (semisimpleConj g s)))
    (h : ∀ x : parameterCentralizer F p n s,
      theta (centralizerConj g s x) = chi x)
    (x : parameterCentralizer F p n s) :
    certificate.descend dualRoots (semisimpleConj g s) theta (centralizerConj g s x) =
      certificate.descend dualRoots s chi x := by
  apply (algebraMap K (AlgebraicClosure K)).injective
  rw [certificate.descend_value, certificate.descend_value]
  exact h x

end ModularRep.PaperProofs.TypeBFLZCentralizerCharacterDescent


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
