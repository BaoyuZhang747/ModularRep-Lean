import ModularRep.PaperProofs.TypeBFLZZeroLabelProduct
import ModularRep.PaperProofs.TypeBFLZPrimarySource
import ModularRep.PaperProofs.TypeBFLZCentralizerCharacterDescent
import ModularRep.PaperProofs.TypeBFLZLiteralCharacterSource

/-!
# Published occurring-component characters on the prescribed ordinary field

The E2 source is the actual FLZ Section 3.4 character family on the product
of occurring polynomial components, over the separate field AlgebraicClosure K.
Its numerical/primary interpretation is retained as a literal E1 guard.
The full profile product is identified by the checked zero-coordinate
equivalence. Serre's one-way character descent then gives the same family
over K with an exact scalar-extension value equation. Injectivity and
conjugation descend in Lean, producing the frozen literal source interface.

Equation (3.4), core/block classification, full union and integral-series
certificates must still use this SAME published assignment. No input here
supplies those statements or the desired blockwise correspondence.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBFLZOccurringCharacterSource

open ModularRep OrdinaryIrreducibleCharacter
open TypeBCliffordCarriers TypeBConformalDualCarriers TypeBFLZLabelSource
open TypeBFLZCentralizerConjugacy TypeBFLZCoreProfileConjugacy
open TypeBFLZPolynomialComponents TypeBFLZCoreExtractionBinding

universe u

variable {F : Type u} [Field F] {p n : ℕ}

/-- The actual product of the fixed-rank labels on occurring components.
Its nonzero-polynomial proof is the checked actual characteristic-polynomial fact. -/
abbrev OccurringLabels (s : SemisimpleParameter F p n) :=
  ∀ Gamma : OccurringComponent (semisimpleProfile s),
    TypeBFLZLiteralProfileModel.ComponentLabel (semisimpleProfile s)
      (semisimpleProfile_polynomial_ne_zero s) Gamma.val

/-- Actual conjugation changes only the equal profile and proof indices. -/
def occurringLabelsConj (g : CSp F n) (s : SemisimpleParameter F p n) :
    OccurringLabels s ≃ OccurringLabels (semisimpleConj g s) :=
  (TypeBFLZZeroLabelProduct.occurringProductEquiv (semisimpleProfile s)
      (semisimpleProfile_polynomial_ne_zero s)).symm.trans
    ((psiConj TypeBFLZZeroLabelProduct.OccurringPsi g s).trans
      (TypeBFLZZeroLabelProduct.occurringProductEquiv
        (semisimpleProfile (semisimpleConj g s))
        (semisimpleProfile_polynomial_ne_zero (semisimpleConj g s))))

/-- The actual full/occurring label equivalence is a checked construction. -/
def labelEquiv (zero : TypeBFLZZeroLabelProduct.ZeroSymbolCertificate)
    (s : SemisimpleParameter F p n) :
    TypeBFLZLiteralProfileModel.Psi (semisimpleProfile s) ≃ OccurringLabels s :=
  TypeBFLZZeroLabelProduct.psiProductEquiv zero (semisimpleProfile s)
    (semisimpleProfile_polynomial_ne_zero s)

@[simp]
theorem labelEquiv_apply (zero : TypeBFLZZeroLabelProduct.ZeroSymbolCertificate)
    (s : SemisimpleParameter F p n)
    (mu : TypeBFLZLiteralProfileModel.Psi (semisimpleProfile s))
    (Gamma : OccurringComponent (semisimpleProfile s)) :
    labelEquiv zero s mu Gamma = mu.2 Gamma.val := rfl

theorem labelEquiv_conjugation (zero : TypeBFLZZeroLabelProduct.ZeroSymbolCertificate)
    (g : CSp F n) (s : SemisimpleParameter F p n)
    (mu : TypeBFLZLiteralProfileModel.Psi (semisimpleProfile s)) :
    labelEquiv zero (semisimpleConj g s)
        (psiConj TypeBFLZLiteralProfileModel.Psi g s mu) =
      occurringLabelsConj g s (labelEquiv zero s mu) := by
  simp only [labelEquiv, occurringLabelsConj, TypeBFLZZeroLabelProduct.psiProductEquiv,
    Equiv.trans_apply, Equiv.symm_apply_apply]
  exact congrArg
    (TypeBFLZZeroLabelProduct.occurringProductEquiv
      (semisimpleProfile (semisimpleConj g s))
      (semisimpleProfile_polynomial_ne_zero (semisimpleConj g s)))
    (TypeBFLZZeroLabelProduct.psiEquiv_transport zero
      (semisimpleProfile_conj g s).symm mu)

variable {K : Type u} [Field K] [Finite F]
variable {ell f : ℕ} [CharP F p]

/-- E2: the FLZ Section 3.4 family on the actual occurring-component
labels and full CSp centralizers. The primary and coefficient guards
are explicit indices; there is no free label or unipotent predicate. -/
structure OccurringCharacterSource
    (parameters : OddFieldParameters F p f) (scope : Applicability p ell n)
    (primary : TypeBFLZPrimarySource.PrimarySource parameters scope)
    [ordinaryCharacteristic : CharZero K] where
  character : ∀ s : SemisimpleParameter F p n,
    OccurringLabels s → Irr (AlgebraicClosure K) (parameterCentralizer F p n s)
  injective : ∀ s, Function.Injective (character s)
  conjugation : ∀ (g : CSp F n) (s : SemisimpleParameter F p n)
    (mu : OccurringLabels s) (x : parameterCentralizer F p n s),
    character (semisimpleConj g s) (occurringLabelsConj g s mu) (centralizerConj g s x) =
      character s mu x

variable [CharZero K]
variable {parameters : OddFieldParameters F p f} {scope : Applicability p ell n}
variable {primary : TypeBFLZPrimarySource.PrimarySource parameters scope}
variable (source : OccurringCharacterSource (K := K) parameters scope primary)
variable (zero : TypeBFLZZeroLabelProduct.ZeroSymbolCertificate)
variable (descent : TypeBFLZCentralizerCharacterDescent.DescentCertificate
  (F := F) (K := K) (p := p) (n := n))
variable (dualRoots : HasEnoughRootsOfUnity K (Nat.card (CSp F n)))

/-- Instantiate the literal source by the SAME published occurring family,
the constructed label equivalence and the exact ordinary-field descent. -/
def OccurringCharacterSource.toLiteralSource :
    TypeBFLZLiteralCharacterSource.CharacterSource parameters scope dualRoots where
  character s mu := descent.descend dualRoots s (source.character s (labelEquiv zero s mu))
  injective s := (descent.descend_injective dualRoots s).comp
    ((source.injective s).comp (labelEquiv zero s).injective)
  conjugation g s mu x := by
    apply descent.descend_conjugation_value dualRoots g s
    intro y
    rw [labelEquiv_conjugation]
    exact source.conjugation g s (labelEquiv zero s mu) y

/-- The prescribed field's character has the exact published values after
the canonical inclusion K -> AlgebraicClosure K. -/
theorem OccurringCharacterSource.toLiteralSource_character_value
    (s : SemisimpleParameter F p n)
    (mu : TypeBFLZLiteralProfileModel.Psi (semisimpleProfile s))
    (x : parameterCentralizer F p n s) :
    algebraMap K (AlgebraicClosure K)
        ((source.toLiteralSource zero descent dualRoots).character s mu x) =
      source.character s (labelEquiv zero s mu) x :=
  descent.descend_value dualRoots s (source.character s (labelEquiv zero s mu)) x

/-- The source image is exactly the descended published occurring family. -/
theorem OccurringCharacterSource.toLiteralSource_unipotent_iff
    (s : SemisimpleParameter F p n) (chi : Irr K (parameterCentralizer F p n s)) :
    (source.toLiteralSource zero descent dualRoots).unipotent s chi ↔
      ∃ mu : OccurringLabels s,
        descent.descend dualRoots s (source.character s mu) = chi := by
  rw [TypeBFLZLiteralCharacterSource.CharacterSource.unipotent_iff]
  constructor
  · rintro ⟨mu, hmu⟩
    exact ⟨labelEquiv zero s mu, hmu⟩
  · rintro ⟨mu, hmu⟩
    refine ⟨(labelEquiv zero s).symm mu, ?_⟩
    change descent.descend dualRoots s
      (source.character s (labelEquiv zero s ((labelEquiv zero s).symm mu))) = chi
    rw [Equiv.apply_symm_apply]
    exact hmu

end ModularRep.PaperProofs.TypeBFLZOccurringCharacterSource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
