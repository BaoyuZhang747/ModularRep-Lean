import ModularRep.PaperProofs.TypeBFLZLiteralScope
import ModularRep.PaperProofs.TypeBFLZLabelSplittingSource
import Mathlib.Logic.Equiv.Set

/-!
# Literal FLZ character assignment and its range presentation

The external family assigns an actual ordinary character of the full
conformal centralizer to each literal partition/symbol label. Its source
boundary retains the actual finite odd field, odd nondefining prime scope
and prescribed ordinary roots. The internal unipotent subset is defined
as its image; its label equivalence and conjugation stability are deduced.

FLZ Section 3.4 identifies the published assignment's image with genuine
unipotent characters. That semantic identification is an E2 source scope,
not a local reconstruction of Deligne--Lusztig occurrence. Primary
multiplicity, centralizer extension and coefficient transport bindings
remain explicit source-realization obligations. Injection and the value
square alone do not characterize the published family: all subsequent
Jordan/block/union certificates must concern the SAME chosen assignment.
No such later certificate is produced for an arbitrary family here.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBFLZLiteralCharacterSource

open ModularRep OrdinaryIrreducibleCharacter
open TypeBCliffordCarriers TypeBConformalDualCarriers TypeBFLZLabelSource
open TypeBFLZCoreProfileConjugacy TypeBFLZCoreExtractionBinding
open TypeBFLZCentralizerConjugacy

universe u

variable {F K : Type u} [Field F] [Finite F] [Field K] [CharZero K]
variable {p ell f n : ℕ} [CharP F p]

/-- E2 interface for the published literal character assignment, with
its numerical and coefficient scope retained as explicit indices.
There is no separately supplied unipotent predicate or label equivalence.
Source authenticity requires the jointly chosen FLZ family and later
certificates; these three fields do not characterize that family uniquely. -/
structure CharacterSource (parameters : OddFieldParameters F p f)
    (scope : Applicability p ell n)
    (dualRoots : HasEnoughRootsOfUnity K (Nat.card (CSp F n)))
    [ordinaryCharacteristic : CharZero K] where
  character : ∀ s : SemisimpleParameter F p n,
    TypeBFLZLiteralProfileModel.Psi (semisimpleProfile s) →
      Irr K (parameterCentralizer F p n s)
  injective : ∀ s, Function.Injective (character s)
  conjugation : ∀ (g : CSp F n) (s : SemisimpleParameter F p n)
      (mu : TypeBFLZLiteralProfileModel.Psi (semisimpleProfile s))
      (x : parameterCentralizer F p n s),
    character (semisimpleConj g s)
        (psiConj TypeBFLZLiteralProfileModel.Psi g s mu) (centralizerConj g s x) =
      character s mu x

variable {parameters : OddFieldParameters F p f} {scope : Applicability p ell n}
variable {dualRoots : HasEnoughRootsOfUnity K (Nat.card (CSp F n))}
variable (source : CharacterSource parameters scope dualRoots)

/-- A definitional presentation of the published family's character
subset, using the actual Irr carrier of the full CSp centralizer. -/
def CharacterSource.unipotent : UnipotentPredicate F K p n :=
  fun s chi => chi ∈ Set.range (source.character s)

theorem CharacterSource.unipotent_iff (s : SemisimpleParameter F p n)
    (chi : Irr K (parameterCentralizer F p n s)) :
    source.unipotent s chi ↔ ∃ mu, source.character s mu = chi := Iff.rfl

/-- The label equivalence is constructed from injection onto the literal
image, not supplied as another character-classification hypothesis. -/
def CharacterSource.label (s : SemisimpleParameter F p n) :
    TypeBFLZLiteralProfileModel.Psi (semisimpleProfile s) ≃
      {chi : Irr K (parameterCentralizer F p n s) // source.unipotent s chi} :=
  Equiv.ofInjective (source.character s) (source.injective s)

@[simp]
theorem CharacterSource.label_apply (s : SemisimpleParameter F p n)
    (mu : TypeBFLZLiteralProfileModel.Psi (semisimpleProfile s)) :
    (source.label s mu).val = source.character s mu := rfl

theorem CharacterSource.label_surjective (s : SemisimpleParameter F p n) :
    Function.Surjective (source.label s) := (source.label s).surjective

theorem CharacterSource.square :
    CharacterSquare TypeBFLZLiteralProfileModel.Psi source.unipotent source.label := by
  intro g s mu x
  exact source.conjugation g s mu x

theorem CharacterSource.stable : UnipotentStable source.unipotent :=
  labelStable TypeBFLZLiteralProfileModel.Psi source.unipotent source.label source.square

end ModularRep.PaperProofs.TypeBFLZLiteralCharacterSource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
