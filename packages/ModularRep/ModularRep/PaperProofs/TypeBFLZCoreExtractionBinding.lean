import ModularRep.PaperProofs.TypeBFLZCoreProfileConjugacy
import ModularRep.PaperProofs.TypeBFLZCorePairConjugacy

/-!
# Core extraction from the same profile labels and actual characters

The possible core carrier is the range of the profile-indexed core operator.
Its class index uses the actual multiplier and characteristic polynomial.
The actual unipotent-character labelling and its precise pointwise value
square determine character transport. That square implies the core-extraction
square; no extra core covariance or core-pair action is sourced.

The profile label/operator must still be identified with the literal FLZ
partition and odd-defect symbol data, with component-field hook/cocore mode.
This is an explicit model obligation. No block classification, global basic
set, blockwise matching or manuscript target is assumed here.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBFLZCoreExtractionBinding

open ModularRep OrdinaryIrreducibleCharacter
open TypeBConformalDualCarriers TypeBFLZLabelSource TypeBFLZCentralizerConjugacy
open TypeBFLZCoreProfileConjugacy TypeBFLZCorePairConjugacy

universe u

variable {F K : Type u} [Field F] [Field K] [CharZero K] {p ell n : ℕ}
variable (Psi RawCore : Profile F → Type u)
variable (takeCore : ∀ profile, Psi profile → RawCore profile)

/-- The core carrier contains exactly the core values actually attained
from the same profile's unipotent labels. -/
def PossibleCore (profile : Profile F) :=
  {kappa : RawCore profile // ∃ mu : Psi profile, takeCore profile mu = kappa}

/-- The canonical core value carries its actual preimage as membership proof. -/
def profileCore (profile : Profile F) (mu : Psi profile) :
    PossibleCore Psi RawCore takeCore profile :=
  ⟨takeCore profile mu, mu, rfl⟩

@[simp]
theorem profileCore_val (profile : Profile F) (mu : Psi profile) :
    (profileCore Psi RawCore takeCore profile mu).val = takeCore profile mu := rfl

/-- There are no extra labels in the possible-core carrier. -/
theorem profileCore_surjective (profile : Profile F) :
    Function.Surjective (profileCore Psi RawCore takeCore profile) := by
  rintro ⟨kappa, mu, hmu⟩
  refine ⟨mu, ?_⟩
  exact Subtype.ext hmu

/-- A profile equality transports the same core operator and its range. -/
theorem profileCore_heq {profile other : Profile F} (h : profile = other)
    {mu : Psi profile} {nu : Psi other} (values : HEq mu nu) :
    HEq (profileCore Psi RawCore takeCore profile mu)
      (profileCore Psi RawCore takeCore other nu) := by
  subst other
  cases values
  rfl

/-- The actual rational index determines the possible-core carrier through
its proved multiplier/characteristic-polynomial profile. -/
def coreByClass (i : SourceIndex F p ell n) : Type u :=
  PossibleCore Psi RawCore takeCore (classProfile i)

/-- Conjugation transports exactly the same profile label by equality. -/
def psiConj (g : CSp F n) (s : SemisimpleParameter F p n) :
    Psi (semisimpleProfile s) ≃ Psi (semisimpleProfile (semisimpleConj g s)) :=
  Equiv.cast (congrArg Psi (semisimpleProfile_conj g s).symm)

theorem psiConj_heq (g : CSp F n) (s : SemisimpleParameter F p n)
    (mu : Psi (semisimpleProfile s)) :
    HEq (psiConj Psi g s mu) mu := cast_heq _ _

section CharacterLabels

variable (unipotent : UnipotentPredicate F K p n)
variable (label : ∀ s : SemisimpleParameter F p n,
  Psi (semisimpleProfile s) ≃
    {chi : Irr K (parameterCentralizer F p n s) // unipotent s chi})

/-- The exact same pointwise character-value square as the frozen Psi
adapter, now with its label transport fixed by the actual profile. -/
def CharacterSquare : Prop :=
  PsiCharacterSquare unipotent (fun s => Psi (semisimpleProfile s))
    (psiConj Psi) label

variable (square : CharacterSquare Psi unipotent label)

include square in
/-- Actual unipotent stability is derived from the value square and the
same fibrewise label equivalence. -/
theorem labelStable : UnipotentStable unipotent :=
  unipotentStable_of_psiCharacterSquare unipotent
    (fun s => Psi (semisimpleProfile s)) (psiConj Psi) label square

/-- Extract the actual label of the actual centralizer character, then
apply the same profile's core operator. The class-profile equality is rfl. -/
def extraction : CoreExtraction (ell := ell) (coreByClass Psi RawCore takeCore) unipotent :=
  fun s chi => profileCore Psi RawCore takeCore (admissibleProfile s)
    ((label (admissibleToSemisimple F p ell n s)).symm chi)

include square in
/-- The inverse actual-character labelling commutes with the already
constructed centralizer-character conjugation. -/
theorem inverseLabel_conj (stable : UnipotentStable unipotent)
    (g : CSp F n) (s : AdmissibleParameter F p ell n)
    (chi : {chi : Irr K (parameterCentralizer F p n (admissibleToSemisimple F p ell n s)) //
      unipotent (admissibleToSemisimple F p ell n s) chi}) :
    (label (admissibleToSemisimple F p ell n (admissibleConj g s))).symm
        (selectedPairConj unipotent stable g
          (⟨s, chi⟩ : CharacterPair F K p ell n unipotent)).2 =
      psiConj Psi g (admissibleToSemisimple F p ell n s)
        ((label (admissibleToSemisimple F p ell n s)).symm chi) := by
  apply (label (admissibleToSemisimple F p ell n (admissibleConj g s))).injective
  dsimp only [selectedPairConj]
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  apply OrdinaryIrreducibleCharacter.ext
  intro y
  obtain ⟨x, rfl⟩ := (centralizerConj g (admissibleToSemisimple F p ell n s)).surjective y
  change centralizerCharacterConj g _ chi.val (centralizerConj g _ x) = _
  rw [centralizerCharacterConj_anchor]
  have hs := square g (admissibleToSemisimple F p ell n s)
    ((label (admissibleToSemisimple F p ell n s)).symm chi) x
  have hmu := congrArg
    (fun z : {chi : Irr K (parameterCentralizer F p n
        (admissibleToSemisimple F p ell n s)) //
      unipotent (admissibleToSemisimple F p ell n s) chi} => z.val x)
    ((label (admissibleToSemisimple F p ell n s)).apply_symm_apply chi)
  exact hmu.symm.trans hs.symm

include square in
/-- The local extraction square is a theorem about the same profile
operator, proved from the actual character-value square. -/
theorem extractionSquare (stable : UnipotentStable unipotent) :
    CoreExtractionSquare (ell := ell) (coreByClass Psi RawCore takeCore) unipotent stable
      (extraction Psi RawCore takeCore unipotent label) := by
  intro g s chi
  apply eq_of_heq
  change HEq
    (profileCore Psi RawCore takeCore (admissibleProfile (admissibleConj g s))
      ((label (admissibleToSemisimple F p ell n (admissibleConj g s))).symm
        (selectedPairConj unipotent stable g
          (⟨s, chi⟩ : CharacterPair F K p ell n unipotent)).2))
    (coreTransport (coreByClass Psi RawCore takeCore) g s
      (extraction Psi RawCore takeCore unipotent label s chi))
  rw [inverseLabel_conj Psi unipotent label square stable g s chi]
  exact (profileCore_heq Psi RawCore takeCore (admissibleProfile_conj g s)
    (psiConj_heq Psi g (admissibleToSemisimple F p ell n s)
      ((label (admissibleToSemisimple F p ell n s)).symm chi))).trans
    (coreTransport_heq (coreByClass Psi RawCore takeCore) g s
      (extraction Psi RawCore takeCore unipotent label s chi)).symm

include square in
/-- Equivariance of the complete core map uses the TWO constructed pair
actions and the derived extraction square, with no additional input. -/
theorem coreAt_equivariant (stable : UnipotentStable unipotent)
    (g : CSp F n) (P : CharacterPair F K p ell n unipotent) :
    let _ : MulAction (CSp F n) (CharacterPair F K p ell n unipotent) :=
      selectedPairAction (ell := ell) unipotent stable
    let _ := corePairAction (coreByClass (p := p) (ell := ell) (n := n) Psi RawCore takeCore)
    coreAt (ell := ell) (coreByClass Psi RawCore takeCore) unipotent
        (extraction Psi RawCore takeCore unipotent label) (g • P) =
      g • coreAt (ell := ell) (coreByClass Psi RawCore takeCore) unipotent
        (extraction Psi RawCore takeCore unipotent label) P :=
  TypeBFLZCorePairConjugacy.coreAt_equivariant (coreByClass Psi RawCore takeCore)
    unipotent stable (extraction Psi RawCore takeCore unipotent label)
    (extractionSquare Psi RawCore takeCore unipotent label square stable) g P

end CharacterLabels

end ModularRep.PaperProofs.TypeBFLZCoreExtractionBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
