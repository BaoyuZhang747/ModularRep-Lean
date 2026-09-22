import ModularRep.PaperProofs.TypeBFLZCentralizerConjugacy

/-!
# Canonical conjugation of core pairs over actual rational conjugacy classes

A core family on the actual SourceIndex is pulled back to the actual
admissible parameters. Conjugation transports the same core value along
the proved equality of class indices. The action laws are derived.

This class-indexed model has trivial action of every parameter stabilizer
on its core fibre, as the published unchanged combinatorial-label action
requires. Its identification with the literal FLZ partition/symbol core
family remains an explicit source-model obligation, not a theorem here.

A narrow fibrewise extraction square on the already constructed actual
centralizer-character transport implies equivariance of the whole core
pair map. No block classification, target correspondence or action laws
are supplied by a source package in this file.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBFLZCorePairConjugacy

open ModularRep OrdinaryIrreducibleCharacter
open TypeBConformalDualCarriers TypeBFLZLabelSource TypeBFLZCentralizerConjugacy

universe u

variable {F K : Type u} [Field F] [Field K] [CharZero K]
variable {p ell n : ℕ}

/-- Actual conjugation preserves the actual rational conjugacy class index. -/
theorem parameterIndex_admissibleConj (g : CSp F n)
    (s : AdmissibleParameter F p ell n) :
    parameterIndex F p ell n (admissibleConj g s) = parameterIndex F p ell n s := by
  have h : IsConj s.val (admissibleConj g s).val := isConj_iff.mpr ⟨g, rfl⟩
  exact (parameterIndex_eq_iff F p ell n (admissibleConj g s) s).mpr h.symm

variable (CoreByClass : SourceIndex F p ell n → Type u)

/-- Pull back the class-indexed core family to the same actual parameters. -/
abbrev CoreFamily (s : AdmissibleParameter F p ell n) :=
  CoreByClass (parameterIndex F p ell n s)

/-- Conjugation changes only the displayed parameter, transporting the
same value by its actual class-index equality. -/
def coreTransport (g : CSp F n) (s : AdmissibleParameter F p ell n)
    (kappa : CoreFamily CoreByClass s) : CoreFamily CoreByClass (admissibleConj g s) :=
  cast (congrArg CoreByClass (parameterIndex_admissibleConj g s).symm) kappa

/-- The transport is a type cast of the same core value. -/
theorem coreTransport_heq (g : CSp F n) (s : AdmissibleParameter F p ell n)
    (kappa : CoreFamily CoreByClass s) :
    HEq (coreTransport CoreByClass g s kappa) kappa :=
  cast_heq _ _

/-- The two coordinates of the actual core-pair conjugation. -/
def corePairConj (g : CSp F n) (P : BlockPair F p ell n (CoreFamily CoreByClass)) :
    BlockPair F p ell n (CoreFamily CoreByClass) :=
  ⟨admissibleConj g P.1, coreTransport CoreByClass g P.1 P.2⟩

@[simp]
theorem corePairConj_parameter (g : CSp F n)
    (P : BlockPair F p ell n (CoreFamily CoreByClass)) :
    (corePairConj CoreByClass g P).1 = admissibleConj g P.1 := rfl

/-- Heterogeneous equality records the explicit dependent-fibre cast. -/
theorem corePairConj_core_heq (g : CSp F n)
    (P : BlockPair F p ell n (CoreFamily CoreByClass)) :
    HEq (corePairConj CoreByClass g P).2 P.2 :=
  coreTransport_heq CoreByClass g P.1 P.2

@[simp]
theorem corePairConj_one (P : BlockPair F p ell n (CoreFamily CoreByClass)) :
    corePairConj CoreByClass 1 P = P :=
  Sigma.ext (admissibleConj_one P.1) (corePairConj_core_heq CoreByClass 1 P)

/-- Multiplication follows from parameter conjugation and composition of
casts; no coherence law on a core action is assumed. -/
theorem corePairConj_mul (g h : CSp F n)
    (P : BlockPair F p ell n (CoreFamily CoreByClass)) :
    corePairConj CoreByClass (g * h) P =
      corePairConj CoreByClass g (corePairConj CoreByClass h P) := by
  apply Sigma.ext (admissibleConj_mul g h P.1)
  exact (corePairConj_core_heq CoreByClass (g * h) P).trans
    ((corePairConj_core_heq CoreByClass g (corePairConj CoreByClass h P)).trans
      (corePairConj_core_heq CoreByClass h P)).symm

/-- The CSp action is constructed on the literal dependent core-pair carrier. -/
@[instance_reducible]
def corePairAction : MulAction (CSp F n) (BlockPair F p ell n (CoreFamily CoreByClass)) where
  smul := corePairConj CoreByClass
  one_smul := corePairConj_one CoreByClass
  mul_smul := corePairConj_mul CoreByClass

theorem corePairAction_parameter (g : CSp F n)
    (P : BlockPair F p ell n (CoreFamily CoreByClass)) :
    let _ := corePairAction CoreByClass
    (g • P).1.val = g * P.1.val * g⁻¹ := rfl

/-- Package the unchanged core together with its actual class index. -/
def coreClassValue (P : BlockPair F p ell n (CoreFamily CoreByClass)) :
    Sigma CoreByClass := ⟨parameterIndex F p ell n P.1, P.2⟩

@[simp]
theorem corePairConj_classValue (g : CSp F n)
    (P : BlockPair F p ell n (CoreFamily CoreByClass)) :
    coreClassValue CoreByClass (corePairConj CoreByClass g P) =
      coreClassValue CoreByClass P :=
  Sigma.ext (parameterIndex_admissibleConj g P.1) (corePairConj_core_heq CoreByClass g P)

/-- The class-family model has no additional stabilizer action on cores.
This consequence is explicit for the later published-model audit. -/
theorem corePairConj_eq_self_iff (g : CSp F n)
    (P : BlockPair F p ell n (CoreFamily CoreByClass)) :
    corePairConj CoreByClass g P = P ↔ admissibleConj g P.1 = P.1 := by
  constructor
  · intro h
    exact congrArg (fun Q : BlockPair F p ell n (CoreFamily CoreByClass) => Q.1) h
  · intro h
    exact Sigma.ext h (corePairConj_core_heq CoreByClass g P)

section Extraction

variable (unipotent : UnipotentPredicate F K p n)
variable (stable : UnipotentStable unipotent)

/-- A per-parameter extraction from the SAME actual unipotent centralizer
characters into the class-indexed core fibre. Its combinatorial meaning
is supplied by the separate FLZ model realization. -/
abbrev CoreExtraction :=
  ∀ s : AdmissibleParameter F p ell n,
    {chi : Irr K (parameterCentralizer F p n (admissibleToSemisimple F p ell n s)) //
      unipotent (admissibleToSemisimple F p ell n s) chi} → CoreFamily CoreByClass s

variable (extraction : CoreExtraction CoreByClass unipotent)

/-- The exact local square compares extraction on the literal transported
centralizer character with the canonical cast of its core. It contains no
whole-pair equivariance, classification or action-law premise. -/
def CoreExtractionSquare : Prop :=
  ∀ (g : CSp F n) (s : AdmissibleParameter F p ell n)
    (chi : {chi : Irr K (parameterCentralizer F p n (admissibleToSemisimple F p ell n s)) //
      unipotent (admissibleToSemisimple F p ell n s) chi}),
    extraction (admissibleConj g s)
        (selectedPairConj unipotent stable g
          (⟨s, chi⟩ : CharacterPair F K p ell n unipotent)).2 =
      coreTransport CoreByClass g s (extraction s chi)

/-- Build the whole core pair from its actual parameter and fibre extraction. -/
def coreAt (P : CharacterPair F K p ell n unipotent) :
    BlockPair F p ell n (CoreFamily CoreByClass) :=
  ⟨P.1, extraction P.1 P.2⟩

@[simp]
theorem coreAt_parameter (P : CharacterPair F K p ell n unipotent) :
    (coreAt CoreByClass unipotent extraction P).1 = P.1 := rfl

/-- The narrow local square implies the whole-pair conjugation formula. -/
theorem coreAt_conj
    (square : CoreExtractionSquare CoreByClass unipotent stable extraction)
    (g : CSp F n) (P : CharacterPair F K p ell n unipotent) :
    coreAt CoreByClass unipotent extraction (selectedPairConj unipotent stable g P) =
      corePairConj CoreByClass g (coreAt CoreByClass unipotent extraction P) := by
  rcases P with ⟨s, chi⟩
  exact congrArg
    (fun kappa : CoreFamily CoreByClass (admissibleConj g s) =>
      (⟨admissibleConj g s, kappa⟩ : BlockPair F p ell n (CoreFamily CoreByClass)))
    (square g s chi)

/-- Equivariance for the TWO constructed actual pair actions is a deduction. -/
theorem coreAt_equivariant
    (square : CoreExtractionSquare CoreByClass unipotent stable extraction)
    (g : CSp F n) (P : CharacterPair F K p ell n unipotent) :
    let _ : MulAction (CSp F n) (CharacterPair F K p ell n unipotent) :=
      selectedPairAction (ell := ell) unipotent stable
    let _ := corePairAction CoreByClass
    coreAt CoreByClass unipotent extraction (g • P) =
      g • coreAt CoreByClass unipotent extraction P :=
  coreAt_conj CoreByClass unipotent stable extraction square g P

end Extraction

end ModularRep.PaperProofs.TypeBFLZCorePairConjugacy


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
