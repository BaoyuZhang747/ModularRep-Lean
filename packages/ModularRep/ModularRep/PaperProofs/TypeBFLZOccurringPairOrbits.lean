import ModularRep.PaperProofs.TypeBFLZOccurringCharacterSource

/-!
# Actual occurring-label pairs and their centralizer-character orbits

The pair action is defined by actual parameter conjugation and the already
constructed equality transport of occurring polynomial labels. Its laws
are proved before any character source is used. The same descended source
then gives an equivariant pair equivalence and an orbit equivalence.

No action, orbit classification, Jordan map, block source, scalar-extension
compatibility or Type B target is supplied as an additional field.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBFLZOccurringPairOrbits

open ModularRep OrdinaryIrreducibleCharacter
open TypeBCliffordCarriers TypeBConformalDualCarriers TypeBFLZLabelSource
open TypeBFLZCentralizerConjugacy TypeBFLZCoreProfileConjugacy
open TypeBFLZPolynomialComponents TypeBFLZCoreExtractionBinding
open TypeBFLZOccurringCharacterSource TypeBFLZZeroLabelProduct

universe u

variable {F : Type u} [Field F] {p n : ℕ}

/-- The two literal coordinates, before choosing any character source. -/
def OccurringPair (F : Type u) [Field F] (p n : ℕ) : Type u :=
  Σ s : SemisimpleParameter F p n, OccurringLabels s

/-- Equality transport of the product changes no label value. -/
theorem productTransport_heq {P Q : Profile F} (h : P = Q)
    (hP : P.2 ≠ 0) (hQ : Q.2 ≠ 0)
    (mu : ∀ Gamma : OccurringComponent P,
      TypeBFLZLiteralProfileModel.ComponentLabel P hP Gamma.val) :
    HEq (occurringProductEquiv Q hQ
      (occurringTransport h ((occurringProductEquiv P hP).symm mu))) mu := by
  subst Q
  rfl

/-- The same equality transport fixes each actual occurring coordinate. -/
theorem productTransport_apply {P Q : Profile F} (h : P = Q)
    (hP : P.2 ≠ 0) (hQ : Q.2 ≠ 0)
    (mu : ∀ Gamma : OccurringComponent P,
      TypeBFLZLiteralProfileModel.ComponentLabel P hP Gamma.val)
    (Gamma : OccurringComponent P) :
    HEq (occurringProductEquiv Q hQ
      (occurringTransport h ((occurringProductEquiv P hP).symm mu))
        (occurringComponentTransport h Gamma)) (mu Gamma) := by
  subst Q
  rfl

theorem occurringLabelsConj_heq (g : CSp F n) (s : SemisimpleParameter F p n)
    (mu : OccurringLabels s) : HEq (occurringLabelsConj g s mu) mu :=
  productTransport_heq (semisimpleProfile_conj g s).symm
    (semisimpleProfile_polynomial_ne_zero s)
    (semisimpleProfile_polynomial_ne_zero (semisimpleConj g s)) mu

theorem occurringLabelsConj_apply (g : CSp F n) (s : SemisimpleParameter F p n)
    (mu : OccurringLabels s) (Gamma : OccurringComponent (semisimpleProfile s)) :
    HEq (occurringLabelsConj g s mu
      (occurringComponentTransport (semisimpleProfile_conj g s).symm Gamma)) (mu Gamma) :=
  productTransport_apply (semisimpleProfile_conj g s).symm
    (semisimpleProfile_polynomial_ne_zero s)
    (semisimpleProfile_polynomial_ne_zero (semisimpleConj g s)) mu Gamma

/-- Literal conjugation, not an action transported through a character equivalence. -/
def pairConj (g : CSp F n) (l : OccurringPair F p n) : OccurringPair F p n :=
  ⟨semisimpleConj g l.1, occurringLabelsConj g l.1 l.2⟩

@[simp]
theorem pairConj_parameter (g : CSp F n) (l : OccurringPair F p n) :
    (pairConj g l).1 = semisimpleConj g l.1 := rfl

theorem pairConj_label_heq (g : CSp F n) (l : OccurringPair F p n) :
    HEq (pairConj g l).2 l.2 := occurringLabelsConj_heq g l.1 l.2

theorem pairConj_coordinate (g : CSp F n) (l : OccurringPair F p n)
    (Gamma : OccurringComponent (semisimpleProfile l.1)) :
    HEq ((pairConj g l).2
      (occurringComponentTransport (semisimpleProfile_conj g l.1).symm Gamma))
      (l.2 Gamma) := occurringLabelsConj_apply g l.1 l.2 Gamma

@[simp]
theorem pairConj_one (l : OccurringPair F p n) : pairConj 1 l = l :=
  Sigma.ext (semisimpleConj_one l.1) (pairConj_label_heq 1 l)

theorem pairConj_mul (g h : CSp F n) (l : OccurringPair F p n) :
    pairConj (g * h) l = pairConj g (pairConj h l) := by
  apply Sigma.ext (semisimpleConj_mul g h l.1)
  exact (pairConj_label_heq (g * h) l).trans
    ((pairConj_label_heq g (pairConj h l)).trans (pairConj_label_heq h l)).symm

/-- The unique chosen action on the new literal pair carrier. -/
instance pairAction : MulAction (CSp F n) (OccurringPair F p n) where
  smul := pairConj
  one_smul := pairConj_one
  mul_smul := pairConj_mul

@[simp]
theorem pairAction_parameter (g : CSp F n) (l : OccurringPair F p n) :
    (g • l).1.val = g * l.1.val * g⁻¹ := rfl

/-- Inverting the already checked label square introduces no new coherence. -/
theorem labelEquiv_symm_conjugation (zero : ZeroSymbolCertificate)
    (g : CSp F n) (s : SemisimpleParameter F p n) (mu : OccurringLabels s) :
    (labelEquiv zero (semisimpleConj g s)).symm (occurringLabelsConj g s mu) =
      psiConj TypeBFLZLiteralProfileModel.Psi g s ((labelEquiv zero s).symm mu) := by
  apply (labelEquiv zero (semisimpleConj g s)).injective
  rw [Equiv.apply_symm_apply, labelEquiv_conjugation, Equiv.apply_symm_apply]

variable {K : Type u} [Field K] [CharZero K] [Finite F]
variable {ell f : ℕ} [CharP F p]
variable {parameters : OddFieldParameters F p f} {scope : Applicability p ell n}
variable {primary : TypeBFLZPrimarySource.PrimarySource parameters scope}
variable (source : OccurringCharacterSource (K := K) parameters scope primary)
variable (zero : ZeroSymbolCertificate)
variable (descent : TypeBFLZCentralizerCharacterDescent.DescentCertificate
  (F := F) (K := K) (p := p) (n := n))
variable (dualRoots : HasEnoughRootsOfUnity K (Nat.card (CSp F n)))

/-- The first coordinate stays fixed. The second is the SAME descended
character labeled by the canonical extension of the occurring product. -/
def pairEquiv : OccurringPair F p n ≃
    FullCharacterPair F K p n (source.toLiteralSource zero descent dualRoots).unipotent :=
  Equiv.sigmaCongrRight (fun s => (labelEquiv zero s).symm.trans
    ((source.toLiteralSource zero descent dualRoots).label s))

@[simp]
theorem pairEquiv_parameter (l : OccurringPair F p n) :
    (pairEquiv source zero descent dualRoots l).1 = l.1 := rfl

@[simp]
theorem pairEquiv_character (l : OccurringPair F p n) :
    (pairEquiv source zero descent dualRoots l).2 =
      (source.toLiteralSource zero descent dualRoots).label l.1
        ((labelEquiv zero l.1).symm l.2) := rfl

/-- Exact value in the original ordinary source field after K's canonical inclusion. -/
theorem pairEquiv_character_value (l : OccurringPair F p n)
    (x : parameterCentralizer F p n l.1) :
    algebraMap K (AlgebraicClosure K)
      ((pairEquiv source zero descent dualRoots l).2.val x) = source.character l.1 l.2 x := by
  change algebraMap K (AlgebraicClosure K)
    ((source.toLiteralSource zero descent dualRoots).character l.1
      ((labelEquiv zero l.1).symm l.2) x) = _
  rw [source.toLiteralSource_character_value, Equiv.apply_symm_apply]

@[simp]
theorem pairEquiv_symm_parameter
    (l : FullCharacterPair F K p n (source.toLiteralSource zero descent dualRoots).unipotent) :
    ((pairEquiv source zero descent dualRoots).symm l).1 = l.1 := rfl

@[simp]
theorem pairEquiv_symm_label
    (l : FullCharacterPair F K p n (source.toLiteralSource zero descent dualRoots).unipotent) :
    ((pairEquiv source zero descent dualRoots).symm l).2 =
      labelEquiv zero l.1
        (((source.toLiteralSource zero descent dualRoots).label l.1).symm l.2) := rfl

/-- The SAME frozen full-pair action, using the SAME derived literal label square. -/
local instance actualFullPairAction : MulAction (CSp F n)
    (FullCharacterPair F K p n (source.toLiteralSource zero descent dualRoots).unipotent) :=
  fullPairAction (source.toLiteralSource zero descent dualRoots).unipotent
    (labelStable TypeBFLZLiteralProfileModel.Psi
      (source.toLiteralSource zero descent dualRoots).unipotent
      (source.toLiteralSource zero descent dualRoots).label
      (source.toLiteralSource zero descent dualRoots).square)

theorem pairEquiv_equivariant (g : CSp F n) (l : OccurringPair F p n) :
    pairEquiv source zero descent dualRoots (g • l) =
      g • pairEquiv source zero descent dualRoots l := by
  rcases l with ⟨s, mu⟩
  apply congrArg (fun chi : {chi : Irr K (parameterCentralizer F p n (semisimpleConj g s)) //
    (source.toLiteralSource zero descent dualRoots).unipotent (semisimpleConj g s) chi} =>
      (⟨semisimpleConj g s, chi⟩ : FullCharacterPair F K p n
        (source.toLiteralSource zero descent dualRoots).unipotent))
  apply Subtype.ext
  apply OrdinaryIrreducibleCharacter.ext
  intro y
  obtain ⟨x, rfl⟩ := (centralizerConj g s).surjective y
  change
    ((source.toLiteralSource zero descent dualRoots).label (semisimpleConj g s)
      ((labelEquiv zero (semisimpleConj g s)).symm (occurringLabelsConj g s mu))).val
        (centralizerConj g s x) =
      centralizerCharacterConj g s
        ((source.toLiteralSource zero descent dualRoots).label s
          ((labelEquiv zero s).symm mu)).val (centralizerConj g s x)
  rw [labelEquiv_symm_conjugation, centralizerCharacterConj_anchor]
  exact (source.toLiteralSource zero descent dualRoots).square g s
    ((labelEquiv zero s).symm mu) x

theorem orbitRel_iff (l m : OccurringPair F p n) :
    MulAction.orbitRel (CSp F n) _ l m ↔
      MulAction.orbitRel (CSp F n) _
        (pairEquiv source zero descent dualRoots l) (pairEquiv source zero descent dualRoots m) := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g, (pairEquiv_equivariant source zero descent dualRoots g m).symm⟩
  · rintro ⟨g, hg⟩
    refine ⟨g, (pairEquiv source zero descent dualRoots).injective ?_⟩
    rw [pairEquiv_equivariant]
    exact hg

/-- Reindex the two literal orbit quotients by the constructed equivariant equivalence. -/
def orbitEquiv : MulAction.orbitRel.Quotient (CSp F n) (OccurringPair F p n) ≃
    MulAction.orbitRel.Quotient (CSp F n)
      (FullCharacterPair F K p n (source.toLiteralSource zero descent dualRoots).unipotent) :=
  Quotient.congr (pairEquiv source zero descent dualRoots)
    (orbitRel_iff source zero descent dualRoots)

@[simp]
theorem orbitEquiv_mk (l : OccurringPair F p n) :
    orbitEquiv source zero descent dualRoots (Quotient.mk _ l) =
      Quotient.mk _ (pairEquiv source zero descent dualRoots l) := rfl

@[simp]
theorem orbitEquiv_symm_mk
    (l : FullCharacterPair F K p n (source.toLiteralSource zero descent dualRoots).unipotent) :
    (orbitEquiv source zero descent dualRoots).symm (Quotient.mk _ l) =
      Quotient.mk _ ((pairEquiv source zero descent dualRoots).symm l) := rfl

end ModularRep.PaperProofs.TypeBFLZOccurringPairOrbits


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
