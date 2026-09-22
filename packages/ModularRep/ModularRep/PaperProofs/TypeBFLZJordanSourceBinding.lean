import ModularRep.PaperProofs.TypeBFLZOccurringPairOrbits
import ModularRep.PaperProofs.TypeBFLZCyclotomicModel

/-!
# The same published Jordan assignment in the rational-series source

The source values are prescribed first on the actual occurring unipotent
characters, in one rational cyclotomic field. The exact FLZ equation (3.4)
certificate identifies its ordinary assignment with those values and gives
the full ordinary classification and rational-series membership.

The actual occurring/full-character pair equivalence constructs the old
Equation34Source. Its classification and its pointwise values are proved to
be those of the SAME prescribed assignment. No block, Brauer matching or
numbered manuscript conclusion is a source field.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBFLZJordanSourceBinding

open ModularRep OrdinaryIrreducibleCharacter
open TypeBCliffordCarriers TypeBConformalDualCarriers TypeBFLZLabelSource
open TypeBFLZOccurringCharacterSource TypeBFLZOccurringPairOrbits
open TypeBFLZCentralizerConjugacy TypeBFLZCyclotomicModel

universe u
variable {F K : Type u} [Field F] [Finite F] [Field K] [CharZero K]
variable {p ell f n : ℕ} [CharP F p] [Finite (Clifford n F)]
variable {parameters : OddFieldParameters F p f} {scope : Applicability p ell n}
variable {primary : TypeBFLZPrimarySource.PrimarySource parameters scope}
variable (source : OccurringCharacterSource (K := K) parameters scope primary)

/-- The actual published occurring family inside the full centralizer Irr. -/
abbrev PublishedUnipotent (s : SemisimpleParameter F p n) :=
  {chi : Irr (AlgebraicClosure K) (parameterCentralizer F p n s) //
    ∃ mu : OccurringLabels s, source.character s mu = chi}

def publishedLabel (s : SemisimpleParameter F p n) (mu : OccurringLabels s) :
    PublishedUnipotent source s := ⟨source.character s mu, mu, rfl⟩

@[simp] theorem publishedLabel_val (s : SemisimpleParameter F p n) (mu : OccurringLabels s) :
    (publishedLabel source s mu).val = source.character s mu := rfl

/-- Prescribed published Jordan values. Only the actual unipotent image is
in scope; no Jordan map on every centralizer irreducible is requested. -/
abbrev JordanValues := ∀ s : SemisimpleParameter F p n,
  PublishedUnipotent source s → SpecialClifford n F → ValueField F n

local instance occurringAction : MulAction (CSp F n) (OccurringPair F p n) :=
  pairAction

variable (choice : Choice (F := F) (n := n) K)

/-- E2: FLZ equation (3.4), p.545, and rational Jordan-series membership,
on the actual occurring pairs and ALL ordinary characters over split K.
The independent value family is evaluated on the SAME centralizer character.
Its interpretation as the published Jordan family remains an explicit source
obligation, not a consequence of arbitrary classification or value data. -/
structure JordanCertificate (values : JordanValues source)
    [ordinaryCharacteristic : CharZero K] where
  classification :
    MulAction.orbitRel.Quotient (CSp F n) (OccurringPair F p n) ≃
      Irr K (SpecialClifford n F)
  value : ∀ (P : OccurringPair F p n) (x : SpecialClifford n F),
    algebraMap K (AlgebraicClosure K) (classification (Quotient.mk _ P) x) =
      choice.closureEmbedding (values P.1 (publishedLabel source P.1 P.2) x)
  rationalSeries : SemisimpleParameter F p n → Irr K (SpecialClifford n F) → Prop
  rational_membership : ∀ (s : SemisimpleParameter F p n) (P : OccurringPair F p n),
    rationalSeries s (classification (Quotient.mk _ P)) ↔ IsConj s.val P.1.val

variable {source choice} {values : JordanValues source}
variable (J : JordanCertificate source choice values)
variable (zero : TypeBFLZZeroLabelProduct.ZeroSymbolCertificate)
variable (descent : TypeBFLZCentralizerCharacterDescent.DescentCertificate
  (F := F) (K := K) (p := p) (n := n))

local instance actualFullPairAction
    (dualRoots : HasEnoughRootsOfUnity K (Nat.card (CSp F n))) : MulAction (CSp F n)
    (FullCharacterPair F K p n (source.toLiteralSource zero descent dualRoots).unipotent) :=
  fullPairAction (source.toLiteralSource zero descent dualRoots).unipotent
    (source.toLiteralSource zero descent dualRoots).stable

/-- Compose only the constructed actual orbit equivalence with the source's
published Jordan assignment; the rational-series predicate is unchanged. -/
def JordanCertificate.toEquation34 : TypeBFLZLabelSplittingSource.Equation34Source
    (ell := ell) (source.toLiteralSource zero descent choice.dualRoots).unipotent where
  hypotheses := scope
  field_finite := inferInstance
  field_characteristic := inferInstance
  ordinary_characteristic := inferInstance
  ordinary_roots := choice.ordinaryRoots
  dual_roots := choice.dualRoots
  clifford_finite := inferInstance
  rationalSeries := J.rationalSeries
  parameter_conjugation := fullPairAction_parameter _ _
  classification := (orbitEquiv source zero descent choice.dualRoots).symm.trans J.classification
  rational_membership s l := by
    obtain ⟨P, rfl⟩ := (pairEquiv source zero descent choice.dualRoots).surjective l
    change J.rationalSeries s
      (J.classification ((orbitEquiv source zero descent choice.dualRoots).symm
        (Quotient.mk _ (pairEquiv source zero descent choice.dualRoots P)))) ↔ _
    rw [← orbitEquiv_mk, Equiv.symm_apply_apply]
    exact J.rational_membership s P

/-- The full ordinary character is literally the published pair assignment. -/
theorem JordanCertificate.fullCharacter_pair (P : OccurringPair F p n) :
    (J.toEquation34 zero descent).fullCharacter
        (pairEquiv source zero descent choice.dualRoots P) =
      J.classification (Quotient.mk _ P) := by
  change J.classification ((orbitEquiv source zero descent choice.dualRoots).symm
    (Quotient.mk _ (pairEquiv source zero descent choice.dualRoots P))) = _
  rw [← orbitEquiv_mk, Equiv.symm_apply_apply]

/-- This value equation reaches the actual Equation34Source consumed by
the block, full-union and integral-series certificates. -/
theorem JordanCertificate.fullCharacter_value (P : OccurringPair F p n)
    (x : SpecialClifford n F) :
    algebraMap K (AlgebraicClosure K)
        ((J.toEquation34 zero descent).fullCharacter
          (pairEquiv source zero descent choice.dualRoots P) x) =
      choice.closureEmbedding (values P.1 (publishedLabel source P.1 P.2) x) := by
  rw [J.fullCharacter_pair zero descent]
  exact J.value P x

/-- Injectivity of the fixed coefficient inclusion also gives values in K. -/
theorem JordanCertificate.fullCharacter_value_in_K (P : OccurringPair F p n)
    (x : SpecialClifford n F) :
    (J.toEquation34 zero descent).fullCharacter
        (pairEquiv source zero descent choice.dualRoots P) x =
      choice.embedding (values P.1 (publishedLabel source P.1 P.2) x) :=
  (choice.value_eq_iff _ _).mp (J.fullCharacter_value zero descent P x)

/-- The source predicate is the SAME prescribed rational Lusztig series. -/
theorem JordanCertificate.rationalSeries_eq (s : SemisimpleParameter F p n)
    (chi : Irr K (SpecialClifford n F)) :
    (J.toEquation34 zero descent).rationalSeries s chi = J.rationalSeries s chi := rfl

/-- The source's ordinary-root guard is the common cyclotomic model guard. -/
theorem JordanCertificate.ordinaryRoots_eq :
    (J.toEquation34 zero descent).ordinary_roots = choice.ordinaryRoots := rfl

end ModularRep.PaperProofs.TypeBFLZJordanSourceBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
