import ManuscriptIBAW.Characters.CyclotomicOrdinaryLabels
import ModularRep.PaperProofs.TypeBOrthogonalOmegaCarriers
import ModularRep.PaperProofs.TypeCOddPrimeConformalCriterionCarriers

/-!
# Rational ℓ′ series for Type C over a field of odd order

The finite dual groups are the specified split SO and special Clifford
(GSpin) groups. Identifying the series with rational Lusztig series remains
an explicit assumption. These series are indexed by all semisimple elements.
For a prime ℓ, take the union indexed by elements of order prime to ℓ.

The ordinary coefficient interpretation fixes two embeddings of one finite
cyclotomic field and the same character values. It assumes neither a map
from C to K nor algebraic closure of K. The interpretation and partition
laws are explicit assumptions (E1/E2).
-/

noncomputable section
open scoped MonoidAlgebra

namespace ManuscriptIBAW.TypeC.OddRationalSeries

open ModularRep OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs
open ManuscriptIBAW.Characters

variable (q : ℕ) (K H Dual : Type)
  [Field K] [CharZero K] [Group H] [Finite H] [Group Dual]

/-- The actual rational Lusztig partition and its ordinary coefficient
interpretation, fixed independently of the modular prime and basic set. In
the finite groups over the defining field, having order prime to q is
equivalent to semisimplicity. The `rational` relation must be the published
rational series on these specified groups. The partition laws alone do not
identify this relation with Lusztig series. -/
structure Interpretation where
  conductor : ℕ
  [nonzeroConductor : NeZero conductor]
  comparison : CyclotomicComparison conductor K H
  common : Irr K H → Irr (ValueField conductor) H
  complexCharacter : Irr K H → Irr ℂ H
  ordinary_value : ∀ chi g,
    comparison.ordinaryEmbedding (common chi g) = chi g
  complex_value : ∀ chi g,
    comparison.complexEmbedding (common chi g) = complexCharacter chi g
  rational : Irr ℂ H → Dual → Prop
  semisimple : ∀ chi s, rational chi s → (orderOf s).Coprime q
  conjugate : ∀ chi s x, rational chi (x * s * x⁻¹) ↔ rational chi s
  exhaustive : ∀ chi, ∃ s, rational chi s
  common_labels : ∀ chi s t, rational chi s → rational chi t →
    ∃ x, t = x * s * x⁻¹

attribute [instance] Interpretation.nonzeroConductor

namespace Interpretation

variable {q K H Dual} (R : Interpretation q K H Dual)

/-- The rational union indexed by semisimple elements of order prime to ell in
the dual group. -/
def ellPrime (ell : ℕ) (chi : Irr K H) : Prop :=
  ∃ s : Dual, (orderOf s).Coprime q ∧ (orderOf s).Coprime ell ∧
    R.rational (R.complexCharacter chi) s

/-- The coefficient interpretation cannot identify distinct ordinary characters:
the two embeddings see the same common field values. -/
theorem complexCharacter_injective : Function.Injective R.complexCharacter := by
  intro chi psi h
  apply OrdinaryIrreducibleCharacter.ext
  intro g
  have hv : R.common chi g = R.common psi g := by
    apply R.comparison.complexEmbedding.injective
    exact (R.complex_value chi g).trans
      ((congrArg (fun theta : Irr ℂ H => theta g) h).trans
        (R.complex_value psi g).symm)
  exact (R.ordinary_value chi g).symm.trans
    ((congrArg R.comparison.ordinaryEmbedding hv).trans (R.ordinary_value psi g))

/-- The character identities imply compatibility with every group automorphism. -/
theorem complexCharacter_twist (chi : Irr K H) (alpha : MulAut H) :
    R.complexCharacter (OrdinaryIrreducibleCharacter.twist K H chi alpha) =
      OrdinaryIrreducibleCharacter.twist ℂ H (R.complexCharacter chi) alpha := by
  apply OrdinaryIrreducibleCharacter.ext
  intro g
  have hv : R.common (OrdinaryIrreducibleCharacter.twist K H chi alpha) g =
      R.common chi (alpha g) := by
    apply R.comparison.ordinaryEmbedding.injective
    exact (R.ordinary_value _ g).trans (R.ordinary_value chi (alpha g)).symm
  exact (R.complex_value _ g).symm.trans
    ((congrArg R.comparison.complexEmbedding hv).trans (R.complex_value chi (alpha g)))

end Interpretation

variable (n : ℕ) (F : Type) [Field F] [Finite F]

/-- The dual of Sp on the specified split quadratic space of odd dimension. -/
abbrev Symplectic (K : Type) [Field K] [CharZero K] :=
  Interpretation (Nat.card F) K
    (TypeCOddPrimeConformalCriterionCarriers.SpSubgroup n F)
    (TypeBOrthogonalOmegaCarriers.SpecialOrthogonal n F)

/-- The dual of CSp on the fixed split Clifford algebra. -/
abbrev Conformal (K : Type) [Field K] [CharZero K] :=
  Interpretation (Nat.card F) K
    (OddTwoConformalProjectiveRealisation.CSp n F)
    (TypeBCliffordCarriers.SpecialClifford n F)

end ManuscriptIBAW.TypeC.OddRationalSeries

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
`docs/manuals/formalisation-companion.tex` and `audit/current/source-crosswalk.json`.
-/
