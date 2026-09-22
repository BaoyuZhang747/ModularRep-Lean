import ModularRep.PaperProofs.TypeBFLZPolynomialDuality
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Data.Fintype.Sets

/-!
# Exact standard primary-polynomial inputs for literal FLZ labels

The finite odd field, rank and prime scope are explicit source indices.
Every clause concerns the actual conformal symplectic element whose order
is prime to p, its multiplier, and its characteristic polynomial on the fixed
symplectic space. In particular, multiplicities are the existing guarded
polynomial divisor multiplicities, not a separately supplied function.

The standard source is FLZ, J. Algebra 604 (2022), Section 3.2, p. 542,
and Lemma 3.1(iv), p. 543. The F1 root clause uses the canonical algebraic
closure of the defining finite field, with its actual coefficient map.
This has no relation to an ordinary modular-system fraction field.

F2 components are products of two distinct irreducibles. Equal paired
exponents are retained to identify their product-divisor multiplicity
with the printed primary multiplicity. No primary-kernel dimension,
centralizer isomorphism, character equivalence, action or target is an
input. Source realization and the subsequent E2 character assignment
remain separate obligations.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBFLZPrimarySource

open scoped Classical
open Polynomial TypeBCliffordCarriers TypeBConformalDualCarriers
open TypeBFLZLabelSource TypeBFLZCoreProfileConjugacy TypeBFLZPolynomialComponents

universe u

variable {F : Type u} [Field F] {p ell f n : ℕ}

/-- The actual endomorphism whose characteristic polynomial is used. -/
def primaryLinearMap (s : SemisimpleParameter F p n) :
    Module.End F (SymplecticSpace F n) :=
  (linearPart F n s.val).toLinearMap

@[simp]
theorem primaryLinearMap_apply (s : SemisimpleParameter F p n)
    (v : SymplecticSpace F n) :
    primaryLinearMap s v = linearPart F n s.val v := rfl

@[simp]
theorem primaryProfile_charpoly (s : SemisimpleParameter F p n) :
    (semisimpleProfile s).2 = LinearMap.charpoly (primaryLinearMap s) := rfl

/-- The existing polynomial multiplicity, with actual nonzeroness proved. -/
def primaryMultiplicity (s : SemisimpleParameter F p n)
    (Gamma : ProfileComponent (semisimpleProfile s)) : ℕ :=
  natComponentMultiplicity (semisimpleProfile s)
    (semisimpleProfile_polynomial_ne_zero s) Gamma

@[simp]
theorem primaryMultiplicity_eq (s : SemisimpleParameter F p n)
    (Gamma : ProfileComponent (semisimpleProfile s)) :
    primaryMultiplicity s Gamma = multiplicity Gamma.val (semisimpleProfile s).2 := rfl

variable [Finite F] [CharP F p]

/-- E1 standard primary interpretation on the literal finite similitude
carrier. FLZ Section 3.2 and Lemma 3.1 retain precisely these polynomial
and root statements; the all-roots norm formulation is the standard
Frobenius-orbit consequence of the same irreducible selfdual condition.
The parameters and applicability remain explicit constructor indices. -/
structure PrimarySource (parameters : OddFieldParameters F p f)
    (scope : Applicability p ell n) where
  support : ∀ s : SemisimpleParameter F p n,
    Finset (ProfileComponent (semisimpleProfile s))
  mem_support : ∀ (s : SemisimpleParameter F p n)
      (Gamma : ProfileComponent (semisimpleProfile s)),
    Gamma ∈ support s ↔ 0 < componentMultiplicity (semisimpleProfile s) Gamma
  factorization : ∀ s : SemisimpleParameter F p n,
    (semisimpleProfile s).2 =
      ∏ Gamma ∈ support s, Gamma.val ^ primaryMultiplicity s Gamma
  paired_exponents : ∀ (s : SemisimpleParameter F p n) (delta : Polynomial F),
    delta.Monic → Irreducible delta → delta ≠ X →
      delta ≠ xiDual (semisimpleProfile s).1 delta →
      emultiplicity delta (semisimpleProfile s).2 =
        emultiplicity (xiDual (semisimpleProfile s).1 delta) (semisimpleProfile s).2
  f0_even : ∀ (s : SemisimpleParameter F p n)
      (Gamma : ProfileComponent (semisimpleProfile s)),
    IsF0 (semisimpleProfile s).1 Gamma.val → Even (primaryMultiplicity s Gamma)
  f1_even : ∀ (s : SemisimpleParameter F p n)
      (Gamma : ProfileComponent (semisimpleProfile s)),
    IsF1 (semisimpleProfile s).1 Gamma.val → Even Gamma.val.natDegree
  f1_root_norm : ∀ (s : SemisimpleParameter F p n)
      (Gamma : ProfileComponent (semisimpleProfile s)),
    IsF1 (semisimpleProfile s).1 Gamma.val →
      ∀ alpha : AlgebraicClosure F,
        (Gamma.val.map (algebraMap F (AlgebraicClosure F))).IsRoot alpha →
        alpha ^ (Nat.card F ^ (Gamma.val.natDegree / 2) + 1) =
          algebraMap F (AlgebraicClosure F) ((semisimpleProfile s).1 : F)

variable {parameters : OddFieldParameters F p f} {scope : Applicability p ell n}
variable (source : PrimarySource parameters scope)

/-- The support names exactly the actual polynomial divisors. -/
theorem PrimarySource.support_dvd (s : SemisimpleParameter F p n)
    (Gamma : ProfileComponent (semisimpleProfile s)) :
    Gamma ∈ source.support s ↔ Gamma.val ∣ (semisimpleProfile s).2 :=
  (source.mem_support s Gamma).trans
    (componentMultiplicity_pos_iff (semisimpleProfile s) Gamma)

/-- Restrict only the proof of occurrence; the component polynomial is
unchanged. No label or primary decomposition equivalence is supplied. -/
def PrimarySource.occurringEquivSupport (s : SemisimpleParameter F p n) :
    OccurringComponent (semisimpleProfile s) ≃ source.support s where
  toFun Gamma := ⟨Gamma.val, (source.mem_support s Gamma.val).mpr Gamma.property⟩
  invFun Gamma := ⟨Gamma.val, (source.mem_support s Gamma.val).mp Gamma.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem PrimarySource.occurringEquivSupport_val (s : SemisimpleParameter F p n)
    (Gamma : OccurringComponent (semisimpleProfile s)) :
    (source.occurringEquivSupport s Gamma).val = Gamma.val := rfl

include source in
/-- Finiteness is deduced from the exact support, not another source field. -/
theorem PrimarySource.occurring_finite (s : SemisimpleParameter F p n) :
    Finite (OccurringComponent (semisimpleProfile s)) :=
  Finite.of_injective (source.occurringEquivSupport s)
    (source.occurringEquivSupport s).injective

end ModularRep.PaperProofs.TypeBFLZPrimarySource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
