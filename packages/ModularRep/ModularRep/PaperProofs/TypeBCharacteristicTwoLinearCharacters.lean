import ModularRep.BrauerQuotientLinearCharacterAction
import Mathlib.Algebra.CharP.Reduced
import Mathlib.GroupTheory.FixedPointFree

/-!
# Odd order of the literal modular linear character group

The Gallagher twists are actual homomorphisms into the units of the
characteristic-two representation field, trivial on a specified subgroup.
Their finiteness is already proved in mathlib by restricting homomorphism
values to the finite roots of unity of the exponent of the domain group.
We reuse that result rather than assuming finiteness of the scalar group.

Frobenius injectivity rules out nontrivial involutions in these homomorphism
groups.  The checked fixed-point-free inversion theorem then gives odd
cardinality.  No external duality, maximal odd quotient, odd-cardinality
certificate, algebraic closure, or normality assumption is required.
In the Clifford application the subgroup below is literally
`TypeBLemma47LeviApplication.baseSubgroupInBrauerInertia`.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBCharacteristicTwoLinearCharacters

universe u

variable {k I : Type u} [Field k] [Group I] [Finite I]

/-- Mathlib's roots-of-unity evaluation argument gives finite modular
linear character groups even when the coefficient field is infinite. -/
theorem modularLinearCharacters_finite : Finite (I →* kˣ) := by
  infer_instance

/-- Restricting to the literal subgroup-trivial characters preserves
finiteness.  This is an explicit proof, not a newly registered instance. -/
theorem linearCharactersTrivialOn_finite (N : Subgroup I) :
    Finite (linearCharactersTrivialOn (k := k) N) := by
  letI := modularLinearCharacters_finite (k := k) (I := I)
  infer_instance

variable [CharP k 2]

/-- A field of characteristic two has no nonidentity unit of order two. -/
theorem unit_eq_one_of_square_eq_one (z : kˣ) (hz : z ^ 2 = 1) : z = 1 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply Units.ext
  apply frobenius_inj k 2
  change (z : k) ^ 2 = (1 : k) ^ 2
  have h := congrArg (fun u : kˣ ↦ (u : k)) hz
  simpa only [Units.val_pow_eq_pow_val, Units.val_one, one_pow] using h

/-- Pointwise evaluation transfers the absence of involutions to actual
modular linear characters. -/
theorem modularLinearCharacter_eq_one_of_square_eq_one
    (lambda : I →* kˣ) (hlambda : lambda ^ 2 = 1) : lambda = 1 := by
  apply MonoidHom.ext
  intro x
  apply unit_eq_one_of_square_eq_one
  have h := congrArg (fun mu : I →* kˣ ↦ mu x) hlambda
  simpa using h

theorem trivialLinearCharacter_eq_one_of_square_eq_one (N : Subgroup I)
    (lambda : linearCharactersTrivialOn (k := k) N)
    (hlambda : lambda ^ 2 = 1) : lambda = 1 := by
  apply Subtype.ext
  apply modularLinearCharacter_eq_one_of_square_eq_one
  exact congrArg Subtype.val hlambda

/-- The actual Gallagher twist carrier has odd cardinality.  Inversion is
an involutive homomorphism because this character group is commutative;
the preceding pointwise argument proves that its only fixed point is one. -/
theorem linearCharactersTrivialOn_odd_card (N : Subgroup I) :
    Odd (Nat.card (linearCharactersTrivialOn (k := k) N)) := by
  letI := linearCharactersTrivialOn_finite (k := k) N
  let inversion : linearCharactersTrivialOn (k := k) N →*
      linearCharactersTrivialOn (k := k) N := invMonoidHom
  have hfixed : MonoidHom.FixedPointFree inversion := by
    intro lambda hlambda
    change lambda⁻¹ = lambda at hlambda
    apply trivialLinearCharacter_eq_one_of_square_eq_one N lambda
    simpa only [pow_two] using (inv_eq_iff_mul_eq_one.mp hlambda)
  exact hfixed.odd_card_of_involutive (fun lambda ↦ inv_inv lambda)

end ModularRep.PaperProofs.TypeBCharacteristicTwoLinearCharacters


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
