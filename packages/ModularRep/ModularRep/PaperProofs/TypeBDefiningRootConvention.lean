import ModularRep.PaperProofs.TypeBFLZCyclotomicModel
import ModularRep.PaperProofs.TypeBPrimitiveRootEquivalence
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# A defining-characteristic root convention on the actual finite scope

The part of the actual CSp order prime to the defining characteristic
divides the existing common cyclotomic conductor. Choose a primitive root
of that order in AlgebraicClosure F and pair it with the corresponding
power of the common number-field generator. The same power of Choice.root
gives the convention over K, with a pointwise square through Choice.embedding.

This is the finite root convention used to interpret the semisimple
parameter, not the modular ell-residue convention. No global isomorphism
on all prime-to-p torsion, torus, DL function, or character is asserted.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBDefiningRootConvention

open ModularRep TypeBCliffordCarriers TypeBConformalDualCarriers
open TypeBFLZCyclotomicModel

universe u

variable {F : Type u} [Field F] [Finite F] {p f n : ℕ}
variable [Finite (Clifford n F)]

/-- The actual dual finite group order with its defining-prime part removed. -/
abbrev exponent (F : Type u) [Field F] [Finite F] (p n : ℕ) : ℕ :=
  primeRegularExponent p (CSp F n)

theorem exponent_pos : 0 < exponent F p n :=
  primeRegularExponent_pos p (CSp F n)

instance exponent_neZero : NeZero (exponent F p n) :=
  ⟨(exponent_pos (F := F) (p := p) (n := n)).ne'⟩

theorem exponent_dvd_conductor : exponent F p n ∣ conductor F n :=
  (Nat.ordCompl_dvd (Nat.card (CSp F n)) p).trans (dual_order_dvd F n)

variable [CharP F p] (parameters : OddFieldParameters F p f)

include parameters in
theorem exponent_coprime : (exponent F p n).Coprime p :=
  (Nat.coprime_ordCompl parameters.prime (Nat.card_pos (α := CSp F n)).ne').symm

include parameters in
theorem exponent_cast_ne_zero : (exponent F p n : F) ≠ 0 := by
  intro hzero
  exact (parameters.prime.coprime_iff_not_dvd.mp
    (exponent_coprime (n := n) parameters).symm)
      ((CharP.cast_eq_zero_iff F p (exponent F p n)).mp hzero)

include parameters in
/-- The algebraic closure of the defining field supplies the primitive root. -/
theorem exists_definingRoot :
    ∃ z : AlgebraicClosure F, IsPrimitiveRoot z (exponent F p n) := by
  letI : NeZero (exponent F p n : F) := ⟨exponent_cast_ne_zero (n := n) parameters⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure F) (exponent F p n)

/-- This single choice fixes the defining-field side of the finite convention. -/
def definingRoot : AlgebraicClosure F :=
  (exists_definingRoot (n := n) parameters).choose

theorem definingRoot_primitive :
    IsPrimitiveRoot (definingRoot (n := n) parameters) (exponent F p n) :=
  (exists_definingRoot (n := n) parameters).choose_spec

/-- The required power of the already specified number-field generator. -/
def valueRoot : ValueField F n :=
  generator (F := F) (n := n) ^ (conductor F n / exponent F p n)

theorem valueRoot_primitive :
    IsPrimitiveRoot (valueRoot (F := F) (p := p) (n := n)) (exponent F p n) :=
  (generator_primitive (F := F) (n := n)).pow (conductor_pos F n)
    (Nat.div_mul_cancel (exponent_dvd_conductor (F := F) (p := p) (n := n))).symm

/-- The entire finite root group is paired by equal powers. -/
def valueEquiv : rootsOfUnity (exponent F p n) (AlgebraicClosure F) ≃*
    rootsOfUnity (exponent F p n) (ValueField F n) :=
  TypeBPrimitiveRootEquivalence.equiv (definingRoot_primitive (n := n) parameters)
    (valueRoot_primitive (F := F) (p := p) (n := n))

theorem valueEquiv_pow_value (j : ℕ) :
    (((valueEquiv (n := n) parameters
      ((definingRoot_primitive (n := n) parameters).toRootsOfUnity ^ j)) :
        (ValueField F n)ˣ) : ValueField F n) =
      valueRoot (F := F) (p := p) (n := n) ^ j :=
  TypeBPrimitiveRootEquivalence.equiv_pow_value
    (definingRoot_primitive (n := n) parameters)
    (valueRoot_primitive (F := F) (p := p) (n := n)) j

variable {K : Type u} [Field K] [CharZero K]
variable (choice : Choice (F := F) (n := n) K)

/-- The same common-root power in the prescribed ordinary field. -/
def ordinaryRoot : K := choice.root ^ (conductor F n / exponent F p n)

theorem ordinaryRoot_primitive :
    IsPrimitiveRoot (ordinaryRoot (p := p) choice) (exponent F p n) :=
  choice.primitive.pow (conductor_pos F n)
    (Nat.div_mul_cancel (exponent_dvd_conductor (F := F) (p := p) (n := n))).symm

theorem embedding_valueRoot :
    choice.embedding (valueRoot (F := F) (p := p) (n := n)) =
      ordinaryRoot (p := p) choice := by
  rw [valueRoot, map_pow, Choice.embedding_generator]
  rfl

/-- Equal powers define the convention over the same ordinary field K. -/
def ordinaryEquiv : rootsOfUnity (exponent F p n) (AlgebraicClosure F) ≃*
    rootsOfUnity (exponent F p n) K :=
  TypeBPrimitiveRootEquivalence.equiv (definingRoot_primitive (n := n) parameters)
    (ordinaryRoot_primitive (p := p) choice)

theorem ordinaryEquiv_pow_value (j : ℕ) :
    (((ordinaryEquiv parameters choice
      ((definingRoot_primitive (n := n) parameters).toRootsOfUnity ^ j)) : Kˣ) : K) =
      ordinaryRoot (p := p) choice ^ j :=
  TypeBPrimitiveRootEquivalence.equiv_pow_value
    (definingRoot_primitive (n := n) parameters)
    (ordinaryRoot_primitive (p := p) choice) j

/-- The number-field and ordinary-field conventions agree on every root. -/
theorem equiv_embedding (z : rootsOfUnity (exponent F p n) (AlgebraicClosure F)) :
    choice.embedding (((valueEquiv parameters z : (ValueField F n)ˣ) : ValueField F n)) =
      ((ordinaryEquiv parameters choice z : Kˣ) : K) := by
  obtain ⟨j, _, rfl⟩ := TypeBPrimitiveRootEquivalence.exists_pow
    (definingRoot_primitive (n := n) parameters) z
  rw [valueEquiv_pow_value, ordinaryEquiv_pow_value, map_pow, embedding_valueRoot]

/-- The same square after the existing canonical inclusion into the ordinary closure. -/
theorem equiv_closureEmbedding
    (z : rootsOfUnity (exponent F p n) (AlgebraicClosure F)) :
    choice.closureEmbedding
      (((valueEquiv parameters z : (ValueField F n)ˣ) : ValueField F n)) =
      algebraMap K (AlgebraicClosure K) ((ordinaryEquiv parameters choice z : Kˣ) : K) := by
  rw [Choice.closureEmbedding_apply, equiv_embedding]

end ModularRep.PaperProofs.TypeBDefiningRootConvention


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
