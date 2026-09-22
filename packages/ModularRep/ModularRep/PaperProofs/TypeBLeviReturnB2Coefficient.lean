import ModularRep.PaperProofs.TypeBLeviReturnPowerModel
import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.FieldTheory.Finite.Basic

/-!
# The literal Sp4 coefficient model for the common return Frobenius

Both matrix Frobenius maps and the coefficient homomorphism are defined
entrywise on mathlib's symplectic group, whose form is the literal matrix
J = fromBlocks 0 (-1) 1 0. The sole optional finite-field E1 boundary is
scalar descent along the specified algebraMap. Matrix descent, the fixed
range, the finite equivalence and the return-power square are deductions.

The application uses b = primeStep * u and f = b * s. It composes the
coefficient equivalence below with normalizedFixedEquiv, using the same
original component embedding and a single Lang element for both powers.
No freely chosen common map, finite-model equivalence, normalized return,
character action, selector or stabilizer conclusion is an input here.

Scalar descent is the standard finite-field root statement for X^(p^f)-X;
its specified coefficient embedding and cardinality must be instantiated.
The original algebraic component and Lang source remain in the consumer.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBLeviReturnB2Coefficient

open TypeBRegularLeviRationalCarriers TypeBLeviReturnPowerAutomorphism

/-- The actual four-dimensional symplectic matrix group with the literal J. -/
abbrev Sp4 (R : Type*) [CommRing R] := Matrix.symplecticGroup (Fin 2) R

abbrev MatrixIndex := Fin 2 ⊕ Fin 2

section Maps

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Entrywise coefficient change, preserving the actual alternating matrix. -/
def spMap (f : R →+* S) : Sp4 R →* Sp4 S where
  toFun g := ⟨g.val.map f, SymplecticGroup.map_mem g.property f⟩
  map_one' := Subtype.ext f.mapMatrix.map_one
  map_mul' g h := Subtype.ext (f.mapMatrix.map_mul g.val h.val)

@[simp] theorem spMap_apply (f : R →+* S) (g : Sp4 R)
    (i j : MatrixIndex) : (spMap f g).val i j = f (g.val i j) := rfl

theorem spMap_injective (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (spMap f) := by
  intro g h equality
  apply Subtype.ext
  apply Matrix.map_injective hf
  exact congrArg Subtype.val equality

/-- An actual coefficient isomorphism acts on the same symplectic matrices. -/
def spMapEquiv (e : R ≃+* S) : Sp4 R ≃* Sp4 S where
  toFun := spMap e.toRingHom
  invFun := spMap e.symm.toRingHom
  left_inv g := by
    apply Subtype.ext
    ext i j
    exact e.symm_apply_apply (g.val i j)
  right_inv g := by
    apply Subtype.ext
    ext i j
    exact e.apply_symm_apply (g.val i j)
  map_mul' g h := (spMap e.toRingHom).map_mul g h

@[simp] theorem spMapEquiv_apply (e : R ≃+* S) (g : Sp4 R)
    (i j : MatrixIndex) : (spMapEquiv e g).val i j = e (g.val i j) := rfl

/-- The canonical action of coefficient automorphisms, with no action input. -/
def spMapAction : (R ≃+* R) →* MulAut (Sp4 R) where
  toFun := spMapEquiv
  map_one' := by
    apply MulEquiv.ext
    intro g
    apply Subtype.ext
    rfl
  map_mul' e f := by
    apply MulEquiv.ext
    intro g
    apply Subtype.ext
    rfl

end Maps

section Common

variable (A : Type*) [Field A] (p : ℕ) [Fact p.Prime] [CharP A p]

/-- The common Frobenius is the specified entrywise p^b map. -/
def commonFrobenius (b : ℕ) : Monoid.End (Sp4 A) :=
  spMap (iterateFrobenius A p b)

@[simp] theorem commonFrobenius_apply (b : ℕ) (g : Sp4 A)
    (i j : MatrixIndex) :
    (commonFrobenius A p b g).val i j = g.val i j ^ (p ^ b) := rfl

/-- Composition powers retain their literal common prime-field exponent. -/
theorem commonFrobenius_pow_apply (b t : ℕ) (g : Sp4 A)
    (i j : MatrixIndex) :
    ((commonFrobenius A p b ^ t) g).val i j = g.val i j ^ (p ^ (b * t)) := by
  induction t with
  | zero => simp
  | succ t ih =>
      calc
        ((commonFrobenius A p b ^ (t + 1)) g).val i j =
            (commonFrobenius A p b ((commonFrobenius A p b ^ t) g)).val i j := by
          rw [pow_succ'] <;> rfl
        _ = (((commonFrobenius A p b ^ t) g).val i j) ^ (p ^ b) := rfl
        _ = g.val i j ^ (p ^ (b * (t + 1))) := by
          rw [ih, ← pow_mul, ← pow_add, ← Nat.mul_succ]

end Common

section FiniteField

variable (FQ : Type*) [Field FQ] [Finite FQ]
variable (p : ℕ) [Fact p.Prime] [CharP FQ p]

/-- The actual finite prime-field automorphism, acting entrywise. -/
def fieldGenerator : MulAut (Sp4 FQ) := spMapEquiv (frobeniusEquiv FQ p)

@[simp] theorem fieldGenerator_apply (g : Sp4 FQ) (i j : MatrixIndex) :
    (fieldGenerator FQ p g).val i j = g.val i j ^ p := rfl

theorem fieldGenerator_pow_apply (t : ℕ) (g : Sp4 FQ) (i j : MatrixIndex) :
    ((fieldGenerator FQ p ^ t) g).val i j = g.val i j ^ (p ^ t) := by
  induction t with
  | zero => simp
  | succ t ih =>
      calc
        ((fieldGenerator FQ p ^ (t + 1)) g).val i j =
            (fieldGenerator FQ p ((fieldGenerator FQ p ^ t) g)).val i j := by
          rw [pow_succ'] <;> rfl
        _ = (((fieldGenerator FQ p ^ t) g).val i j) ^ p := rfl
        _ = g.val i j ^ (p ^ (t + 1)) := by
          rw [ih, ← pow_mul, ← pow_succ]

end FiniteField

section Coefficients

variable (FQ A : Type*) [Field FQ] [Field A] [Algebra FQ A]

/-- The fixed coefficient inclusion is the actual algebraMap on each entry. -/
def coefficientMap : Sp4 FQ →* Sp4 A := spMap (algebraMap FQ A)

@[simp] theorem coefficientMap_apply (g : Sp4 FQ) (i j : MatrixIndex) :
    (coefficientMap FQ A g).val i j = algebraMap FQ A (g.val i j) := rfl

theorem coefficientMap_injective : Function.Injective (coefficientMap FQ A) :=
  spMap_injective (algebraMap FQ A) (algebraMap FQ A).injective

/-- The geometric characteristic is derived from the same coefficient map. -/
theorem coefficient_charP (p : ℕ) [CharP FQ p] : CharP A p :=
  charP_of_injective_algebraMap (algebraMap FQ A).injective p

variable [Finite FQ]
variable (p b f s : ℕ) [Fact p.Prime] [CharP FQ p] [CharP A p]
variable (cardinality : Nat.card FQ = p ^ f) (exponent : f = b * s)

include cardinality in
private theorem scalar_fixed (a : FQ) :
    (algebraMap FQ A a) ^ (p ^ f) = algebraMap FQ A a := by
  letI : Fintype FQ := Fintype.ofFinite FQ
  have value : a ^ (p ^ f) = a := by
    rw [← cardinality, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card a
  rw [← map_pow, value]

include cardinality exponent in
/-- Every actual coefficient matrix lies in the displayed defining fixed group. -/
theorem coefficientMap_fixed (g : Sp4 FQ) :
    (commonFrobenius A p b ^ s) (coefficientMap FQ A g) = coefficientMap FQ A g := by
  apply Subtype.ext
  ext i j
  rw [commonFrobenius_pow_apply, coefficientMap_apply, ← exponent]
  exact scalar_fixed FQ A p f cardinality (g.val i j)

/- The only optional E1 input is scalar descent on this exact coefficient map.
Matrix membership and the full symplectic fixed range are derived below. -/
variable (scalarDescent : ∀ x : A, x ^ (p ^ f) = x →
  ∃ a : FQ, algebraMap FQ A a = x)

include cardinality exponent scalarDescent in
theorem coefficientMap_range :
    (coefficientMap FQ A).range = fixedPoints (commonFrobenius A p b ^ s) := by
  classical
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact coefficientMap_fixed FQ A p b f s cardinality exponent g
  · intro hx
    have hfixed : (commonFrobenius A p b ^ s) x = x := hx
    have entries : ∀ i j : MatrixIndex, ∃ a : FQ,
        algebraMap FQ A a = x.val i j := by
      intro i j
      apply scalarDescent
      have value := congrArg (fun z : Sp4 A ↦ z.val i j) hfixed
      rw [commonFrobenius_pow_apply] at value
      simpa only [← exponent] using value
    choose a₀ ha using entries
    let a : Matrix MatrixIndex MatrixIndex FQ := a₀
    have mapped : a.map (algebraMap FQ A) = x.val := Matrix.ext ha
    have symplectic : a ∈ Matrix.symplecticGroup (Fin 2) FQ := by
      apply SymplecticGroup.mem_iff.mpr
      apply Matrix.map_injective (algebraMap FQ A).injective
      simpa only [Matrix.map_mul (f := algebraMap FQ A),
        Matrix.transpose_map, Matrix.map_J, mapped] using
        (SymplecticGroup.mem_iff.mp x.property)
    exact ⟨⟨a, symplectic⟩, Subtype.ext mapped⟩

/-- Restrict the same coefficient homomorphism to the derived fixed range. -/
def coefficientToFixed : Sp4 FQ →* fixedPoints (commonFrobenius A p b ^ s) :=
  (coefficientMap FQ A).codRestrict _
    (coefficientMap_fixed FQ A p b f s cardinality exponent)

/-- The finite identification is constructed from coefficient injectivity and
the scalar-to-matrix fixed-range deduction, not supplied as a source. -/
def coefficientEquiv : Sp4 FQ ≃* fixedPoints (commonFrobenius A p b ^ s) :=
  MulEquiv.ofBijective (coefficientToFixed FQ A p b f s cardinality exponent)
    ⟨fun _ _ equality ↦ coefficientMap_injective FQ A
        (congrArg Subtype.val equality), by
      intro x
      have hx : x.val ∈ (coefficientMap FQ A).range := by
        rw [coefficientMap_range FQ A p b f s cardinality exponent scalarDescent]
        exact x.property
      obtain ⟨g, hg⟩ := hx
      exact ⟨g, Subtype.ext hg⟩⟩

@[simp] theorem coefficientEquiv_value (g : Sp4 FQ) :
    (coefficientEquiv FQ A p b f s cardinality exponent scalarDescent g).val =
      coefficientMap FQ A g := rfl

theorem coefficientEquiv_symm_value
    (x : fixedPoints (commonFrobenius A p b ^ s)) :
    coefficientMap FQ A
      ((coefficientEquiv FQ A p b f s cardinality exponent scalarDescent).symm x) =
      x.val := by
  have equality := congrArg (fun z : fixedPoints (commonFrobenius A p b ^ s) ↦ z.val)
    ((coefficientEquiv FQ A p b f s cardinality exponent scalarDescent).apply_symm_apply x)
  simpa only [coefficientEquiv_value] using equality

/-- Every common power has the same literal finite-field coefficient value. -/
theorem coefficient_power_square (r : ℕ) (g : Sp4 FQ) :
    (commonFrobenius A p b ^ r) (coefficientMap FQ A g) =
      coefficientMap FQ A ((fieldGenerator FQ p ^ (b * r)) g) := by
  apply Subtype.ext
  ext i j
  simp only [commonFrobenius_pow_apply, coefficientMap_apply,
    fieldGenerator_pow_apply, map_pow]

/-- Orientation for the original-return consumer: the same coefficient
equivalence intertwines the actual finite field power and fixedPowerAut. -/
theorem coefficientEquiv_field_power (r : ℕ) (hs : 0 < s) (g : Sp4 FQ) :
    coefficientEquiv FQ A p b f s cardinality exponent scalarDescent
      ((fieldGenerator FQ p ^ (b * r)) g) =
    fixedPowerAut (commonFrobenius A p b) r s hs
      (coefficientEquiv FQ A p b f s cardinality exponent scalarDescent g) := by
  apply Subtype.ext
  change coefficientMap FQ A ((fieldGenerator FQ p ^ (b * r)) g) =
    (commonFrobenius A p b ^ r) (coefficientMap FQ A g)
  exact (coefficient_power_square FQ A p b r g).symm

/-- Conjugation uses the same coefficient equivalence, preserving the exact
positive exponent b*r without introducing an extra inverse. -/
theorem coefficientEquiv_conjugates_power (r : ℕ) (hs : 0 < s) :
    MulAut.congr (coefficientEquiv FQ A p b f s cardinality exponent scalarDescent).symm
      (fixedPowerAut (commonFrobenius A p b) r s hs) =
        fieldGenerator FQ p ^ (b * r) := by
  let e := coefficientEquiv FQ A p b f s cardinality exponent scalarDescent
  apply MulEquiv.ext
  intro g
  apply e.injective
  change e (e.symm (fixedPowerAut (commonFrobenius A p b) r s hs (e g))) =
    e ((fieldGenerator FQ p ^ (b * r)) g)
  rw [e.apply_symm_apply]
  exact (coefficientEquiv_field_power FQ A p b f s cardinality exponent scalarDescent
    r hs g).symm

end Coefficients

end ModularRep.PaperProofs.TypeBLeviReturnB2Coefficient


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
