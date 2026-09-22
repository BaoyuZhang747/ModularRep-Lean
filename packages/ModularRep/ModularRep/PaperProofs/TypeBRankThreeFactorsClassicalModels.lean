import ModularRep.PaperProofs.TypeBRegularLeviRationalCarriers
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.SymplecticGroup

/-!
# Literal classical fixed-point models for one Levi component

These are standard algebraic matrix carriers, with the actual matrix equation
for their q-power or graph-field map. They are not free finite groups tagged
with a Dynkin type. The unitary model is the fixed subgroup of transpose-inverse
composed with entrywise q-power on SL3 over the algebraic closure; no q-power
star is installed on that whole closure. An identification with SU3 over a
quadratic finite field is unnecessary for this explicit fixed-point carrier.

E1 source: the named matrix map is an automorphism on the standard algebraic
group at the retained defining field parameter. MT Theorem 22.5 and Example
22.6, pp. 191--192; DM (2020, second edition), Example 4.3.3, p. 71.
The value equation determines this map uniquely. The consumer must pass the
same q = Nat.card F from its specified Clifford/Frobenius source. This module
does not choose the form of a component or prove the manuscript inventory.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRankThreeFactorsClassicalModels

open TypeBRegularLeviRationalCarriers

/-- One-component standard forms. Product configurations are not input data. -/
inductive Form where
  | a1
  | a2
  | unitaryA2
  | b2
  deriving DecidableEq

def MatrixIndex : Form → Type
  | .a1 => Fin 2
  | .a2 => Fin 3
  | .unitaryA2 => Fin 3
  | .b2 => Fin 2 ⊕ Fin 2

instance matrixIndexFintype (form : Form) : Fintype (MatrixIndex form) := by
  cases form <;> dsimp [MatrixIndex] <;> infer_instance

instance matrixIndexDecidableEq (form : Form) : DecidableEq (MatrixIndex form) := by
  cases form <;> dsimp [MatrixIndex] <;> infer_instance

/-- B2 is realized by the simply connected Sp4 model, with mathlib's literal J. -/
def AlgebraicGroup (A : Type) [Field A] : Form → Type
  | .a1 => Matrix.SpecialLinearGroup (Fin 2) A
  | .a2 => Matrix.SpecialLinearGroup (Fin 3) A
  | .unitaryA2 => Matrix.SpecialLinearGroup (Fin 3) A
  | .b2 => Matrix.symplecticGroup (Fin 2) A

instance algebraicGroupGroup (A : Type) [Field A] (form : Form) :
    Group (AlgebraicGroup A form) := by
  cases form <;> dsimp [AlgebraicGroup] <;> infer_instance

/-- Preserve the actual entries, rather than an abstract isomorphism class. -/
def toMatrix {A : Type} [Field A] (form : Form) :
    AlgebraicGroup A form → Matrix (MatrixIndex form) (MatrixIndex form) A := by
  cases form <;> exact fun g => g.val

theorem toMatrix_injective {A : Type} [Field A] (form : Form) :
    Function.Injective (toMatrix (A := A) form) := by
  cases form <;> exact Subtype.val_injective

/-- The prescribed matrix operation. Transpose-inverse is the unitary graph
operation; its difference from a chosen pinned graph map belongs in the
displayed inner twist of the one-component normalization certificate. -/
def matrixOperation {A : Type} [Field A] (form : Form) (q : ℕ)
    (g : AlgebraicGroup A form) : Matrix (MatrixIndex form) (MatrixIndex form) A :=
  if form = .unitaryA2 then
    Matrix.transpose ((toMatrix form g).map (fun x => x ^ q))⁻¹
  else (toMatrix form g).map (fun x => x ^ q)

/-- A narrow standard source, with its full matrix-value equation. -/
structure StandardFrobenius (F A : Type) [Field F] [Finite F] [Field A]
    (form : Form) where
  automorphism : MulAut (AlgebraicGroup A form)
  matrix_value : ∀ g, toMatrix form (automorphism g) =
    matrixOperation form (Nat.card F) g

namespace StandardFrobenius

variable {F A : Type} [Field F] [Finite F] [Field A] {form : Form}

/-- There is no choice of a different rational action hidden in this source. -/
theorem automorphism_unique (first second : StandardFrobenius F A form) :
    first.automorphism = second.automorphism := by
  ext g
  apply toMatrix_injective form
  rw [first.matrix_value, second.matrix_value]

/-- The model is the literal fixed subgroup of the displayed matrix map. -/
abbrev RationalModel (source : StandardFrobenius F A form) : Type :=
  fixedPoints source.automorphism.toMonoidHom

/-- Every model element satisfies the defining q/graph-field matrix equation. -/
theorem rationalModel_equation (source : StandardFrobenius F A form)
    (g : source.RationalModel) :
    toMatrix form g.val = matrixOperation form (Nat.card F) g.val :=
  (congrArg (toMatrix form) g.property).symm.trans (source.matrix_value g.val)

end StandardFrobenius

end ModularRep.PaperProofs.TypeBRankThreeFactorsClassicalModels


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
