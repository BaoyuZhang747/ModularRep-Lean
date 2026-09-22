import ModularRep.PaperProofs.TypeBCliffordNormSquareQuotient
import ModularRep.PaperProofs.TypeBCliffordNormSurjectivity
import ModularRep.PaperProofs.TypeBCliffordCentreSource
import ModularRep.PaperProofs.TypeBFiniteFieldSquareClass
import ModularRep.PaperProofs.TypeBSpinDiagonalFieldQuotient

/-!
# The Spin diagonal source constructed from the actual norm

The norm is followed by the actual unit square-class quotient. Surjectivity
comes from explicit Clifford norm preimages. The exact kernel is the proved
Spin-scalar join, with the centre substituted using the narrow literal E1
centre certificate. No diagonal map, kernel, index or effective action is
supplied as an input.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBSpinDiagonalNormSource

open TypeBCliffordCarriers TypeBCliffordScalarNorm TypeBCliffordNormSquareQuotient
open TypeBCliffordCentreSource TypeBFiniteFieldSquareClass
open TypeBSpinStabilizer TypeBSpinDiagonalFieldQuotient

variable (n : ℕ) (F : Type) [Field F] [Finite F] (N : NormSource n F)

/-- The prescribed finite field has odd cardinality by its actual parameter equation. -/
theorem odd_card_of_parameters {p f : ℕ} [CharP F p]
    (parameters : OddFieldParameters F p f) : Odd (Nat.card F) := by
  rw [parameters.cardinality]
  exact parameters.odd.pow

/-- The diagonal homomorphism is the square class of the literal Clifford norm. -/
def normSquareClassMap (hOdd : Odd (Nat.card F)) :
    SpecialClifford n F →* DiagonalGroup :=
  (squareClassMap F hOdd).comp N.norm

theorem normSquareClassMap_apply (hOdd : Odd (Nat.card F)) (g : SpecialClifford n F) :
    normSquareClassMap n F N hOdd g = squareClassMap F hOdd (N.norm g) := rfl

/-- Surjectivity is a deduction from the explicit hyperbolic norm preimages. -/
theorem normSquareClassMap_surjective (hOdd : Odd (Nat.card F)) (rank : 1 ≤ n) :
    Function.Surjective (normSquareClassMap n F N hOdd) :=
  (squareClassMap_surjective F hOdd).comp
    (TypeBCliffordNormSurjectivity.norm_surjective n F rank N)

/-- The kernel is calculated before using any centre theorem. -/
theorem normSquareClassMap_kernel (hOdd : Odd (Nat.card F)) :
    (normSquareClassMap n F N hOdd).ker =
      SpinSubgroup n F N ⊔ (scalar n F).range := by
  change ((squareClassMap F hOdd).comp N.norm).ker = _
  rw [← MonoidHom.comap_ker, squareClassMap_kernel]
  exact square_norm_preimage n F N

/-- Literal scalar elements are killed because their norms are squares. -/
theorem normSquareClassMap_scalar (hOdd : Odd (Nat.card F)) (z : Fˣ) :
    normSquareClassMap n F N hOdd (scalar n F z) = 1 := by
  rw [normSquareClassMap_apply, norm_scalar, squareClassMap_sq]

/-- The former diagonal source is constructed, retaining only the matched
one-way external centre certificate on the same finite odd Clifford carrier. -/
def diagonalSource {p f : ℕ} [CharP F p]
    (parameters : OddFieldParameters F p f) (rank : 1 ≤ n)
    (centre : CentreSource n F parameters rank) : DiagonalSource N where
  diagonal := normSquareClassMap n F N (odd_card_of_parameters F parameters)
  surjective := normSquareClassMap_surjective n F N
    (odd_card_of_parameters F parameters) rank
  kernel := by
    change (normSquareClassMap n F N (odd_card_of_parameters F parameters)).ker =
      SpinSubgroup n F N ⊔ Subgroup.center (SpecialClifford n F)
    rw [normSquareClassMap_kernel, centre.center_eq_scalarRange]

theorem diagonalSource_apply {p f : ℕ} [CharP F p]
    (parameters : OddFieldParameters F p f) (rank : 1 ≤ n)
    (centre : CentreSource n F parameters rank) (g : SpecialClifford n F) :
    (diagonalSource n F N parameters rank centre).diagonal g =
      squareClassMap F (odd_card_of_parameters F parameters) (N.norm g) := rfl

end ModularRep.PaperProofs.TypeBSpinDiagonalNormSource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
