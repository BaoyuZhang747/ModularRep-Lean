import ModularRep.PaperProofs.TypeBCliffordNormSurjectivity
import ModularRep.PaperProofs.TypeBCliffordOrthogonalSourceBinding
import ModularRep.PaperProofs.TypeBSplitQuadraticGeometry
import Mathlib.GroupTheory.OrderOfElement

/-!
# An explicit involution in the actual matrix Omega

The axis and a norm-one hyperbolic vector give an actual Spin element.
Its square is scalar minus one and its vector action negates the axis.
The fixed projection therefore gives a nonidentity matrix involution.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBMatrixOmegaEvenOrder

open TypeBCliffordCarriers TypeBCliffordNormSurjectivity
open TypeBCliffordOrthogonalAction TypeBCliffordScalarNorm
open TypeBCliffordOrthogonalSourceBinding TypeBOrthogonalOmegaCarriers

variable (n : ℕ) (F : Type) [Field F]

/-- These two displayed norm-one vectors are orthogonal. -/
theorem hyperbolic_axis_polar (i : Fin n) :
    QuadraticMap.polar (splitForm n F)
      (hyperbolicVector n F i 1) (axisVector n F) = 0 := by
  change (splitForm n F).polarBilin
    (hyperbolicVector n F i 1) (axisVector n F) = 0
  rw [TypeBSplitQuadraticGeometry.polarBilin_apply]
  simp [axisVector, hyperbolicVector]

/-- The Clifford anticommutation is restricted to this orthogonal pair. -/
theorem iota_hyperbolic_axis (i : Fin n) :
    CliffordAlgebra.ι (splitForm n F) (hyperbolicVector n F i 1) *
        CliffordAlgebra.ι (splitForm n F) (axisVector n F) =
      -(CliffordAlgebra.ι (splitForm n F) (axisVector n F) *
        CliffordAlgebra.ι (splitForm n F) (hyperbolicVector n F i 1)) := by
  have h := CliffordAlgebra.ι_mul_ι_add_swap (Q := splitForm n F)
    (hyperbolicVector n F i 1) (axisVector n F)
  rw [hyperbolic_axis_polar, map_zero] at h
  exact eq_neg_of_add_eq_zero_left h

/-- The existing vector-pair constructor on the same coordinate vectors. -/
def normOnePair (i : Fin n) : SpecialClifford n F :=
  vectorPair n F (axisVector n F) (hyperbolicVector n F i 1)
    (by rw [splitForm_axisVector]; exact one_ne_zero)
    (by rw [splitForm_hyperbolicVector]; exact one_ne_zero)

theorem normOnePair_norm (N : NormSource n F) (i : Fin n) :
    N.norm (normOnePair n F i) = 1 := by
  apply Units.ext
  simp only [normOnePair, norm_vectorPair, splitForm_axisVector,
    splitForm_hyperbolicVector, one_mul, Units.val_one]

/-- The square is the actual scalar minus one, before taking a quotient. -/
theorem normOnePair_square (i : Fin n) :
    normOnePair n F i ^ 2 = scalar n F (-1) := by
  apply toClifford_injective n F
  simp only [map_pow, normOnePair, toClifford_vectorPair, toClifford_scalar,
    Units.coe_neg_one, map_neg, map_one]
  let a := CliffordAlgebra.ι (splitForm n F) (axisVector n F)
  let b := CliffordAlgebra.ι (splitForm n F) (hyperbolicVector n F i 1)
  have aa : a * a = 1 := by
    dsimp only [a]
    rw [CliffordAlgebra.ι_sq_scalar, splitForm_axisVector, map_one]
  have bb : b * b = 1 := by
    dsimp only [b]
    rw [CliffordAlgebra.ι_sq_scalar, splitForm_hyperbolicVector, map_one]
  have ba : b * a = -(a * b) := iota_hyperbolic_axis n F i
  change (a * b) ^ 2 = -1
  calc
    (a * b) ^ 2 = a * (b * a) * b := by simp only [pow_two, mul_assoc]
    _ = -(a * a) * (b * b) := by
      rw [ba]
      simp only [mul_neg, neg_mul, mul_assoc]
    _ = -1 := by rw [aa, bb, mul_one]

/-- Conjugation by the pair sends the prescribed axis to its negative. -/
theorem normOnePair_axis_action (i : Fin n) :
    linearAction n F (normOnePair n F i) (axisVector n F) = -axisVector n F := by
  apply iota_injective n F
  rw [iota_action, map_neg]
  have anti : toClifford n F (normOnePair n F i) *
      CliffordAlgebra.ι (splitForm n F) (axisVector n F) =
      -(CliffordAlgebra.ι (splitForm n F) (axisVector n F) *
        toClifford n F (normOnePair n F i)) := by
    change (CliffordAlgebra.ι (splitForm n F) (axisVector n F) *
      CliffordAlgebra.ι (splitForm n F) (hyperbolicVector n F i 1)) *
        CliffordAlgebra.ι (splitForm n F) (axisVector n F) =
      -(CliffordAlgebra.ι (splitForm n F) (axisVector n F) *
        (CliffordAlgebra.ι (splitForm n F) (axisVector n F) *
          CliffordAlgebra.ι (splitForm n F) (hyperbolicVector n F i 1)))
    rw [mul_assoc, iota_hyperbolic_axis]
    simp only [mul_neg, mul_assoc]
  have cancel : toClifford n F (normOnePair n F i) *
      toClifford n F ((normOnePair n F i)⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  rw [anti, neg_mul, mul_assoc, cancel, mul_one]

/-- The same displayed pair belongs to the actual norm kernel. -/
def spinElement (N : NormSource n F) (i : Fin n) : Spin n F N :=
  ⟨normOnePair n F i, normOnePair_norm n F N i⟩

variable {p f : ℕ} [Finite F] [CharP F p]

/-- Its image uses the fixed vector-action projection onto matrix Omega. -/
def omegaElement (N : NormSource n F) (parameters : OddFieldParameters F p f)
    (rank : 3 ≤ n) (C : Source n F p f parameters rank N) (i : Fin n) : Omega n F :=
  spinProjection n F parameters rank N C (spinElement n F N i)

theorem omegaElement_square (N : NormSource n F) (parameters : OddFieldParameters F p f)
    (rank : 3 ≤ n) (C : Source n F p f parameters rank N) (i : Fin n) :
    omegaElement n F N parameters rank C i ^ 2 = 1 := by
  apply Subtype.ext
  change projection n F C.det_one (normOnePair n F i) ^ 2 = 1
  rw [← map_pow, normOnePair_square, projection_scalar]

theorem omegaElement_axis_action
    (N : NormSource n F) (parameters : OddFieldParameters F p f)
    (rank : 3 ≤ n) (C : Source n F p f parameters rank N) (i : Fin n) :
    omegaToLinear n F (omegaElement n F N parameters rank C i) (axisVector n F) =
      -axisVector n F :=
  normOnePair_axis_action n F i

theorem omegaElement_ne_one
    (N : NormSource n F) (parameters : OddFieldParameters F p f)
    (rank : 3 ≤ n) (C : Source n F p f parameters rank N) (i : Fin n) :
    omegaElement n F N parameters rank C i ≠ 1 := by
  intro h
  have action := omegaElement_axis_action n F N parameters rank C i
  rw [h, map_one] at action
  have value : (1 : F) = -1 := congrFun action none
  have two_zero : (2 : F) = 0 := by
    calc
      (2 : F) = 1 + 1 := one_add_one_eq_two.symm
      _ = -1 + 1 := congrArg (fun x : F => x + 1) value
      _ = 0 := neg_add_cancel 1
  exact TypeBSplitQuadraticGeometry.two_ne_zero_of_oddFieldParameters F parameters two_zero

theorem omegaElement_order
    (N : NormSource n F) (parameters : OddFieldParameters F p f)
    (rank : 3 ≤ n) (C : Source n F p f parameters rank N) (i : Fin n) :
    orderOf (omegaElement n F N parameters rank C i) = 2 := by
  letI primeTwoFact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (omegaElement_square n F N parameters rank C i)
    (omegaElement_ne_one n F N parameters rank C i)

/-- The exhibited involution proves divisibility of the actual group order. -/
theorem two_dvd_card
    (N : NormSource n F) (parameters : OddFieldParameters F p f)
    (rank : 3 ≤ n) (C : Source n F p f parameters rank N) :
    2 ∣ Nat.card (Omega n F) := by
  let i : Fin n := ⟨0, lt_of_lt_of_le (by decide : 0 < 3) rank⟩
  rw [← omegaElement_order n F N parameters rank C i]
  exact orderOf_dvd_natCard (omegaElement n F N parameters rank C i)

end ModularRep.PaperProofs.TypeBMatrixOmegaEvenOrder


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
