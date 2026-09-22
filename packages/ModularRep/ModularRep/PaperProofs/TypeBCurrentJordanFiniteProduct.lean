import ModularRep.PaperProofs.TypeBCurrentJordanCliffordCarriers
import ModularRep.PaperProofs.TypeBRankThreeJordanDiagonalProduct

/-!
# The diagonal product on the original finite Clifford carrier

The geometric product and one-variable Levi Lang solution give a product
of fixed points. The same Clifford fixed-point source then transports it
to the original finite Clifford group and its literal Spin norm kernel.
The point and inclusion equations retain the original elements.

The geometric central decomposition and Levi intersection are structural
inputs on these exact subgroups. Lang applicability on the same connected
Levi remains in the given LeviLangSource. No rational product, quotient
surjectivity, character correspondence or stabilizer conclusion is input.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBCurrentJordanFiniteProduct

open TypeBCliffordCarriers TypeBRegularLeviRationalCarriers
open TypeBCurrentJordanCliffordCarriers TypeBRankThreeJordanDiagonalProduct

variable {n p f : ℕ} {F A : Type}
variable [Field F] [Finite F] [CharP F p] [Field A] [Algebra F A]
variable {N : NormSource n F} {Nbar : NormSource n A}
variable {Frob : MulAut (SpecialClifford n A)}
variable (points : CliffordFixedPointSource n p f F A N Nbar Frob)

/-- Spin descent has the same underlying fixed point as ambient descent. -/
@[simp] theorem finiteSpinEquiv_point (g : Spin n F N) :
    (finiteSpinEquiv n p f F A N Nbar Frob points g).val =
      ambientEquiv points g.val := rfl

/-- The inverse Spin descent retains the original ambient fixed point. -/
@[simp] theorem finiteSpinEquiv_symm_point
    (g : rationalSubgroup Frob.toMonoidHom (SpinSubgroup n A Nbar)) :
    ambientEquiv points
        ((finiteSpinEquiv n p f F A N Nbar Frob points).symm g).val = g.val :=
  congrArg Subtype.val
    ((finiteSpinEquiv n p f F A N Nbar Frob points).apply_symm_apply g)

/-- Inverse Spin descent also preserves the specified geometric inclusion. -/
@[simp] theorem finiteSpinEquiv_symm_inclusion
    (g : rationalSubgroup Frob.toMonoidHom (SpinSubgroup n A Nbar)) :
    points.inclusion
        ((finiteSpinEquiv n p f F A N Nbar Frob points).symm g).val = g.val.val :=
  congrArg Subtype.val (finiteSpinEquiv_symm_point points g)

variable (Lbar : Subgroup (SpecialClifford n A))
variable (levi_le_spin : Lbar ≤ SpinSubgroup n A Nbar)
variable (decomposition : ∀ x : SpecialClifford n A,
  ∃ g ∈ SpinSubgroup n A Nbar,
    ∃ z ∈ Subgroup.center (SpecialClifford n A), x = g * z)
variable (intersection : pairedLevi Lbar ⊓ SpinSubgroup n A Nbar ≤ Lbar)
variable (lang : LeviLangSource Frob Lbar)

include levi_le_spin decomposition intersection lang in
/-- The geometric deduction transported onto the SAME finite Clifford and
Spin carriers, with the existing rational paired-Levi inclusion. -/
theorem finite_product (a : SpecialClifford n F) :
    ∃ g : Spin n F N, ∃ m : M Frob.toMonoidHom Lbar,
      a = (g : SpecialClifford n F) * gammaEmbedding points Lbar m := by
  obtain ⟨gFixed, m, h⟩ :=
    rational_product Frob (SpinSubgroup n A Nbar) Lbar
      (geometricSpin_frobenius_stable n p f F A N Nbar Frob points)
      levi_le_spin decomposition intersection lang (ambientEquiv points a)
  refine ⟨(finiteSpinEquiv n p f F A N Nbar Frob points).symm gFixed, m, ?_⟩
  apply (ambientEquiv points).injective
  rw [(ambientEquiv points).map_mul, finiteSpinEquiv_symm_point,
    gammaEmbedding_point]
  exact h

include levi_le_spin decomposition intersection lang in
/-- The same chosen finite factors satisfy the original fixed-point and
geometric inclusion equations. -/
theorem finite_product_values (a : SpecialClifford n F) :
    ∃ g : Spin n F N, ∃ m : M Frob.toMonoidHom Lbar,
      a = (g : SpecialClifford n F) * gammaEmbedding points Lbar m ∧
      ambientEquiv points a =
        (finiteSpinEquiv n p f F A N Nbar Frob points g).val * m.val ∧
      points.inclusion a = points.inclusion (g : SpecialClifford n F) * m.val.val := by
  obtain ⟨g, m, h⟩ :=
    finite_product points Lbar levi_le_spin decomposition intersection lang a
  refine ⟨g, m, h, ?_, ?_⟩
  · rw [h, (ambientEquiv points).map_mul, gammaEmbedding_point,
      finiteSpinEquiv_point]
  · rw [h, points.inclusion.map_mul, gammaEmbedding_inclusion]

end ModularRep.PaperProofs.TypeBCurrentJordanFiniteProduct


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
