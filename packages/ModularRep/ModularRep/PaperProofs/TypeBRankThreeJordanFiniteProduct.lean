import ModularRep.PaperProofs.TypeBRankThreeJordanCliffordCarriers
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

namespace ModularRep.PaperProofs.TypeBRankThreeJordanFiniteProduct

open TypeBCliffordCarriers TypeBRegularLeviRationalCarriers
open TypeBRankThreeJordanCliffordCarriers TypeBRankThreeJordanDiagonalProduct

variable {p f : ℕ} {F A : Type}
variable [Field F] [Finite F] [CharP F p] [Field A] [Algebra F A]
variable {N : NormSource 3 F} {Nbar : NormSource 3 A}
variable {Frob : MulAut (SpecialClifford 3 A)}
variable (points : CliffordFixedPointSource 3 p f F A N Nbar Frob)

/-- Spin descent has the same underlying fixed point as ambient descent. -/
@[simp] theorem finiteSpinEquiv_point (g : Spin 3 F N) :
    (finiteSpinEquiv 3 p f F A N Nbar Frob points g).val =
      ambientEquiv points g.val := rfl

/-- The inverse Spin descent retains the original ambient fixed point. -/
@[simp] theorem finiteSpinEquiv_symm_point
    (g : rationalSubgroup Frob.toMonoidHom (SpinSubgroup 3 A Nbar)) :
    ambientEquiv points
        ((finiteSpinEquiv 3 p f F A N Nbar Frob points).symm g).val = g.val :=
  congrArg Subtype.val
    ((finiteSpinEquiv 3 p f F A N Nbar Frob points).apply_symm_apply g)

/-- Inverse Spin descent also preserves the specified geometric inclusion. -/
@[simp] theorem finiteSpinEquiv_symm_inclusion
    (g : rationalSubgroup Frob.toMonoidHom (SpinSubgroup 3 A Nbar)) :
    points.inclusion
        ((finiteSpinEquiv 3 p f F A N Nbar Frob points).symm g).val = g.val.val :=
  congrArg Subtype.val (finiteSpinEquiv_symm_point points g)

variable (Lbar : Subgroup (SpecialClifford 3 A))
variable (levi_le_spin : Lbar ≤ SpinSubgroup 3 A Nbar)
variable (decomposition : ∀ x : SpecialClifford 3 A,
  ∃ g ∈ SpinSubgroup 3 A Nbar,
    ∃ z ∈ Subgroup.center (SpecialClifford 3 A), x = g * z)
variable (intersection : pairedLevi Lbar ⊓ SpinSubgroup 3 A Nbar ≤ Lbar)
variable (lang : LeviLangSource Frob Lbar)

include levi_le_spin decomposition intersection lang in
/-- The geometric deduction transported onto the SAME finite Clifford and
Spin carriers, with the existing rational paired-Levi inclusion. -/
theorem finite_product (a : SpecialClifford 3 F) :
    ∃ g : Spin 3 F N, ∃ m : M Frob.toMonoidHom Lbar,
      a = (g : SpecialClifford 3 F) * gammaEmbedding points Lbar m := by
  obtain ⟨gFixed, m, h⟩ :=
    rational_product Frob (SpinSubgroup 3 A Nbar) Lbar
      (geometricSpin_frobenius_stable 3 p f F A N Nbar Frob points)
      levi_le_spin decomposition intersection lang (ambientEquiv points a)
  refine ⟨(finiteSpinEquiv 3 p f F A N Nbar Frob points).symm gFixed, m, ?_⟩
  apply (ambientEquiv points).injective
  rw [(ambientEquiv points).map_mul, finiteSpinEquiv_symm_point,
    gammaEmbedding_point]
  exact h

include levi_le_spin decomposition intersection lang in
/-- The same chosen finite factors satisfy the original fixed-point and
geometric inclusion equations. -/
theorem finite_product_values (a : SpecialClifford 3 F) :
    ∃ g : Spin 3 F N, ∃ m : M Frob.toMonoidHom Lbar,
      a = (g : SpecialClifford 3 F) * gammaEmbedding points Lbar m ∧
      ambientEquiv points a =
        (finiteSpinEquiv 3 p f F A N Nbar Frob points g).val * m.val ∧
      points.inclusion a = points.inclusion (g : SpecialClifford 3 F) * m.val.val := by
  obtain ⟨g, m, h⟩ :=
    finite_product points Lbar levi_le_spin decomposition intersection lang a
  refine ⟨g, m, h, ?_, ?_⟩
  · rw [h, (ambientEquiv points).map_mul, gammaEmbedding_point,
      finiteSpinEquiv_point]
  · rw [h, points.inclusion.map_mul, gammaEmbedding_inclusion]

end ModularRep.PaperProofs.TypeBRankThreeJordanFiniteProduct


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
