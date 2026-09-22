import ManuscriptIBAW.Library.FixedBasis
import ModularRep.IntegralBasicSetBridge

/-!
# Integral basic sets fixed by automorphisms

If a decomposition map identifies two integral permutation modules and the
ordinary basis is fixed pointwise, the modular basis is fixed pointwise too.
The equality of their ranks then gives an equivariant bijection. This is the argument using a fixed basis in Proposition 3.8 of the companion manuscript.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ManuscriptIBAW

open ModularRep.IntegralBasicSetBridge

variable {A X Y : Type*} [Group A] [MulAction A X] [MulAction A Y]

/-- A natural integral basic set fixed pointwise gives a pointwise fixed
modular basis. -/
theorem modular_basis_fixed_of_basic_set_fixed
    (d : MonoidAlgebra ℤ X ≃ₗ[ℤ] MonoidAlgebra ℤ Y)
    (natural : MatrixEquivariant (A := A) d.toLinearMap)
    (fixed : ∀ (a : A) (x : X), a • x = x) :
    ∀ (a : A) (y : Y), a • y = y := by
  let b := (MonoidAlgebra.basis X ℤ).map d
  let c := MonoidAlgebra.basis Y ℤ
  apply action_trivial_of_fixed_basis (Representation.ofMulAction ℤ A Y) b c
  · intro a x
    change Representation.ofMulAction ℤ A Y a (d (MonoidAlgebra.single x 1)) =
      d (MonoidAlgebra.single x 1)
    calc
      _ = d (Representation.ofMulAction ℤ A X a (MonoidAlgebra.single x 1)) :=
        (map_action_of_matrixEquivariant d.toLinearMap natural a
          (MonoidAlgebra.single x 1)).symm
      _ = d (MonoidAlgebra.single x 1) := by
        rw [Representation.ofMulAction_single, fixed]
  · intro a y
    exact Representation.ofMulAction_single a y 1

/-- The two character sets have the same cardinality because their integral
permutation modules have bases indexed by these sets. With trivial actions,
any resulting bijection is equivariant. -/
theorem equivariant_bijection_of_basic_set_fixed
    (d : MonoidAlgebra ℤ X ≃ₗ[ℤ] MonoidAlgebra ℤ Y)
    (natural : MatrixEquivariant (A := A) d.toLinearMap)
    (fixed : ∀ (a : A) (x : X), a • x = x) :
    ∃ e : X ≃ Y, ∀ (a : A) (x : X), e (a • x) = a • e x := by
  let b := (MonoidAlgebra.basis X ℤ).map d
  let c := MonoidAlgebra.basis Y ℤ
  refine ⟨b.indexEquiv c, ?_⟩
  intro a x
  rw [fixed, modular_basis_fixed_of_basic_set_fixed d natural fixed]

end ManuscriptIBAW

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
