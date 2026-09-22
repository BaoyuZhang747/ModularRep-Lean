import ModularRep.PaperProofs.TypeBComponentCycleNormalization
import ModularRep.PaperProofs.TypeBRegularLeviRationalCarriers

/-!
# Actual fixed points of a cycle of geometric components

This finite group-coordinate deduction constructs the fixed-point product
in current Lemma 4.5. The geometric factors, their original monomial maps,
and the actual point automorphism are prescribed. Successor normalization
and the full-return identity are the checked Lemma 4.4 group constructions.

The input convention sends coordinate j+1 to coordinate j. The inverse
fixed-product equivalence therefore uses `toBase.symm` at each position.
This explicit Frobenius-diagonal formula, with its chosen cycle orientation,
must be retained in the algebraic application; a bare one-factor inclusion
is not the fixed-point isomorphism. No character theorem is used here.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBRegularLeviComponentFixedPoints

open TypeBComponentCycleNormalization TypeBRegularLeviRationalCarriers

variable {C : Type} (m : C → ℕ) (H : Index m → Type)
variable [∀ i, Group (H i)] (S : CycleCoordinates m H)
variable (a : MulAut (Original m H)) (ha : MonomialAction m H S a)

/-- The computed coordinate equivalence restricts to actual fixed points. -/
def normalizedFixedEquiv :
    fixedPoints a.toMonoidHom ≃*
      fixedPoints (normalizedAut m H S a).toMonoidHom where
  toFun x := ⟨productEquiv m H S x.1, by
    change productEquiv m H S
      (a ((productEquiv m H S).symm (productEquiv m H S x.1))) =
        productEquiv m H S x.1
    rw [MulEquiv.symm_apply_apply]
    exact congrArg (productEquiv m H S) x.2⟩
  invFun x := ⟨(productEquiv m H S).symm x.1, by
    apply (productEquiv m H S).injective
    change normalizedAut m H S a x.1 = productEquiv m H S ((productEquiv m H S).symm x.1)
    rw [MulEquiv.apply_symm_apply]
    exact x.2⟩
  left_inv x := Subtype.ext ((productEquiv m H S).symm_apply_apply x.1)
  right_inv x := Subtype.ext ((productEquiv m H S).apply_symm_apply x.1)
  map_mul' x y := Subtype.ext ((productEquiv m H S).map_mul x.1 y.1)

include ha in
/-- A normalized fixed tuple is constant along each cycle. -/
theorem fixed_coordinate (x : fixedPoints (normalizedAut m H S a).toMonoidHom)
    (c : C) (j : Fin (m c + 1)) : x.1 ⟨c, j⟩ = x.1 (first m c) := by
  refine Fin.induction ?_ ?_ j
  · rfl
  · intro j ih
    have hsucc := normalized_successor m H S ha x.1 c j
    have hfixed : normalizedAut m H S a x.1 ⟨c, j.castSucc⟩ = x.1 ⟨c, j.castSucc⟩ :=
      congrFun x.2 ⟨c, j.castSucc⟩
    exact (hsucc.symm.trans hfixed).trans ih

include ha in
/-- The first coordinate is fixed by the literal full return. -/
theorem first_fixed (x : fixedPoints (normalizedAut m H S a).toMonoidHom) (c : C) :
    fullReturn m H S c (x.1 (first m c)) = x.1 (first m c) := by
  have hwrap := normalized_wrap m H S ha x.1 c
  have hfixed : normalizedAut m H S a x.1 (last m c) = x.1 (last m c) :=
    congrFun x.2 (last m c)
  exact (hwrap.symm.trans hfixed).trans (fixed_coordinate m H S a ha x c (Fin.last (m c)))

/-- Evaluate a normalized fixed tuple at its original first factors. The
inverse is the constant tuple, made fixed by the actual return condition. -/
def evaluateFixedEquiv :
    fixedPoints (normalizedAut m H S a).toMonoidHom ≃*
      ((c : C) → fixedPoints (fullReturn m H S c).toMonoidHom) where
  toFun x c := ⟨x.1 (first m c), first_fixed m H S a ha x c⟩
  invFun theta := ⟨fun (i : Index m) ↦ (theta i.1).1, by
    change normalizedAut m H S a (fun (i : Index m) ↦ (theta i.1).1) =
      (fun (i : Index m) ↦ (theta i.1).1)
    funext i
    rcases i with ⟨c, j⟩
    refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · exact (normalized_wrap m H S ha (fun (i : Index m) ↦ (theta i.1).1) c).trans (theta c).2
    · exact normalized_successor m H S ha (fun (i : Index m) ↦ (theta i.1).1) c j⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    exact (fixed_coordinate m H S a ha x i.1 i.2).symm
  right_inv theta := by
    funext c
    rfl
  map_mul' x y := by
    funext c
    rfl

/-- The actual original fixed-point group is the product of actual
full-return fixed-point groups on its original first factors. -/
def fixedProductEquiv :
    fixedPoints a.toMonoidHom ≃*
      ((c : C) → fixedPoints (fullReturn m H S c).toMonoidHom) :=
  (normalizedFixedEquiv m H S a).trans (evaluateFixedEquiv m H S a ha)

@[simp]
theorem fixedProductEquiv_value (x : fixedPoints a.toMonoidHom) (c : C) :
    (fixedProductEquiv m H S a ha x c).1 = x.1 (first m c) := rfl

/-- The literal Frobenius-diagonal inverse, in the supplied cycle order. -/
@[simp]
theorem fixedProductEquiv_symm_value
    (theta : (c : C) → fixedPoints (fullReturn m H S c).toMonoidHom) (i : Index m) :
    ((fixedProductEquiv m H S a ha).symm theta).1 i =
      (toBase m H S i.1 i.2).symm (theta i.1).1 := rfl

include ha in
/-- The return used in the factor carrier is the actual full power of the
same geometric point automorphism, not a separately supplied map. -/
theorem factorReturn_power_value (c : C) (g : Original m H) :
    fullReturn m H S c (g (first m c)) = (a ^ (m c + 1)) g (first m c) :=
  fullReturn_eq_power m H S ha c g

end ModularRep.PaperProofs.TypeBRegularLeviComponentFixedPoints


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
