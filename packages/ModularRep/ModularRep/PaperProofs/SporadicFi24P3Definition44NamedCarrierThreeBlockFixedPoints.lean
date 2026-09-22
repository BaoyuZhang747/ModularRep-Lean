import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Equiv.Basic

/-! An injective map on three points fixing two distinct points fixes all points. -/

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierThreeBlockFixedPoints

theorem eq_self_of_two_fixed_three
    {B : Type*} (roles : Fin 3 ≃ B) (f : B → B)
    (hf : Function.Injective f) (x y : B) (hxy : x ≠ y)
    (hx : f x = x) (hy : f y = y) : ∀ z, f z = z := by
  classical
  intro z
  by_cases hzx : z = x
  · subst z
    exact hx
  by_cases hzy : z = y
  · subst z
    exact hy
  have hfx : f z ≠ x := fun h => hzx (hf (h.trans hx.symm))
  have hfy : f z ≠ y := fun h => hzy (hf (h.trans hy.symm))
  have hthree : ∀ a b c d : Fin 3,
      a ≠ b → c ≠ a → c ≠ b → d ≠ a → d ≠ b → c = d := by decide
  apply roles.symm.injective
  exact hthree (roles.symm x) (roles.symm y)
    (roles.symm (f z)) (roles.symm z)
    (fun h => hxy (roles.symm.injective h))
    (fun h => hfx (roles.symm.injective h))
    (fun h => hfy (roles.symm.injective h))
    (fun h => hzx (roles.symm.injective h))
    (fun h => hzy (roles.symm.injective h))

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierThreeBlockFixedPoints


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
