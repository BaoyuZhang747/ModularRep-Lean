import ModularRep.PaperProofs.EvenFieldSourceShaped

/-!
# Automorphisms of a Frobenius fixed-point group

An algebraic-group automorphism commuting with the defining Frobenius
endomorphism restricts to an automorphism of the finite fixed-point group.
This is the typed bridge used to construct the manuscript's field
automorphism and its inner twist from the Lang witness.
-/

namespace ModularRep.PaperProofs.EvenFieldFixedPointMulAut

open ModularRep.PaperProofs.EvenFieldSourceShaped

universe u

variable {G : Type u} [Group G]

/-- Commutation with `F` also gives commutation of the inverse automorphism
with `F`. -/
theorem commute_symm (F : G →* G) (sigma : MulAut G)
    (commute : ∀ x : G, F (sigma x) = sigma (F x)) (x : G) :
    F (sigma.symm x) = sigma.symm (F x) := by
  apply sigma.injective
  have h := commute (sigma.symm x)
  simpa using h.symm

/-- Restriction of a commuting algebraic automorphism to the finite
fixed-point subgroup. -/
def fixedPointMulAut (F : G →* G) (sigma : MulAut G)
    (commute : ∀ x : G, F (sigma x) = sigma (F x)) :
    MulAut (frobeniusFixedSubgroup F) where
  toFun := frobeniusFixedSubgroupHom F sigma.toMonoidHom commute
  invFun := frobeniusFixedSubgroupHom F sigma.symm.toMonoidHom
    (commute_symm F sigma commute)
  left_inv x := by
    apply Subtype.ext
    exact sigma.symm_apply_apply x
  right_inv x := by
    apply Subtype.ext
    exact sigma.apply_symm_apply x
  map_mul' x y := by ext; simp

@[simp]
theorem fixedPointMulAut_coe (F : G →* G) (sigma : MulAut G)
    (commute : ∀ x : G, F (sigma x) = sigma (F x))
    (x : frobeniusFixedSubgroup F) :
    (fixedPointMulAut F sigma commute x : G) = sigma x :=
  rfl

end ModularRep.PaperProofs.EvenFieldFixedPointMulAut


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
