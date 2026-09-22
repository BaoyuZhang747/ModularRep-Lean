import ModularRep.PaperProofs.EvenFieldFixedPointMulAut

/-!
# The Lang witness and the finite inner twist

This module isolates manuscript lines 340--356.  From the Lang equation and
fixation of the chosen Weyl representative, Lean proves that
`g * sigma(g)⁻¹` lies in the finite fixed-point group.  The field
automorphism and the inner-twisted automorphism of that finite group are then
definitions, so their factorisation is not an external hypothesis.
-/

namespace ModularRep.PaperProofs.EvenFieldLangInnerTwist

open ModularRep.PaperProofs.EvenFieldFixedPointMulAut
open ModularRep.PaperProofs.EvenFieldSourceShaped

universe u

variable {G : Type u} [Group G]

/-- The E7 Lang witness together with the field-fixation property of its
chosen representative.  The rational-Levi parametrisation that relates this
representative to a standard Levi is supplied separately. -/
structure Data (F : G →* G) (sigma : MulAut G)
    (commute : ∀ x : G, F (sigma x) = sigma (F x)) (g : G) where
  representative : G
  langEquation : g⁻¹ * F g = representative
  representative_fixed : sigma representative = representative

/-- The element `g sigma(g)⁻¹`, proved to lie in `G^F`. -/
def Data.innerElement
    {F : G →* G} {sigma : MulAut G}
    {commute : ∀ x : G, F (sigma x) = sigma (F x)} {g : G}
    (D : Data F sigma commute g) : frobeniusFixedSubgroup F :=
  ⟨innerTwistElement sigma.toMonoidHom g,
    innerTwistElement_mem_frobeniusFixedSubgroup F sigma.toMonoidHom g
      D.representative commute D.langEquation D.representative_fixed⟩

@[simp]
theorem Data.innerElement_coe
    {F : G →* G} {sigma : MulAut G}
    {commute : ∀ x : G, F (sigma x) = sigma (F x)} {g : G}
    (D : Data F sigma commute g) :
    (D.innerElement : G) = g * (sigma g)⁻¹ :=
  rfl

/-- The standard field automorphism induced on the fixed-point group. -/
def Data.fieldAut
    {F : G →* G} {sigma : MulAut G}
    {commute : ∀ x : G, F (sigma x) = sigma (F x)} {g : G}
    (_D : Data F sigma commute g) : MulAut (frobeniusFixedSubgroup F) :=
  fixedPointMulAut F sigma commute

/-- The inner-twisted automorphism on the finite fixed-point group. -/
def Data.tau
    {F : G →* G} {sigma : MulAut G}
    {commute : ∀ x : G, F (sigma x) = sigma (F x)} {g : G}
    (D : Data F sigma commute g) : MulAut (frobeniusFixedSubgroup F) :=
  MulAut.conj D.innerElement * D.fieldAut

/-- The factorisation used in orbit descent is definitional once the Lang
witness has been supplied. -/
theorem Data.tau_factorisation
    {F : G →* G} {sigma : MulAut G}
    {commute : ∀ x : G, F (sigma x) = sigma (F x)} {g : G}
    (D : Data F sigma commute g) :
    D.tau = MulAut.conj D.innerElement * D.fieldAut :=
  rfl

end ModularRep.PaperProofs.EvenFieldLangInnerTwist


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
