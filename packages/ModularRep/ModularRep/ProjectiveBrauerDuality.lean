import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Projective and Brauer duality under automorphisms

This file formalises the finite deduction used in manuscript Corollary 4.10.
If an automorphism group fixes the projective indecomposable characters and
the usual duality between projective indecomposable characters and
irreducible Brauer characters is equivariant, then it fixes every irreducible
Brauer character.

The relation `Paired` is a source shaped interface for that duality.  The
file does not construct projective indecomposable characters, Brauer
characters, their scalar product, or the relevant field automorphism action.
-/

namespace ModularRep.ManuscriptVerification.ProjectiveBrauerDuality

variable {E Projective Brauer : Type*}
variable [Group E] [MulAction E Projective] [MulAction E Brauer]

/-- The exact set level content of the duality used in Corollary 4.10.

Every Brauer label has a paired projective label, a projective label is
paired with at most one Brauer label, and the pairing is preserved by the
automorphism action.  In the manuscript application, `Paired P phi` means
that the scalar product of the projective indecomposable character `P` with
the irreducible Brauer character `phi` is one.
-/
structure EquivariantDualIndexing where
  Paired : Projective -> Brauer -> Prop
  exists_projective : forall phi : Brauer, exists P : Projective, Paired P phi
  unique_brauer : forall {P : Projective} {phi psi : Brauer},
    Paired P phi -> Paired P psi -> phi = psi
  equivariant : forall (e : E) (P : Projective) (phi : Brauer),
    Paired P phi -> Paired (e • P) (e • phi)

/-- Pointwise fixation of the projective labels transfers across an
equivariant dual indexing to pointwise fixation of the Brauer labels. -/
theorem brauer_fixed_of_projective_fixed
    (D : EquivariantDualIndexing (E := E)
      (Projective := Projective) (Brauer := Brauer))
    (hProjective : forall (e : E) (P : Projective), e • P = P) :
    forall (e : E) (phi : Brauer), e • phi = phi := by
  intro e phi
  obtain ⟨P, hPphi⟩ := D.exists_projective phi
  apply D.unique_brauer
  · simpa [hProjective e P] using D.equivariant e P phi hPphi
  · exact hPphi

section FixedAmbientSpace

variable {V : Type*} [MulAction E V]

/-- If projective labels embed equivariantly into a pointwise-fixed ambient
space, then the projective labels themselves are pointwise fixed. -/
theorem projective_fixed_of_fixed_ambient
    (character : Projective -> V)
    (character_injective : Function.Injective character)
    (character_equivariant : forall (e : E) (P : Projective),
      character (e • P) = e • character P)
    (ambient_fixed : forall (e : E) (v : V), e • v = v) :
    forall (e : E) (P : Projective), e • P = P := by
  intro e P
  apply character_injective
  rw [character_equivariant, ambient_fixed]

/-- Combined form matching Corollary 4.10: triviality of the action on the
projective character space fixes the projective basis, and equivariant
projective--Brauer duality then fixes all irreducible Brauer characters. -/
theorem brauer_fixed_of_fixed_projective_space
    (D : EquivariantDualIndexing (E := E)
      (Projective := Projective) (Brauer := Brauer))
    (character : Projective -> V)
    (character_injective : Function.Injective character)
    (character_equivariant : forall (e : E) (P : Projective),
      character (e • P) = e • character P)
    (ambient_fixed : forall (e : E) (v : V), e • v = v) :
    forall (e : E) (phi : Brauer), e • phi = phi :=
  brauer_fixed_of_projective_fixed D
    (projective_fixed_of_fixed_ambient character character_injective
      character_equivariant ambient_fixed)

end FixedAmbientSpace

end ModularRep.ManuscriptVerification.ProjectiveBrauerDuality


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
