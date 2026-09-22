import ModularRep.PaperProofs.EvenFieldAlgebraicTorusPairInertiaBridge
import ModularRep.PaperProofs.IntermediateRestrictionIrreducible

/-!
# A certified ambient extension for the even-field argument

This module gives the source-shaped interface for the use of Späth's
extension theorem in manuscript Lemma 3.6.  The ambient representation is
required to restrict irreducibly to the literal base subgroup attached to
the selected Levi character, and that restriction has the selected
character.  Thus the representation used in Gallagher's formula cannot be
chosen independently of the generic-pair witness.

An ambient conjugation witness is kept separate.  It says that one element
of the ambient stabiliser induces the already constructed automorphism of
the actual inertia subgroup.  Character invariance is then proved from the
trace identity; it is not an input.
-/

namespace ModularRep.PaperProofs.EvenFieldAmbientExtension

open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPair
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPairInertiaBridge

universe u

variable {k N K : Type u} [Field k] [CharZero k] [Group N] [Group K]

/-- The canonical identification of the base subgroup viewed inside the
character inertia group with the original base subgroup. -/
def baseInInertiaEquiv (B : Subgroup N) [B.Normal]
    (lambda : Irr k B) : baseInInertia B lambda ≃* B where
  toFun x := ⟨((x : characterInertia B lambda) : N), x.property⟩
  invFun x :=
    ⟨⟨(x : N), (base_le_characterInertia B lambda) x.property⟩, x.property⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl
  map_mul' x y := by ext; rfl

/-- A representation supplied by the ambient extension theorem, certified
to extend the selected character of the literal base subgroup.

The map `inclusion` is the concrete inclusion of the character inertia group
in the ambient stabiliser.  Injectivity is part of the semantic certificate,
even though trace invariance itself only needs a homomorphism. -/
structure Data (B : Subgroup N) [B.Normal] (lambda : Irr k B)
    (K : Type u) [Group K] where
  dimension : ℕ
  rho : Representation k K (Fin dimension → k)
  inclusion : characterInertia B lambda →* K
  inclusion_injective : Function.Injective inclusion
  baseRestriction_irreducible : Representation.IsIrreducible
    (rho.pullback
      (inclusion.comp (baseInInertia B lambda).subtype))
  baseRestriction_character :
    (rho.pullback
      (inclusion.comp (baseInInertia B lambda).subtype)).character =
      fun x : baseInInertia B lambda =>
        lambda (baseInInertiaEquiv B lambda x)

variable {B : Subgroup N} [B.Normal] {lambda : Irr k B}

/-- The restriction of the certified ambient representation to the
character inertia group is irreducible. -/
theorem Data.inertiaRestriction_irreducible
    (D : Data B lambda K) :
    Representation.IsIrreducible (D.rho.pullback D.inclusion) := by
  apply Representation.isIrreducible_of_pullback
    (D.rho.pullback D.inclusion) (baseInInertia B lambda).subtype
  simpa only [Representation.pullback_comp] using
    D.baseRestriction_irreducible

/-- The irreducible extension character on the inertia subgroup constructed
from the certified ambient representation. -/
noncomputable def Data.extensionIrr (D : Data B lambda K) :
    Irr k (characterInertia B lambda) :=
  ⟨(D.rho.pullback D.inclusion).character, ⟨
    { dimension := D.dimension
      representation := D.rho.pullback D.inclusion
      irreducible := Data.inertiaRestriction_irreducible D
      character_eq := rfl }
  ⟩⟩

@[simp]
theorem Data.extensionIrr_apply (D : Data B lambda K)
    (x : characterInertia B lambda) :
    D.extensionIrr x = D.rho.character (D.inclusion x) :=
  rfl

/-- The constructed inertia character restricts to the selected Levi
character under the canonical identification of the base. -/
theorem Data.extensionIrr_restricts_to_lambda (D : Data B lambda K)
    (x : baseInInertia B lambda) :
    D.extensionIrr x = lambda (baseInInertiaEquiv B lambda x) := by
  exact congrFun D.baseRestriction_character x

/-- An element of the ambient stabiliser realising a prescribed
automorphism of the literal inertia group. -/
structure ConjugationWitness (D : Data B lambda K)
    (alpha : MulAut (characterInertia B lambda)) where
  element : K
  intertwines : ∀ x : characterInertia B lambda,
    D.inclusion (alpha x) = element * D.inclusion x * element⁻¹

/-- The certified extension character is fixed by every automorphism
realised by ambient conjugation. -/
theorem Data.extensionIrr_fixed (D : Data B lambda K)
    (alpha : MulAut (characterInertia B lambda))
    (W : ConjugationWitness D alpha) :
    twist k (characterInertia B lambda) D.extensionIrr alpha =
      D.extensionIrr := by
  apply OrdinaryIrreducibleCharacter.ext
  intro x
  rw [twist_apply, D.extensionIrr_apply, D.extensionIrr_apply,
    W.intertwines]
  simpa [mul_assoc] using
    D.rho.char_mul_comm (W.element⁻¹) (W.element * D.inclusion x)

end ModularRep.PaperProofs.EvenFieldAmbientExtension


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
