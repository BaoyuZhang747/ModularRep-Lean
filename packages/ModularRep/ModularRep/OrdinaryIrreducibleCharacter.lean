import ModularRep.Twist

/-!
# Function-valued ordinary irreducible characters

This file supplies a semantic carrier for `Irr(G)`.  An element is a function
realised as the trace character of an irreducible finite-dimensional
representation.  In particular, it is strictly smaller than the type of all
class functions.  Equality is equality of character functions, matching the
usual convention for `Irr(G)`.
-/

namespace ModularRep.OrdinaryIrreducibleCharacter

universe u

variable (k G : Type u) [Field k] [CharZero k] [Group G]

/-- A finite-dimensional irreducible representation realising a function as
its trace character. -/
structure Realisation (chi : G → k) where
  dimension : ℕ
  representation : Representation k G (Fin dimension → k)
  irreducible : Representation.IsIrreducible representation
  character_eq : representation.character = chi

/-- Function-valued ordinary irreducible characters. -/
def Irr := {chi : G → k // Nonempty (Realisation k G chi)}

instance : CoeFun (Irr k G) (fun _ ↦ G → k) :=
  ⟨fun chi ↦ chi.1⟩

@[ext]
theorem ext {chi psi : Irr k G} (h : ∀ g, chi g = psi g) : chi = psi := by
  apply Subtype.ext
  funext g
  exact h g

/-- Pull an irreducible character back along a group automorphism. -/
def twist (chi : Irr k G) (alpha : MulAut G) : Irr k G :=
  ⟨fun g ↦ chi (alpha g), by
    rcases chi.property with ⟨R⟩
    let R' : Realisation k G (fun g ↦ chi (alpha g)) :=
      { dimension := R.dimension
        representation := R.representation.twist alpha
        irreducible := R.irreducible.twist alpha
        character_eq := by
          funext g
          change R.representation.character (alpha g) = chi (alpha g)
          exact congrFun R.character_eq (alpha g) }
    exact ⟨R'⟩⟩

@[simp]
theorem twist_apply (chi : Irr k G) (alpha : MulAut G) (g : G) :
    twist k G chi alpha g = chi (alpha g) :=
  rfl

@[simp]
theorem twist_refl (chi : Irr k G) :
    twist k G chi (MulEquiv.refl G) = chi := by
  ext g
  rfl

/-- If the underlying group automorphism is the identity, its action on
`Irr(G)` is the identity. -/
theorem twist_eq_self_of_eq_refl (chi : Irr k G) (alpha : MulAut G)
    (h : alpha = MulEquiv.refl G) :
    twist k G chi alpha = chi := by
  subst alpha
  exact twist_refl k G chi

end ModularRep.OrdinaryIrreducibleCharacter


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
