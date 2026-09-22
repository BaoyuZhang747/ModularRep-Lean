import ModularRep.PrimeRegular
import ModularRep.Twist

/-!
# Restriction to prime regular elements

This file supplies the function level infrastructure needed before Brauer
characters can be defined.  It restricts functions and trace functions to
the prime regular elements and proves compatibility with homomorphisms and
automorphism twists.

The restricted trace of a representation in positive characteristic is not
defined here to be a Brauer character.
-/

namespace ModularRep

universe u v w

namespace PrimeRegularElement

variable {G : Type u} {H : Type v} {K : Type w} {p : ℕ}

/-- A monoid homomorphism maps prime regular elements to prime regular
elements. -/
def map [Monoid G] [Monoid H] (f : G →* H) :
    PrimeRegularElement (G := G) p → PrimeRegularElement (G := H) p :=
  fun g ↦ ⟨f g.1, g.2.map f⟩

@[simp]
theorem coe_map [Monoid G] [Monoid H] (f : G →* H)
    (g : PrimeRegularElement (G := G) p) :
    (map f g).1 = f g.1 :=
  rfl

@[simp]
theorem map_id [Monoid G] (g : PrimeRegularElement (G := G) p) :
    map (MonoidHom.id G) g = g :=
  rfl

@[simp]
theorem map_comp [Monoid G] [Monoid H] [Monoid K]
    (f : G →* H) (q : H →* K) (g : PrimeRegularElement (G := G) p) :
    map (q.comp f) g = map q (map f g) :=
  rfl

/-- A monoid equivalence restricts to an equivalence on the prime regular
elements. -/
def equiv [Monoid G] [Monoid H] (e : G ≃* H) :
    PrimeRegularElement (G := G) p ≃ PrimeRegularElement (G := H) p where
  toFun := map e.toMonoidHom
  invFun := map e.symm.toMonoidHom
  left_inv g := by
    apply Subtype.ext
    exact e.symm_apply_apply g.1
  right_inv h := by
    apply Subtype.ext
    exact e.apply_symm_apply h.1

@[simp]
theorem coe_equiv [Monoid G] [Monoid H] (e : G ≃* H)
    (g : PrimeRegularElement (G := G) p) :
    (equiv e g).1 = e g.1 :=
  rfl

end PrimeRegularElement

/-- An `R` valued function on the prime regular elements of `G`. -/
abbrev PrimeRegularFunction (R : Type w) (G : Type u) [Monoid G] (p : ℕ) :=
  PrimeRegularElement (G := G) p → R

/-- Restrict a function on a monoid to its prime regular elements. -/
def restrictToPrimeRegular {G : Type u} {R : Type w} [Monoid G] (p : ℕ)
    (f : G → R) : PrimeRegularFunction R G p :=
  fun g ↦ f g.1

@[simp]
theorem restrictToPrimeRegular_apply {G : Type u} {R : Type w} [Monoid G]
    (p : ℕ) (f : G → R) (g : PrimeRegularElement (G := G) p) :
    restrictToPrimeRegular p f g = f g.1 :=
  rfl

/-- Pull a function on prime regular elements back along a monoid
homomorphism. -/
def PrimeRegularFunction.pullback {G : Type u} {H : Type v} {R : Type w}
    [Monoid G] [Monoid H] {p : ℕ} (f : G →* H)
    (chi : PrimeRegularFunction R H p) : PrimeRegularFunction R G p :=
  fun g ↦ chi (PrimeRegularElement.map f g)

@[simp]
theorem PrimeRegularFunction.pullback_apply {G : Type u} {H : Type v}
    {R : Type w} [Monoid G] [Monoid H] {p : ℕ} (f : G →* H)
    (chi : PrimeRegularFunction R H p) (g : PrimeRegularElement (G := G) p) :
    chi.pullback f g = chi (PrimeRegularElement.map f g) :=
  rfl

end ModularRep

namespace Representation

variable {k : Type w} {G : Type u} {V : Type v}
variable [Field k] [Monoid G] [AddCommGroup V] [Module k V]

/-- The trace function of a representation, restricted to the prime regular
elements.  In positive characteristic this is not a definition of a Brauer
character. -/
noncomputable def regularTrace (rho : Representation k G V)
    [FiniteDimensional k V] (p : ℕ) :
    ModularRep.PrimeRegularFunction k G p :=
  ModularRep.restrictToPrimeRegular p rho.character

variable [FiniteDimensional k V]

@[simp]
theorem regularTrace_apply (rho : Representation k G V) (p : ℕ)
    (g : ModularRep.PrimeRegularElement (G := G) p) :
    rho.regularTrace p g = rho.character g.1 :=
  rfl

/-- Restriction of trace functions to prime regular elements commutes with
automorphism twists. -/
@[simp]
theorem regularTrace_twist (rho : Representation k G V) (p : ℕ)
    (alpha : MulAut G) :
    (rho.twist alpha).regularTrace p =
      (rho.regularTrace p).pullback alpha.toMonoidHom :=
  rfl

end Representation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
