import ModularRep.RegularRestriction

/-!
# Class functions on prime regular elements

Brauer characters are class functions on the prime regular elements, but not
every class function on that domain is a Brauer character.  This file defines
only the ambient function space and its automorphism action.
-/

namespace ModularRep

universe u v

/-- An `R` valued function on the prime regular elements which is invariant
under conjugation by the ambient group. -/
structure PrimeRegularClassFunction (R : Type v) (G : Type u) [Group G]
    (p : ℕ) where
  /-- The underlying function on prime regular elements. -/
  toFun : PrimeRegularFunction R G p
  /-- Invariance under conjugation in `G`. -/
  map_conj : ∀ (x : G) (g : PrimeRegularElement (G := G) p),
    toFun ⟨x * g.1 * x⁻¹, g.2.conj x⟩ = toFun g

namespace PrimeRegularClassFunction

variable {R : Type v} {G : Type u} [Group G] {p : ℕ}

instance : CoeFun (PrimeRegularClassFunction R G p)
    (fun _ ↦ PrimeRegularElement (G := G) p → R) :=
  ⟨PrimeRegularClassFunction.toFun⟩

@[ext]
theorem ext {f q : PrimeRegularClassFunction R G p}
    (h : ∀ g, f g = q g) : f = q := by
  cases f with
  | mk f hf =>
      cases q with
      | mk q hq =>
          congr
          funext g
          exact h g

instance [Zero R] : Zero (PrimeRegularClassFunction R G p) where
  zero :=
    { toFun := 0
      map_conj := fun _ _ ↦ rfl }

@[simp]
theorem zero_apply [Zero R] (g : PrimeRegularElement (G := G) p) :
    (0 : PrimeRegularClassFunction R G p) g = 0 :=
  rfl

instance [Add R] : Add (PrimeRegularClassFunction R G p) where
  add f q :=
    { toFun := f.toFun + q.toFun
      map_conj := fun x g ↦
        congrArg₂ (· + ·) (f.map_conj x g) (q.map_conj x g) }

@[simp]
theorem add_apply [Add R] (f q : PrimeRegularClassFunction R G p)
    (g : PrimeRegularElement (G := G) p) :
    (f + q) g = f g + q g :=
  rfl

instance [AddMonoid R] : SMul ℕ (PrimeRegularClassFunction R G p) where
  smul n f :=
    { toFun := n • f.toFun
      map_conj := fun x g ↦ congrArg (n • ·) (f.map_conj x g) }

@[simp]
theorem nsmul_apply [AddMonoid R] (n : ℕ)
    (f : PrimeRegularClassFunction R G p)
    (g : PrimeRegularElement (G := G) p) :
    (n • f) g = n • f g :=
  rfl

instance [Neg R] : Neg (PrimeRegularClassFunction R G p) where
  neg f :=
    { toFun := -f.toFun
      map_conj := fun x g ↦ congrArg Neg.neg (f.map_conj x g) }

@[simp]
theorem neg_apply [Neg R] (f : PrimeRegularClassFunction R G p)
    (g : PrimeRegularElement (G := G) p) :
    (-f) g = -f g :=
  rfl

instance [Sub R] : Sub (PrimeRegularClassFunction R G p) where
  sub f q :=
    { toFun := f.toFun - q.toFun
      map_conj := fun x g ↦
        congrArg₂ (· - ·) (f.map_conj x g) (q.map_conj x g) }

@[simp]
theorem sub_apply [Sub R] (f q : PrimeRegularClassFunction R G p)
    (g : PrimeRegularElement (G := G) p) :
    (f - q) g = f g - q g :=
  rfl

instance [AddGroup R] : SMul ℤ (PrimeRegularClassFunction R G p) where
  smul n f :=
    { toFun := n • f.toFun
      map_conj := fun x g ↦ congrArg (n • ·) (f.map_conj x g) }

@[simp]
theorem zsmul_apply [AddGroup R] (n : ℤ)
    (f : PrimeRegularClassFunction R G p)
    (g : PrimeRegularElement (G := G) p) :
    (n • f) g = n • f g :=
  rfl

instance [AddCommGroup R] : AddCommGroup (PrimeRegularClassFunction R G p) :=
  Function.Injective.addCommGroup PrimeRegularClassFunction.toFun
    (fun _ _ h ↦ ext (congrFun h)) rfl (fun _ _ ↦ rfl)
      (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

/-- Restrict a conjugation invariant function on `G` to its prime regular
elements. -/
def ofFunction (f : G → R)
    (hf : ∀ x g : G, f (x * g * x⁻¹) = f g) :
    PrimeRegularClassFunction R G p where
  toFun := restrictToPrimeRegular p f
  map_conj x g := hf x g.1

@[simp]
theorem ofFunction_apply (f : G → R)
    (hf : ∀ x g : G, f (x * g * x⁻¹) = f g)
    (g : PrimeRegularElement (G := G) p) :
    ofFunction f hf g = f g.1 :=
  rfl

/-- Pull a prime regular class function back along an automorphism of the
ambient group. -/
def twist (f : PrimeRegularClassFunction R G p) (alpha : MulAut G) :
    PrimeRegularClassFunction R G p where
  toFun := f.toFun.pullback alpha.toMonoidHom
  map_conj x g := by
    have h := f.map_conj (alpha x) (PrimeRegularElement.map alpha.toMonoidHom g)
    change f (PrimeRegularElement.map alpha.toMonoidHom
      ⟨x * g.1 * x⁻¹, g.2.conj x⟩) =
        f (PrimeRegularElement.map alpha.toMonoidHom g)
    have hmap :
        PrimeRegularElement.map alpha.toMonoidHom
            ⟨x * g.1 * x⁻¹, g.2.conj x⟩ =
          ⟨alpha x * (PrimeRegularElement.map alpha.toMonoidHom g).1 * (alpha x)⁻¹,
            (PrimeRegularElement.map alpha.toMonoidHom g).2.conj (alpha x)⟩ := by
      apply Subtype.ext
      change alpha (x * g.1 * x⁻¹) = alpha x * alpha g.1 * (alpha x)⁻¹
      simp
    rw [hmap]
    exact h

@[simp]
theorem twist_apply (f : PrimeRegularClassFunction R G p) (alpha : MulAut G)
    (g : PrimeRegularElement (G := G) p) :
    f.twist alpha g = f (PrimeRegularElement.map alpha.toMonoidHom g) :=
  rfl

@[simp]
theorem twist_refl (f : PrimeRegularClassFunction R G p) :
    f.twist (MulEquiv.refl G) = f := by
  ext g
  rfl

/-- Inner automorphisms fix every prime regular class function. -/
@[simp]
theorem twist_conj (f : PrimeRegularClassFunction R G p) (x : G) :
    f.twist (MulAut.conj x) = f := by
  ext g
  change f ⟨x * g.1 * x⁻¹, g.2.conj x⟩ = f g
  exact f.map_conj x g

@[simp]
theorem twist_mul (f : PrimeRegularClassFunction R G p)
    (alpha beta : MulAut G) :
    (f.twist alpha).twist beta = f.twist (alpha * beta) := by
  ext g
  rfl

end PrimeRegularClassFunction

end ModularRep

namespace Representation

universe u v w

variable {k : Type w} {G : Type u} {V : Type v}
variable [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- The trace function of a representation, restricted to the prime regular
elements and packaged with its conjugation invariance.  In positive
characteristic this is not a Brauer character. -/
noncomputable def regularTraceClassFunction (rho : Representation k G V)
    [FiniteDimensional k V] (p : ℕ) :
    ModularRep.PrimeRegularClassFunction k G p :=
  ModularRep.PrimeRegularClassFunction.ofFunction rho.character
    (fun x g ↦ rho.char_conj g x)

variable [FiniteDimensional k V]

@[simp]
theorem regularTraceClassFunction_apply (rho : Representation k G V)
    (p : ℕ) (g : ModularRep.PrimeRegularElement (G := G) p) :
    rho.regularTraceClassFunction p g = rho.character g.1 :=
  rfl

/-- The prime regular trace class function respects automorphism twists. -/
@[simp]
theorem regularTraceClassFunction_twist (rho : Representation k G V)
    (p : ℕ) (alpha : MulAut G) :
    (rho.twist alpha).regularTraceClassFunction p =
      (rho.regularTraceClassFunction p).twist alpha := by
  ext g
  rfl

end Representation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
