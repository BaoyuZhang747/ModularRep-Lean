import Mathlib.RepresentationTheory.Character

/-!
# Pullbacks and automorphism twists of representations

This file defines pullback of a representation along a monoid homomorphism and
twisting along a monoid automorphism.  A surjective pullback preserves and
reflects irreducibility, so an automorphism twist does as well.

The final results concern the trace function of a representation.
In positive characteristic this trace function is not a Brauer character.
-/

namespace Representation

section Pullback

variable {A G H K V : Type*} [Semiring A] [Monoid G] [Monoid H] [Monoid K]
  [AddCommMonoid V] [Module A V]

/-- Pull a representation of `G` back along a monoid homomorphism `H →* G`. -/
def pullback (rho : Representation A G V) (f : H →* G) : Representation A H V :=
  rho.comp f

@[simp]
theorem pullback_apply (rho : Representation A G V) (f : H →* G) (h : H) :
    rho.pullback f h = rho (f h) :=
  rfl

@[simp]
theorem pullback_id (rho : Representation A G V) :
    rho.pullback (MonoidHom.id G) = rho :=
  rfl

@[simp]
theorem pullback_comp (rho : Representation A G V) (f : H →* G) (q : K →* H) :
    (rho.pullback f).pullback q = rho.pullback (f.comp q) :=
  rfl

/-- Pulling back subrepresentations along a surjective homomorphism induces an
order isomorphism on invariant submodules. -/
def subrepresentationPullbackOrderIso (rho : Representation A G V) (f : H →* G)
    (hf : Function.Surjective f) :
    Subrepresentation (rho.pullback f) ≃o Subrepresentation rho where
  toFun W :=
    { toSubmodule := W.toSubmodule
      apply_mem_toSubmodule := by
        intro g v hv
        obtain ⟨h, rfl⟩ := hf g
        exact W.apply_mem_toSubmodule h hv }
  invFun W :=
    { toSubmodule := W.toSubmodule
      apply_mem_toSubmodule := fun h _ hv ↦ W.apply_mem_toSubmodule (f h) hv }
  left_inv W := by
    apply Subrepresentation.ext
    rfl
  right_inv W := by
    apply Subrepresentation.ext
    rfl
  map_rel_iff' := by
    rfl

end Pullback

section Equiv

variable {A G H V W : Type*} [Semiring A] [Monoid G] [Monoid H]
  [AddCommMonoid V] [Module A V] [AddCommMonoid W] [Module A W]
  {rho : Representation A G V} {sigma : Representation A G W}

/-- Pull back an equivalence of representations along a monoid homomorphism. -/
def Equiv.pullback (e : Equiv rho sigma) (f : H →* G) :
    Equiv (rho.pullback f) (sigma.pullback f) :=
  Equiv.mk e.toLinearEquiv fun h ↦ e.isIntertwining' (f h)

@[simp]
theorem Equiv.pullback_apply (e : Equiv rho sigma) (f : H →* G) (v : V) :
    e.pullback f v = e v :=
  rfl

end Equiv

section Irreducible

variable {k G H V : Type*} [Field k] [Monoid G] [Monoid H]
  [AddCommGroup V] [Module k V]

/-- Pullback along a surjective monoid homomorphism preserves and reflects
irreducibility. -/
theorem isIrreducible_pullback_iff (rho : Representation k G V) (f : H →* G)
    (hf : Function.Surjective f) :
    IsIrreducible (rho.pullback f) ↔ IsIrreducible rho :=
  OrderIso.isSimpleOrder_iff (subrepresentationPullbackOrderIso rho f hf)

namespace IsIrreducible

/-- A surjective pullback of an irreducible representation is irreducible. -/
theorem pullback {rho : Representation k G V} (hrho : IsIrreducible rho)
    (f : H →* G) (hf : Function.Surjective f) :
    IsIrreducible (rho.pullback f) :=
  (isIrreducible_pullback_iff rho f hf).2 hrho

end IsIrreducible

end Irreducible

section Twist

variable {A G V W : Type*} [Semiring A] [Monoid G]
  [AddCommMonoid V] [Module A V] [AddCommMonoid W] [Module A W]

/-- Twist a representation by precomposing it with a monoid automorphism. -/
def twist (rho : Representation A G V) (alpha : MulAut G) : Representation A G V :=
  rho.pullback alpha.toMonoidHom

@[simp]
theorem twist_apply (rho : Representation A G V) (alpha : MulAut G) (g : G) :
    rho.twist alpha g = rho (alpha g) :=
  rfl

@[simp]
theorem twist_refl (rho : Representation A G V) : rho.twist (MulEquiv.refl G) = rho :=
  rfl

/-- Successive twists use the right action convention: first `alpha`, then
`beta`, is twisting by `alpha * beta`. -/
@[simp]
theorem twist_mul (rho : Representation A G V) (alpha beta : MulAut G) :
    (rho.twist alpha).twist beta = rho.twist (alpha * beta) :=
  rfl

@[simp]
theorem twist_symm_twist (rho : Representation A G V) (alpha : MulAut G) :
    (rho.twist alpha).twist alpha.symm = rho := by
  ext g v
  simp

@[simp]
theorem twist_twist_symm (rho : Representation A G V) (alpha : MulAut G) :
    (rho.twist alpha.symm).twist alpha = rho := by
  ext g v
  simp

/-- Twisting preserves an equivalence of representations. -/
def Equiv.twist {rho : Representation A G V} {sigma : Representation A G W}
    (e : Equiv rho sigma) (alpha : MulAut G) :
    Equiv (rho.twist alpha) (sigma.twist alpha) :=
  e.pullback alpha.toMonoidHom

@[simp]
theorem Equiv.twist_apply {rho : Representation A G V} {sigma : Representation A G W}
    (e : Equiv rho sigma) (alpha : MulAut G) (v : V) :
    e.twist alpha v = e v :=
  rfl

/-- Two representations are equivalent if and only if their twists by the
same automorphism are equivalent. -/
theorem nonempty_equiv_twist_iff {rho : Representation A G V}
    {sigma : Representation A G W} (alpha : MulAut G) :
    Nonempty (Equiv (rho.twist alpha) (sigma.twist alpha)) ↔
      Nonempty (Equiv rho sigma) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨by simpa only [twist_symm_twist] using e.twist alpha.symm⟩
  · rintro ⟨e⟩
    exact ⟨e.twist alpha⟩

end Twist

section TwistIrreducible

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]

/-- Twisting by an automorphism preserves and reflects irreducibility. -/
@[simp]
theorem isIrreducible_twist_iff (rho : Representation k G V) (alpha : MulAut G) :
    IsIrreducible (rho.twist alpha) ↔ IsIrreducible rho :=
  isIrreducible_pullback_iff rho alpha.toMonoidHom alpha.surjective

namespace IsIrreducible

/-- An automorphism twist of an irreducible representation is irreducible. -/
theorem twist {rho : Representation k G V} (hrho : IsIrreducible rho)
    (alpha : MulAut G) : IsIrreducible (rho.twist alpha) :=
  (isIrreducible_twist_iff rho alpha).2 hrho

end IsIrreducible

end TwistIrreducible

section Character

variable {k G H V : Type*} [Field k] [Monoid G] [Monoid H]
  [AddCommGroup V] [Module k V]

/-- Trace functions pull back by composition with the monoid
homomorphism.  This statement does not construct a Brauer character. -/
@[simp]
theorem character_pullback (rho : Representation k G V) (f : H →* G) (h : H) :
    (rho.pullback f).character h = rho.character (f h) :=
  rfl

/-- Function-valued form of `character_pullback`. -/
theorem character_pullback_eq (rho : Representation k G V) (f : H →* G) :
    (rho.pullback f).character = rho.character ∘ f :=
  rfl

/-- The trace function of an automorphism twist is obtained by
precomposing the original trace function with the automorphism. -/
@[simp]
theorem character_twist (rho : Representation k G V) (alpha : MulAut G) (g : G) :
    (rho.twist alpha).character g = rho.character (alpha g) :=
  rfl

/-- Function-valued form of `character_twist`. -/
theorem character_twist_eq (rho : Representation k G V) (alpha : MulAut G) :
    (rho.twist alpha).character = rho.character ∘ alpha :=
  rfl

end Character

end Representation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
