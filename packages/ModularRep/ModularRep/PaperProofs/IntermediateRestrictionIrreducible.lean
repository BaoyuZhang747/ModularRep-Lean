import ModularRep.CyclicExtension

/-!
# Irreducibility and invariance of intermediate restrictions

This file isolates an elementary representation theoretic step used in the
maximal-extension argument of manuscript Lemma 3.6.  If the restriction of an
ambient representation to a base subgroup is irreducible, then its restriction
to every intermediate subgroup containing that base is irreducible.  When the
intermediate subgroup is normal in the ambient group, the restricted
representation is invariant under ambient conjugation.

No character-theoretic extension or Clifford correspondence is assumed here.
The second conclusion uses only that the restricted representation is the
literal restriction of an ambient representation.
-/

namespace Representation

universe uR uG uV

section Pullback

variable {k : Type uR} {G H : Type uG} {V : Type uV}
variable [Field k] [Monoid G] [Monoid H]
variable [AddCommGroup V] [Module k V]

/-- If a pullback of a representation is irreducible, then the original
representation is irreducible.  Surjectivity of the homomorphism is not
needed in this direction: every invariant subspace for the original
representation is invariant for the pullback. -/
theorem isIrreducible_of_pullback
    (rho : Representation k G V) (f : H →* G)
    (hrestricted : IsIrreducible (rho.pullback f)) :
    IsIrreducible rho := by
  let _ : IsIrreducible (rho.pullback f) := hrestricted
  let _ : Nontrivial (Submodule k V) :=
    (Subrepresentation.toSubmodule_injective
      (ρ := rho.pullback f)).nontrivial
  let _ : Nontrivial V := (Submodule.nontrivial_iff k).mp inferInstance
  let _ : Nontrivial (Subrepresentation rho) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    have h' := congrArg Subrepresentation.toSubmodule h
    exact (bot_ne_top : (⊥ : Submodule k V) ≠ ⊤) h'
  refine { eq_bot_or_eq_top := fun W ↦ ?_ }
  let Wrestricted : Subrepresentation (rho.pullback f) :=
    { toSubmodule := W.toSubmodule
      apply_mem_toSubmodule := fun h _ hv ↦
        W.apply_mem_toSubmodule (f h) hv }
  rcases eq_bot_or_eq_top Wrestricted with hbot | htop
  · left
    apply Subrepresentation.toSubmodule_injective
    have h := congrArg Subrepresentation.toSubmodule hbot
    exact h
  · right
    apply Subrepresentation.toSubmodule_injective
    have h := congrArg Subrepresentation.toSubmodule htop
    exact h

end Pullback

section Intermediate

variable {k : Type uR} {K : Type uG} {V : Type uV}
variable [Field k] [Group K]
variable [AddCommGroup V] [Module k V]

/-- Source-shaped intermediate-subgroup form.  Here `B` is the base subgroup
viewed inside the intermediate subgroup `I`.  Irreducibility of the restriction
to `B` forces irreducibility of the restriction to `I`. -/
theorem intermediateRestriction_isIrreducible
    (sigma : Representation k K V) (I : Subgroup K) (B : Subgroup I)
    (hbase : IsIrreducible
      (sigma.pullback (I.subtype.comp B.subtype))) :
    IsIrreducible (sigma.pullback I.subtype) := by
  apply isIrreducible_of_pullback
    (sigma.pullback I.subtype) B.subtype
  simpa only [pullback_comp] using hbase

/-- The restriction of an ambient representation to a normal intermediate
subgroup is invariant under conjugation by every ambient element.  The
intertwiner is supplied by the action of that element in the ambient
representation. -/
noncomputable def intermediateRestrictionTwistEquiv
    (sigma : Representation k K V) (I : Subgroup K) [I.Normal]
    (tau : K) :
    Representation.Equiv
      ((sigma.pullback I.subtype).twist (MulAut.conjNormal tau))
      (sigma.pullback I.subtype) :=
  Extension.restrictionTwistEquiv sigma tau

/-- Combined form used in the maximal-extension step: irreducibility on the
base subgroup gives irreducibility on the inertia subgroup, and an ambient
representation realising that restriction makes it invariant under every
element of the larger group. -/
theorem intermediateRestriction_irreducible_and_invariant
    (sigma : Representation k K V) (I : Subgroup K) [I.Normal]
    (B : Subgroup I)
    (hbase : IsIrreducible
      (sigma.pullback (I.subtype.comp B.subtype))) :
    IsIrreducible (sigma.pullback I.subtype) ∧
      ∀ tau : K, Nonempty
        (Representation.Equiv
          ((sigma.pullback I.subtype).twist (MulAut.conjNormal tau))
          (sigma.pullback I.subtype)) := by
  refine ⟨intermediateRestriction_isIrreducible sigma I B hbase, ?_⟩
  intro tau
  exact ⟨intermediateRestrictionTwistEquiv sigma I tau⟩

/-- Exact three-level form of the restriction step in manuscript Lemma 3.6.
Irreducibility on `B` forces irreducibility both on the larger group `K` and
on the inertia subgroup `I`.  Normality of `I` in `K` then makes the latter
restriction invariant under `K`. -/
theorem ambient_and_intermediateRestrictions_irreducible_and_invariant
    (sigma : Representation k K V) (I : Subgroup K) [I.Normal]
    (B : Subgroup I)
    (hbase : IsIrreducible
      (sigma.pullback (I.subtype.comp B.subtype))) :
    IsIrreducible sigma ∧
      IsIrreducible (sigma.pullback I.subtype) ∧
      ∀ tau : K, Nonempty
        (Representation.Equiv
          ((sigma.pullback I.subtype).twist (MulAut.conjNormal tau))
          (sigma.pullback I.subtype)) := by
  refine ⟨isIrreducible_of_pullback sigma
      (I.subtype.comp B.subtype) hbase, ?_⟩
  exact intermediateRestriction_irreducible_and_invariant
    sigma I B hbase

/-- Character-level consequence of the ambient realisation.  This is an
identity of trace characters; over a modular coefficient field it is not, by
itself, an identity of Brauer characters. -/
theorem intermediateRestriction_character_fixed
    (sigma : Representation k K V) (I : Subgroup K) [I.Normal]
    (tau : K) :
    ((sigma.pullback I.subtype).twist
        (MulAut.conjNormal tau)).character =
      (sigma.pullback I.subtype).character :=
  Representation.char_iso
    (intermediateRestrictionTwistEquiv sigma I tau)

end Intermediate

end Representation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
