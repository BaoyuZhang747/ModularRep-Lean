import ModularRep.Twist
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupExtension.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Extension across a cyclic quotient

This file isolates the representation-level content surrounding Lemma 2.9 of
the accompanying manuscript.  It defines invariance under ambient
conjugation and what it means for a representation of a normal subgroup to
extend to the ambient group.  It then packages the cited cyclic-extension
theorem as an explicit principle.

The principle is not proved here. Isaacs, Corollary 11.22, treats ordinary
complex characters. Its version over a chosen coefficient field is supplied
separately. Navarro, Theorem 8.12, treats the modular case over an algebraically
closed field. Character separation and realisation relate these character
statements to the representation invariance predicate below.
-/

namespace Representation

universe uR uH uV

section Basic

variable {R : Type uR} {H : Type uH} {V : Type uV}
variable [Semiring R] [Group H] [AddCommMonoid V] [Module R V]
variable (N : Subgroup H) [N.Normal]

/-- A representation of a normal subgroup is invariant under ambient
conjugation when every conjugation twist is equivalent to the original
representation. -/
def ConjugationInvariant (rho : Representation R N V) : Prop :=
  ∀ h : H, Nonempty
    (Representation.Equiv
      (rho.twist (MulAut.conjNormal h)) rho)

/-- An extension of `rho` is an ambient representation whose restriction to
`N` is equivalent to `rho`.  Equivalence, rather than literal equality,
makes the definition independent of the chosen representation space. -/
structure Extension (rho : Representation R N V) where
  representation : Representation R H V
  restrictionEquiv : Representation.Equiv
    (representation.pullback N.subtype) rho

namespace Extension

variable {N}
variable {rho : Representation R N V}

omit [N.Normal] in
/-- Elementwise intertwining identity for the restriction equivalence stored
in an extension. -/
theorem map_restriction (E : Extension N rho) (n : N) (v : V) :
    E.restrictionEquiv (E.representation (n : H) v) =
      rho n (E.restrictionEquiv v) := by
  exact DFunLike.congr_fun (E.restrictionEquiv.isIntertwining' n) v

/-- Conjugation of the restriction of an ambient representation is
equivalent to that restriction.  The intertwiner is the action of `h⁻¹`. -/
noncomputable def restrictionTwistEquiv
    (sigma : Representation R H V) (h : H) :
    Representation.Equiv
      ((sigma.pullback N.subtype).twist (MulAut.conjNormal h))
      (sigma.pullback N.subtype) :=
  Representation.Equiv.mk
    (LinearEquiv.ofBijective (sigma h⁻¹) (sigma.apply_bijective h⁻¹)) (by
      intro n
      ext v
      change sigma h⁻¹ (sigma (h * (n : H) * h⁻¹) v) =
        sigma (n : H) (sigma h⁻¹ v)
      simp only [← Module.End.mul_apply, ← map_mul]
      congr 2
      group)

/-- Every actual extension supplies conjugation invariance of the original
representation. -/
theorem conjugationInvariant (E : Extension N rho) :
    ConjugationInvariant N rho := by
  intro h
  exact ⟨(E.restrictionEquiv.twist (MulAut.conjNormal h)).symm |>.trans
    ((restrictionTwistEquiv E.representation h).trans E.restrictionEquiv)⟩

end Extension

end Basic

section Irreducible

variable {k : Type uR} {H : Type uH} {V : Type uV}
variable [Field k] [Group H] [AddCommGroup V] [Module k V]
variable {N : Subgroup H} {rho : Representation k N V}

namespace Extension

/-- If the representation of `N` is irreducible, then every extension to
`H` is irreducible.  Normality of `N` is not needed: every `H`-stable
submodule is automatically `N`-stable. -/
theorem representation_isIrreducible (E : Extension N rho)
    (hirr : Representation.IsIrreducible rho) :
    Representation.IsIrreducible E.representation := by
  let _ : Representation.IsIrreducible rho := hirr
  let _ : Nontrivial (Submodule k V) :=
    (Subrepresentation.toSubmodule_injective (ρ := rho)).nontrivial
  let _ : Nontrivial V := (Submodule.nontrivial_iff k).mp inferInstance
  let _ : Nontrivial (Subrepresentation E.representation) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    have h' := congrArg Subrepresentation.toSubmodule h
    exact (bot_ne_top : (⊥ : Submodule k V) ≠ ⊤) h'
  refine { eq_bot_or_eq_top := fun W ↦ ?_ }
  let W_rho : Subrepresentation rho :=
    { toSubmodule := W.toSubmodule.map E.restrictionEquiv.toLinearMap
      apply_mem_toSubmodule := by
        intro n v hv
        obtain ⟨w, hw, rfl⟩ := hv
        refine ⟨E.representation (n : H) w,
          W.apply_mem_toSubmodule (n : H) hw, ?_⟩
        exact E.map_restriction n w }
  rcases eq_bot_or_eq_top W_rho with hbot | htop
  · left
    apply Subrepresentation.toSubmodule_injective
    have hmap :
        W.toSubmodule.map E.restrictionEquiv.toLinearMap = ⊥ := by
      change W_rho.toSubmodule = ⊥
      rw [hbot]
      rfl
    exact (Submodule.map_eq_bot_iff
      (e := E.restrictionEquiv.toLinearEquiv)).mp hmap
  · right
    apply Subrepresentation.toSubmodule_injective
    have hmap :
        W.toSubmodule.map E.restrictionEquiv.toLinearMap = ⊤ := by
      change W_rho.toSubmodule = ⊤
      rw [htop]
      rfl
    exact (Submodule.map_eq_top_iff
      (e := E.restrictionEquiv.toLinearEquiv)).mp hmap

end Extension

end Irreducible

section Character

variable {k : Type uR} {H : Type uH} {V : Type uV}
variable [Field k] [Group H]
variable [AddCommGroup V] [Module k V]
variable {N : Subgroup H}
variable {rho : Representation k N V}

namespace Extension

/-- The trace character of an extension restricts to the trace character of
the original representation, using the equivalence stored in `Extension`.

For a modular coefficient field this remains a trace identity; it is not by
itself an identity of Brauer characters. -/
theorem restrictedCharacter_eq (E : Extension N rho) :
    (E.representation.pullback N.subtype).character = rho.character :=
  Representation.char_iso E.restrictionEquiv

/-- Elementwise form of `restrictedCharacter_eq`. -/
theorem character_coe (E : Extension N rho) (n : N) :
    E.representation.character (n : H) = rho.character n := by
  exact congrFun E.restrictedCharacter_eq n

end Extension

namespace ConjugationInvariant

/-- Representation-level conjugation invariance implies invariance of the
trace character under ambient conjugation. -/
theorem character_conj [N.Normal]
    (hinvariant : ConjugationInvariant N rho) (h : H) (n : N) :
    rho.character (MulAut.conjNormal h n) = rho.character n := by
  obtain ⟨e⟩ := hinvariant h
  have hc := congrFun (Representation.char_iso e) n
  simpa using hc

end ConjugationInvariant

namespace Extension

/-- The restricted trace character of an extension is invariant under
ambient conjugation. -/
theorem character_conj [N.Normal] (E : Extension N rho) (h : H) (n : N) :
    rho.character (MulAut.conjNormal h n) = rho.character n :=
  ConjugationInvariant.character_conj E.conjugationInvariant h n

end Extension

end Character

/-- The external extension theorem needed in the cyclic-quotient case.

The principle is supplied independently for the ordinary and modular
coefficient fields.  It is not a consequence of the coefficient-ring data in
`ModularSystem`: its character-theoretic applications require the relevant
splitting hypotheses and realisation of irreducible characters. -/
def CyclicExtensionPrinciple (k : Type uR) [Field k] : Prop :=
  ∀ {H : Type uH} [Group H] [Finite H]
    (N : Subgroup H) [N.Normal]
    {V : Type uV} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : Representation k N V),
    Representation.IsIrreducible rho →
    IsCyclic (H ⧸ N) →
    ConjugationInvariant N rho →
    Nonempty (Extension N rho)

/-- The source-shaped modular instance of `CyclicExtensionPrinciple`.

Navarro, *Characters and Blocks of Finite Groups*, Theorem (8.12), p. 163,
works over the fixed algebraically closed field of characteristic `p` used in
that book.  Its proof starts with a representation affording the invariant
irreducible Brauer character and constructs an extension on the same vector
space.  Thus the theorem supplies precisely this proposition. -/
def BrauerCyclicExtensionPrinciple
    (p : ℕ) (k : Type uR) [Field k] [CharP k p] [IsAlgClosed k] : Prop :=
  CyclicExtensionPrinciple.{uR, uH, uV} k

/-- Direct use of an explicitly supplied cyclic-extension principle. -/
theorem exists_extension_of_cyclic_quotient
    {k : Type uR} [Field k]
    (principle : CyclicExtensionPrinciple.{uR, uH, uV} k)
    {H : Type uH} [Group H] [Finite H]
    {N : Subgroup H} [N.Normal]
    {V : Type uV} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : Representation k N V)
    (hirr : Representation.IsIrreducible rho)
    (hcyclic : IsCyclic (H ⧸ N))
    (hinvariant : ConjugationInvariant N rho) :
    Nonempty (Extension N rho) :=
  principle N (V := V) rho hirr hcyclic hinvariant

/-- If the quotient embeds in a cyclic group, the supplied cyclic-extension
principle applies.  This is the group-theoretic step used for the global and
local stabiliser quotients in the manuscript: the existence of the embedding
is semantic input, while cyclicity of its domain is proved here. -/
theorem exists_extension_of_quotient_embedding_cyclic
    {k : Type uR} [Field k]
    (principle : CyclicExtensionPrinciple.{uR, uH, uV} k)
    {H : Type uH} [Group H] [Finite H]
    {N : Subgroup H} [N.Normal]
    {E : Type*} [Group E] [IsCyclic E]
    {V : Type uV} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : Representation k N V)
    (hirr : Representation.IsIrreducible rho)
    (embedding : (H ⧸ N) →* E)
    (hinjective : Function.Injective embedding)
    (hinvariant : ConjugationInvariant N rho) :
    Nonempty (Extension N rho) := by
  apply exists_extension_of_cyclic_quotient principle rho hirr
    (isCyclic_of_injective embedding hinjective) hinvariant

/-- Application to a semidirect product with cyclic outer factor.  The
normal subgroup is the canonical embedded copy of the left factor.  Lean
constructs the quotient embedding into the outer factor, so this group
theoretic part of the extension step does not remain a manuscript input. -/
theorem exists_extension_to_semidirect_of_cyclic_outer
    {k : Type uR} [Field k]
    (principle : CyclicExtensionPrinciple.{uR, uH, uV} k)
    {D E : Type uH} [Group D] [Finite D]
    [Group E] [Finite E] [IsCyclic E]
    (phi : E →* MulAut D)
    {V : Type uV} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : Representation k
      (SemidirectProduct.rightHom (φ := phi)).ker V)
    (hirr : Representation.IsIrreducible rho)
    (hinvariant : ConjugationInvariant
      (SemidirectProduct.rightHom (φ := phi)).ker rho) :
    Nonempty (Extension
      (SemidirectProduct.rightHom (φ := phi)).ker rho) := by
  let N : Subgroup (D ⋊[phi] E) :=
    (SemidirectProduct.rightHom (φ := phi)).ker
  let _ : Finite (D ⋊[phi] E) :=
    Finite.of_injective
      (fun p : D ⋊[phi] E ↦ (p.left, p.right)) (by
        intro p q h
        exact SemidirectProduct.ext
          (congrArg Prod.fst h) (congrArg Prod.snd h))
  let quotientEquiv : ((D ⋊[phi] E) ⧸ N) ≃* E :=
    (SemidirectProduct.toGroupExtension phi).quotientKerRightHomEquivRight
  exact exists_extension_of_quotient_embedding_cyclic principle rho hirr
    quotientEquiv.toMonoidHom quotientEquiv.injective hinvariant

end Representation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
