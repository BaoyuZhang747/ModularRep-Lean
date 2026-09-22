import ModularRep.OrdinaryIrreducibleCharacter
import ModularRep.ModularTraceSeparation
import ModularRep.CyclicExtension

/-!
# Ordinary characters extend across a cyclic inertia quotient

This module applies `Representation.CyclicExtensionPrinciple` over K.
Isaacs, Corollary 11.22, supplies the classical complex character theorem.
Here the corresponding principle over the chosen field is a hypothesis.
Equality of conjugate character functions gives equivalence of the chosen
irreducible representations by trace separation. The supplied principle
then gives an irreducible character of the ambient group whose restriction
is the original character.

No character-extension existence, conjugation-invariance conclusion, weight,
block, or block-triple relation is introduced as a new source assumption.
An application must establish invariance and cyclicity on its own actual
inertia group. In particular this does not replace an inertia normalizer by
the whole normalizer in the local hypotheses of Brough--Spath Lemma 4.6.
-/

noncomputable section

namespace ModularRep.OrdinaryIrreducibleCharacter

universe u

variable {K H : Type u} [Field K] [CharZero K] [Group H]
variable (N : Subgroup H)

/-- An ordinary-character extension on the fixed ambient group and its
actual normal-subgroup inclusion. -/
def ExtensionWitness (chi : Irr K N) :=
  {chiHat : Irr K H // ∀ x : N, chiHat (x : H) = chi x}

/-- The extended representation produces an actual irreducible ordinary
character; its restriction equality comes from its actual intertwiner. -/
def extensionWitnessOfRepresentation (chi : Irr K N)
    (R : Realisation K N chi.1)
    (E : Representation.Extension N R.representation) : ExtensionWitness N chi :=
  ⟨⟨E.representation.character, ⟨
    { dimension := R.dimension
      representation := E.representation
      irreducible := E.representation_isIrreducible R.irreducible
      character_eq := rfl }⟩⟩, by
    intro x
    exact (E.character_coe x).trans (congrFun R.character_eq x)⟩

variable [IsAlgClosed K] [Finite H] [N.Normal]

/-- Actual fixedness of the ordinary character identifies every conjugate
of its own irreducible representation with that representation. -/
theorem realisation_conjugationInvariant_of_fixed (chi : Irr K N)
    (R : Realisation K N chi.1)
    (hfixed : ∀ h : H, ∀ x : N, chi (MulAut.conjNormal h x) = chi x) :
    Representation.ConjugationInvariant N R.representation := by
  intro h
  apply ModularRep.ModularTraceSeparation.representation_equiv_of_character_eq
    (R.representation.twist (MulAut.conjNormal h)) R.representation
    (R.irreducible.twist (MulAut.conjNormal h)) R.irreducible
  funext x
  change R.representation.character (MulAut.conjNormal h x) =
    R.representation.character x
  rw [R.character_eq]
  exact hfixed h x

/-- The supplied cyclic extension principle gives an ordinary character
extension once invariance and cyclicity have been established. -/
theorem exists_extensionWitness_of_fixed_cyclic_quotient
    (principle : Representation.CyclicExtensionPrinciple.{u, u, u} K)
    (chi : Irr K N) (hcyclic : IsCyclic (H ⧸ N))
    (hfixed : ∀ h : H, ∀ x : N, chi (MulAut.conjNormal h x) = chi x) :
    Nonempty (ExtensionWitness N chi) := by
  obtain ⟨R⟩ := chi.property
  obtain ⟨E⟩ := Representation.exists_extension_of_cyclic_quotient
    principle R.representation R.irreducible hcyclic
    (realisation_conjugationInvariant_of_fixed N chi R hfixed)
  exact ⟨extensionWitnessOfRepresentation N chi R E⟩

/-- Existence of an extending irreducible character, with the pointwise
restriction identity along the subgroup inclusion. -/
theorem exists_extension_of_fixed_cyclic_quotient
    (principle : Representation.CyclicExtensionPrinciple.{u, u, u} K)
    (chi : Irr K N) (hcyclic : IsCyclic (H ⧸ N))
    (hfixed : ∀ h : H, ∀ x : N, chi (MulAut.conjNormal h x) = chi x) :
    ∃ chiHat : Irr K H, ∀ x : N, chiHat (x : H) = chi x := by
  obtain ⟨E⟩ := exists_extensionWitness_of_fixed_cyclic_quotient
    N principle chi hcyclic hfixed
  exact ⟨E.1, E.2⟩

end ModularRep.OrdinaryIrreducibleCharacter


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
