import ModularRep.PaperProofs.EvenFieldGallagherFormula
import ModularRep.PaperProofs.IntermediateRestrictionIrreducible

/-!
# Restricting Spath's extension and applying Gallagher

This module connects the ambient extension in manuscript Lemma 3.6 to the
formula-level Gallagher argument.  The character of the intermediate
restriction is fixed because it is literally restricted from a
representation of the group containing the twisting element.  Fixedness is
therefore derived, not stored in an input field.
-/

namespace ModularRep.PaperProofs.EvenFieldExtensionGallagher

open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs.EvenFieldGallagherFormula

universe u

variable {k K V : Type u} [Field k] [CharZero k] [Group K]
  [AddCommGroup V] [Module k V]

/-- The restricted extension is irreducible and its Gallagher products are
fixed under conjugation by the chosen ambient element. -/
theorem restrictedExtension_and_correspondent_fixed
    (sigma : Representation k K V)
    (I : Subgroup K) [I.Normal]
    (B : Subgroup I) [B.Normal]
    (baseRestriction_irreducible : Representation.IsIrreducible
      (sigma.pullback (I.subtype.comp B.subtype)))
    (tau : K)
    (difference_mem : ∀ x : I,
      x⁻¹ * MulAut.conjNormal tau x ∈ B)
    (kappa : Irr k I)
    (factorisation : HasGallagherFactorisation B
      (sigma.pullback I.subtype).character kappa) :
    Representation.IsIrreducible (sigma.pullback I.subtype) ∧
      twist k I kappa (MulAut.conjNormal tau) = kappa := by
  have hirreducible := Representation.intermediateRestriction_isIrreducible
    sigma I B baseRestriction_irreducible
  have hextension : ∀ x : I,
      (sigma.pullback I.subtype).character (MulAut.conjNormal tau x) =
        (sigma.pullback I.subtype).character x := by
    intro x
    exact congrFun
      (Representation.intermediateRestriction_character_fixed sigma I tau) x
  refine ⟨hirreducible, ?_⟩
  exact EvenFieldGallagherFormula.character_fixed B
    (MulAut.conjNormal tau) difference_mem
    (sigma.pullback I.subtype).character hextension kappa factorisation

end ModularRep.PaperProofs.EvenFieldExtensionGallagher


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
