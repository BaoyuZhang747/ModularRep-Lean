import ModularRep.OrdinaryIrreducibleCharacter
import ModularRep.PaperProofs.EvenFieldQuotientTriviality

/-!
# Gallagher's formula in the local step of Lemma 3.6

This file does not represent Gallagher's theorem by an arbitrary equivalence.
Its external input has the exact formula used in the manuscript: a character
above the base constituent is the product of a chosen extension with an
irreducible quotient character inflated from `I / B`.  Once the extension is
fixed and the induced action on `I / B` is trivial, Lean proves that the
character is fixed.
-/

namespace ModularRep.PaperProofs.EvenFieldGallagherFormula

open ModularRep.OrdinaryIrreducibleCharacter

universe u

variable {k I : Type u} [Field k] [CharZero k] [Group I]

/-- Inflation of a quotient character to the inertia group. -/
def inflate (B : Subgroup I) [B.Normal]
    (xi : Irr k (I ⧸ B)) : I → k :=
  fun x ↦ xi (QuotientGroup.mk' B x)

/-- The character function appearing in Gallagher's theorem. -/
def gallagherProduct (B : Subgroup I) [B.Normal]
    (extension : I → k) (xi : Irr k (I ⧸ B)) : I → k :=
  fun x ↦ extension x * inflate B xi x

/-- Source-shaped Gallagher input for one irreducible character.  The
quotient factor is an actual member of `Irr(I / B)`, and the equality is the
published multiplication and inflation formula. -/
def HasGallagherFactorisation (B : Subgroup I) [B.Normal]
    (extension : I → k) (kappa : Irr k I) : Prop :=
  ∃ xi : Irr k (I ⧸ B),
    (kappa : I → k) = gallagherProduct B extension xi

/-- A representative-level quotient-triviality hypothesis gives equality of
the quotient classes of `tau x` and `x`. -/
theorem quotient_mk_tau_eq
    (B : Subgroup I) [B.Normal] (tau : MulAut I)
    (difference_mem : ∀ x : I, x⁻¹ * tau x ∈ B) (x : I) :
    QuotientGroup.mk' B (tau x) = QuotientGroup.mk' B x := by
  change (tau x : I ⧸ B) = (x : I ⧸ B)
  rw [QuotientGroup.eq_iff_div_mem, div_eq_mul_inv]
  have hx : x * (x⁻¹ * tau x) * x⁻¹ ∈ B :=
    (inferInstance : B.Normal).conj_mem (x⁻¹ * tau x)
      (difference_mem x) x
  simpa [mul_assoc] using hx

/-- Formula-level Gallagher deduction used in Lemma 3.6.  No action on an
arbitrary character type and no naturality square is assumed. -/
theorem character_fixed
    (B : Subgroup I) [B.Normal] (tau : MulAut I)
    (difference_mem : ∀ x : I, x⁻¹ * tau x ∈ B)
    (extension : I → k)
    (extension_fixed : ∀ x : I, extension (tau x) = extension x)
    (kappa : Irr k I)
    (factorisation : HasGallagherFactorisation B extension kappa) :
    twist k I kappa tau = kappa := by
  rcases factorisation with ⟨xi, hfactor⟩
  apply OrdinaryIrreducibleCharacter.ext
  intro x
  rw [twist_apply]
  have htau := congrFun hfactor (tau x)
  have hx := congrFun hfactor x
  rw [htau, hx]
  change extension (tau x) * xi (QuotientGroup.mk' B (tau x)) =
    extension x * xi (QuotientGroup.mk' B x)
  rw [extension_fixed, quotient_mk_tau_eq B tau difference_mem]

end ModularRep.PaperProofs.EvenFieldGallagherFormula


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
