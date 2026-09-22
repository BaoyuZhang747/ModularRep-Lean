import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Triviality of the relative quotient action in Lemma 3.6

The manuscript does not merely assume that the field action on a relative
quotient is inner.  It proves that for every representative `x`, the element
`x⁻¹ * sigma x` lies in the base subgroup.  The lemmas below turn exactly
that representative-level statement into equality of the induced quotient
endomorphism with the identity.
-/

namespace ModularRep.PaperProofs.EvenFieldQuotientTriviality

universe u

variable {K : Type u} [Group K]

/-- A homomorphism preserving a normal subgroup induces an endomorphism of
the quotient. -/
def quotientEndomorphism (B : Subgroup K) [B.Normal]
    (sigma : K →* K) (preserves : ∀ x : B, sigma x ∈ B) :
    K ⧸ B →* K ⧸ B :=
  QuotientGroup.map B B sigma (by
    intro x hx
    exact preserves ⟨x, hx⟩)

@[simp]
theorem quotientEndomorphism_mk (B : Subgroup K) [B.Normal]
    (sigma : K →* K) (preserves : ∀ x : B, sigma x ∈ B) (x : K) :
    quotientEndomorphism B sigma preserves (QuotientGroup.mk' B x) =
      QuotientGroup.mk' B (sigma x) :=
  rfl

/-- If `x⁻¹ sigma(x)` lies in the base subgroup for every representative,
then the induced endomorphism of the quotient is the identity. -/
theorem quotientEndomorphism_eq_id
    (B : Subgroup K) [B.Normal]
    (sigma : K →* K) (preserves : ∀ x : B, sigma x ∈ B)
    (difference_mem : ∀ x : K, x⁻¹ * sigma x ∈ B) :
    quotientEndomorphism B sigma preserves = MonoidHom.id (K ⧸ B) := by
  apply QuotientGroup.monoidHom_ext
  ext x
  change (sigma x : K ⧸ B) = (x : K ⧸ B)
  rw [QuotientGroup.eq_iff_div_mem]
  rw [div_eq_mul_inv]
  have hx : x * (x⁻¹ * sigma x) * x⁻¹ ∈ B :=
    (inferInstance : B.Normal).conj_mem (x⁻¹ * sigma x)
      (difference_mem x) x
  simpa [mul_assoc] using hx

/-- Pointwise form of quotient triviality. -/
theorem quotientEndomorphism_apply
    (B : Subgroup K) [B.Normal]
    (sigma : K →* K) (preserves : ∀ x : B, sigma x ∈ B)
    (difference_mem : ∀ x : K, x⁻¹ * sigma x ∈ B)
    (q : K ⧸ B) :
    quotientEndomorphism B sigma preserves q = q := by
  rw [quotientEndomorphism_eq_id B sigma preserves difference_mem]
  rfl

end ModularRep.PaperProofs.EvenFieldQuotientTriviality


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
