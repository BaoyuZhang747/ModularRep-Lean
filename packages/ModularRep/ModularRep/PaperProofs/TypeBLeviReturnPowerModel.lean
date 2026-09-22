import ModularRep.PaperProofs.TypeBLeviReturnPowerAutomorphism

/-!
# One normalized model for the defining and positive-return maps

The finite fixed-point identification is constructed from the same adjusted
geometric embedding and its literal range. The inclusion of the standard
fixed subgroup is canonical. No finite-factor equivalence or independently
normalized return is an input.

The actual positive return is compared through its original ambient
Frobenius-value equation. The resulting conjugation square uses the same
embedding and Lang element as the fixed-point equivalence. Identifying the
standard fixed subgroup with a concrete SL, SU or Spin coefficient model
still requires its actual coefficient inclusion, pinning and fixed-subgroup
interpretation. This file supplies no such source inhabitant or selector.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBLeviReturnPowerModel

open TypeBRegularLeviRationalCarriers
open TypeBRankThreeFactorsRationalForms
open TypeBLeviReturnPowerFixedPoints TypeBLeviReturnPowerAutomorphism

variable {B S : Type*} [Group B] [Group S]

/-- The defining square uses only its own exponent, with the same Lang adjustment. -/
theorem normalized_defining_square (j : S →* B) (F0 F : Monoid.End B)
    (Φ : Monoid.End S) (h u d s : ℕ)
    (hF : F = F0 ^ h) (fixed_exponent : h * d = u * s)
    (c : S) (generator_value : ∀ x, (F0 ^ u) (j x) = j (c * Φ x * c⁻¹))
    (a : S) (lang_value : Φ a * a⁻¹ = c⁻¹) (x : S) :
    (F ^ d) (adjustedEmbedding j a x) = adjustedEmbedding j a ((Φ ^ s) x) := by
  rw [defining_power F0 F h u d s hF fixed_exponent]
  exact intertwining_power (adjustedEmbedding j a) (F0 ^ u) Φ
    (adjustedEmbedding_frobenius j (F0 ^ u) Φ c generator_value a lang_value) s x

section Model

variable (j : S →* B) (U : Subgroup B)
variable (j_injective : Function.Injective j) (j_range : j.range = U)
variable (F0 F : Monoid.End B) (Φ : Monoid.End S) (h u d s : ℕ)
variable (hF : F = F0 ^ h) (fixed_exponent : h * d = u * s)
variable (c : S) (generator_value : ∀ x, (F0 ^ u) (j x) = j (c * Φ x * c⁻¹))
variable (a : S) (lang_value : Φ a * a⁻¹ = c⁻¹)

/-- Construct the identification from the two literal subgroup ranges. -/
def normalizedFixedEquiv :
    fixedPoints (Φ ^ s) ≃* rationalSubgroup (F ^ d) U :=
  finiteRationalEquiv (adjustedEmbedding j a) U
    (adjustedEmbedding_injective j j_injective a)
    (adjustedEmbedding_range j U j_range a)
    (F ^ d) (Φ ^ s)
    (normalized_defining_square j F0 F Φ h u d s hF fixed_exponent
      c generator_value a lang_value)
    (fixedPoints (Φ ^ s)).subtype
    (fixedPoints (Φ ^ s)).subtype_injective
    (fixedPoints (Φ ^ s)).range_subtype

/-- Forward values remain values of the same adjusted geometric embedding. -/
@[simp] theorem normalizedFixedEquiv_value (x : fixedPoints (Φ ^ s)) :
    (normalizedFixedEquiv j U j_injective j_range F0 F Φ h u d s
      hF fixed_exponent c generator_value a lang_value x).1.1 =
        adjustedEmbedding j a x.1 := rfl

/-- The inverse identification has the same exact ambient-value equation. -/
theorem normalizedFixedEquiv_symm_value (y : rationalSubgroup (F ^ d) U) :
    adjustedEmbedding j a
      ((normalizedFixedEquiv j U j_injective j_range F0 F Φ h u d s
        hF fixed_exponent c generator_value a lang_value).symm y).1 = y.1.1 := by
  have equality := congrArg (fun z : rationalSubgroup (F ^ d) U ↦ z.1.1)
    ((normalizedFixedEquiv j U j_injective j_range F0 F Φ h u d s
      hF fixed_exponent c generator_value a lang_value).apply_symm_apply y)
  simpa only [normalizedFixedEquiv_value] using equality

/-- The original positive-return value equation yields the normalized square. -/
theorem normalizedFixedEquiv_return_square
    (v q r : ℕ) (return_exponent : v + h * q = u * r) (hs : 0 < s)
    (actualReturn : MulAut (rationalSubgroup (F ^ d) U))
    (return_value : ∀ y, (actualReturn y).1.1 = (F ^ q) ((F0 ^ v) y.1.1))
    (x : fixedPoints (Φ ^ s)) :
    actualReturn (normalizedFixedEquiv j U j_injective j_range F0 F Φ h u d s
      hF fixed_exponent c generator_value a lang_value x) =
    normalizedFixedEquiv j U j_injective j_range F0 F Φ h u d s
      hF fixed_exponent c generator_value a lang_value (fixedPowerAut Φ r s hs x) := by
  apply Subtype.ext
  apply Subtype.ext
  simp only [return_value, normalizedFixedEquiv_value, fixedPowerAut_value]
  exact (normalized_simultaneous_powers j F0 F Φ h u v q r d s hF
    return_exponent fixed_exponent c generator_value a lang_value).1 x.1

/-- Conjugating the actual positive return gives the concrete standard power. -/
theorem normalizedFixedEquiv_conjugates_return
    (v q r : ℕ) (return_exponent : v + h * q = u * r) (hs : 0 < s)
    (actualReturn : MulAut (rationalSubgroup (F ^ d) U))
    (return_value : ∀ y, (actualReturn y).1.1 = (F ^ q) ((F0 ^ v) y.1.1)) :
    MulAut.congr
      (normalizedFixedEquiv j U j_injective j_range F0 F Φ h u d s
        hF fixed_exponent c generator_value a lang_value).symm actualReturn =
      fixedPowerAut Φ r s hs := by
  let e := normalizedFixedEquiv j U j_injective j_range F0 F Φ h u d s
    hF fixed_exponent c generator_value a lang_value
  change MulAut.congr e.symm actualReturn = fixedPowerAut Φ r s hs
  apply MulEquiv.ext
  intro x
  apply e.injective
  change e (e.symm (actualReturn (e x))) = e (fixedPowerAut Φ r s hs x)
  rw [e.apply_symm_apply]
  exact normalizedFixedEquiv_return_square j U j_injective j_range F0 F Φ h u d s
    hF fixed_exponent c generator_value a lang_value v q r return_exponent hs
    actualReturn return_value x

end Model

end ModularRep.PaperProofs.TypeBLeviReturnPowerModel


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
