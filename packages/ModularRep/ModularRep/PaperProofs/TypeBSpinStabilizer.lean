import ModularRep.PaperProofs.TypeBCliffordCarriers
import ModularRep.ConlonStabilizerBridge

/-!
# The effective Spin block stabilizer in Lemma 4.2

The standard E1 outer-group identification places the literal effective
block stabilizer inside `C_2 x C_f` (FLZ Section 3.5, p. 546).  For every
actual subgroup of that product, this file constructs the field projection,
embeds its kernel into the actual first factor, proves the bound two, and
constructs the quotient embedding.  The existing Conlon stabilizer bridge
then proves `2`-hypoelementarity.  Neither a cardinality bound nor a
hypoelementary conclusion is an input.

Matching an action of this subgroup to the literal Spin character and block
actions remains a separate source binding.  There is no iBAW or blockwise
bijection premise in this group-theoretic deduction.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBSpinStabilizer

open ModularRep.PaperProofs.TypeBCliffordCarriers
open ModularRep.IntegralBasicSetBridge
open ModularRep.ManuscriptVerification.ConlonStabilizerBridge

/-- The actual diagonal factor of the type B effective outer group. -/
abbrev DiagonalGroup := Multiplicative (ZMod 2)

/-- The standard type B effective outer group on the Spin group. -/
abbrev OuterGroup (f : ℕ) := DiagonalGroup × FieldGroup f

variable {f : ℕ} [NeZero f]

/-- Restrict the second product projection to the chosen subgroup. -/
def fieldProjection (J : Subgroup (OuterGroup f)) : J →* FieldGroup f :=
  (MonoidHom.snd _ _).comp J.subtype

/-- Restrict the first product projection to the field kernel. -/
def kernelFirstProjection (J : Subgroup (OuterGroup f)) :
    (fieldProjection J).ker →* DiagonalGroup :=
  ((MonoidHom.fst _ _).comp J.subtype).comp (fieldProjection J).ker.subtype

/-- Two kernel elements with the same first coordinate have both
coordinates equal, because their second coordinates are one. -/
theorem kernelFirstProjection_injective (J : Subgroup (OuterGroup f)) :
    Function.Injective (kernelFirstProjection J) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact hxy
  · have hx : x.1.1.2 = 1 := x.2
    have hy : y.1.1.2 = 1 := y.2
    exact hx.trans hy.symm

theorem fieldProjection_kernel_card_le_two (J : Subgroup (OuterGroup f)) :
    Nat.card (fieldProjection J).ker ≤ 2 := by
  have hcard := Nat.card_le_card_of_injective
    (kernelFirstProjection J) (kernelFirstProjection_injective J)
  have hdiagonal : Nat.card DiagonalGroup = 2 := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  simpa only [hdiagonal] using hcard

/-- The first isomorphism theorem realizes the quotient in the cyclic
field group, with no externally supplied quotient map. -/
def quotientFieldEmbedding (J : Subgroup (OuterGroup f)) :
    J ⧸ (fieldProjection J).ker →* FieldGroup f :=
  (fieldProjection J).range.subtype.comp
    (QuotientGroup.quotientKerEquivRange (fieldProjection J)).toMonoidHom

theorem quotientFieldEmbedding_injective (J : Subgroup (OuterGroup f)) :
    Function.Injective (quotientFieldEmbedding J) :=
  (fieldProjection J).range.subtype_injective.comp
    (QuotientGroup.quotientKerEquivRange (fieldProjection J)).injective

/-- The Spin stabilizer assertion of Lemma 4.2 after the exact E1
identification of its effective outer group with `C_2 x C_f`. -/
theorem spin_stabilizer_twoHypoelementary (J : Subgroup (OuterGroup f)) :
    IsPHypoelementary 2 J :=
  isTwoHypoelementary_of_small_normal_quotient_embedding
    (fieldProjection J).ker (fieldProjection_kernel_card_le_two J)
    (quotientFieldEmbedding J) (quotientFieldEmbedding_injective J)

end ModularRep.PaperProofs.TypeBSpinStabilizer


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
