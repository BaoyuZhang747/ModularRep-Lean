import ModularRep.PaperProofs.TypeBRankThreeFactorsClassification
import ModularRep.PaperProofs.TypeBRankThreeFactorsRationalForms

/-!
# One-component classical realization after the computed root guard

The source below never supplies a factor form or a rational product. For a
specified actual component whose root support and internal graph action have
already been identified, it supplies the standard algebraic realization and
its original Frobenius equation up to a displayed inner twist. Lang is used
only at that twist. The finite equivalence and its value equations are K.

E1/E2 source locators: MT Theorem 9.13/Table 9.2, pp. 70--72 (simply connected
classical model), Proposition 12.14, p. 103 (derived Levi), Theorem 22.5 and
Example 22.6, pp. 191--192 (specified q and graph part up to inner twist), and
Theorem 21.7, p. 184 (Lang). DM 2020 Example 4.3.3, p. 71 fixes the unitary
matrix convention. Authentic algebraic pinnings, root datum, and applicability
to these literal component subgroups remain the displayed E1/E2/U boundary.
The source must not be authenticated merely because its record is inhabited.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRankThreeFactorsComponentModels

open TypeBCliffordCarriers TypeBConformalDualCarriers TypeBRegularLeviRationalCarriers
open TypeBRankThreeFactorsPointSource TypeBRankThreeFactorsClassicalModels
open TypeBRankThreeFactorsClassification TypeBRankThreeFactorsRationalForms

variable {F A : Type} [Field F] [Finite F] [Field A]
variable {Nbar : NormSource 3 A} {Lstar : Subgroup (PCSp A 3)}
variable (chart : PairedChart Nbar Lstar)
variable (Frob : MulAut (SpecialClifford 3 A))
variable (stable : chart.primalLevi.map Frob.toMonoidHom = chart.primalLevi)
variable (components : ComponentSource chart Frob stable)

/-- One-way algebraic normalization on one already identified component.
The model is an actual matrix group and the return map is the original one.
No finite-component equivalence is a source field. -/
structure NormalizationData (c : ComponentIndex chart.selected) (form : Form) where
  standard : StandardFrobenius F A form
  embedding : AlgebraicGroup A form →* derivedLevi chart.primalLevi
  injective : Function.Injective embedding
  range : embedding.range = geometricComponent chart c
  twist : AlgebraicGroup A form
  return_value : ∀ x, derivedFrobenius chart Frob stable (embedding x) =
    embedding (twist * standard.automorphism x * twist⁻¹)
  lang : ∃ a : AlgebraicGroup A form,
    standard.automorphism a * a⁻¹ = twist⁻¹

/-- The standard one-component theorem is applicable only after the root and
graph guard has been derived. In particular it does not choose a form. -/
structure NormalizationSource where
  realise : ∀ (c : ComponentIndex chart.selected) (form : Form),
    ComponentHasForm chart.selected components.action c form →
      Nonempty (NormalizationData (F := F) chart Frob stable c form)

/-- Reorder only the two literal fixedness/component-membership proofs. -/
def componentFixedEquivRational (c : ComponentIndex chart.selected) :
    fixedPoints (components.componentFrobenius c).toMonoidHom ≃*
      rationalSubgroup (derivedFrobenius chart Frob stable).toMonoidHom
        (geometricComponent chart c) where
  toFun x := ⟨⟨x.val.val, congrArg Subtype.val x.property⟩, x.val.property⟩
  invFun x := ⟨⟨x.val.val, x.property⟩, Subtype.ext x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem componentFixedEquivRational_value
    (c : ComponentIndex chart.selected)
    (x : fixedPoints (components.componentFrobenius c).toMonoidHom) :
    (componentFixedEquivRational chart Frob stable components c x).val.val = x.val.val := rfl

/-- Construct the same component's rational model, preserving the Lang
conjugator, the original Frobenius square, and both original point values. -/
theorem exists_component_model (c : ComponentIndex chart.selected) (form : Form)
    (data : NormalizationData (F := F) chart Frob stable c form) :
    ∃ a : AlgebraicGroup A form,
      data.standard.automorphism a * a⁻¹ = data.twist⁻¹ ∧
      (∀ x, derivedFrobenius chart Frob stable (adjustedEmbedding data.embedding a x) =
        adjustedEmbedding data.embedding a (data.standard.automorphism x)) ∧
      ∃ e : data.standard.RationalModel ≃*
          fixedPoints (components.componentFrobenius c).toMonoidHom,
        (∀ x, (e x).val.val = data.embedding (a * x.val * a⁻¹)) ∧
        (∀ y, data.embedding (a * (e.symm y).val * a⁻¹) = y.val.val) := by
  let fixed := fixedPoints data.standard.automorphism.toMonoidHom
  have range_subtype : fixed.subtype.range = fixed := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨a, ha, square, e, forward, backward⟩ :=
    exists_rationalForm data.embedding (geometricComponent chart c) data.injective data.range
      (derivedFrobenius chart Frob stable).toMonoidHom
      data.standard.automorphism.toMonoidHom data.twist data.return_value data.lang
      fixed.subtype Subtype.val_injective range_subtype
  let rearrange := componentFixedEquivRational chart Frob stable components c
  refine ⟨a, ha, square, e.trans rearrange.symm, ?_, ?_⟩
  · intro x
    exact forward x
  · intro y
    exact backward (rearrange y)

end ModularRep.PaperProofs.TypeBRankThreeFactorsComponentModels


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
