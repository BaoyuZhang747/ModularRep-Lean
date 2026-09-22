import ModularRep.PaperProofs.TypeBRankThreeFactorsComponentModels
import ModularRep.PaperProofs.TypeBRankThreeFactorsFixedPoints
import ModularRep.PaperProofs.TypeBRankThreeFactorsInventoryCases
import ModularRep.PaperProofs.TypeBRankThreeFactorsSpinBinding

/-!
# The actual paired-Levi derived-factor inventory

Starting at the same proper dual Levi, its paired root chart determines the
primal Levi and its actual root-generated derived components. Properness and
the component forms are deduced from the chart and restricted root action.
Only then is the one-component algebraic normalization certificate used.
The original rational product and the classical fixed-model product are
constructed, retaining original coordinate and Lang-adjusted point values.

The final endpoint takes no factor list, finite factor equivalence, rational
product, character selector or block criterion as an external input. Its
standard root/pinning/rational-pairing and one-component normalization inputs
have the precise E1/E2/U scope recorded in the Type B factor contracts.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRankThreeFactorsApplication

open TypeBCliffordCarriers TypeBConformalDualCarriers TypeBRegularLeviRationalCarriers
open TypeBRankThreeFactorsDiagram TypeBRankThreeFactorsPointSource
open TypeBRankThreeFactorsClassicalModels TypeBRankThreeFactorsClassification
open TypeBRankThreeFactorsComponentModels TypeBRankThreeFactorsFixedPoints
open TypeBRankThreeFactorsRationalForms
open TypeBRankThreeFactorsInventoryCases
open TypeBRankThreeFactorsSpinBinding

variable {F A : Type} [Field F] [Finite F] [Field A]
variable {Nbar : NormSource 3 A} {Lstar : Subgroup (PCSp A 3)}
variable (chart : PairedChart Nbar Lstar)
variable (Frob : MulAut (SpecialClifford 3 A))
variable (stable : chart.primalLevi.map Frob.toMonoidHom = chart.primalLevi)
variable (components : ComponentSource chart Frob stable)

/-- Output data for one original component; every finite map is constructed. -/
structure RealizedComponent (c : ComponentIndex chart.selected) where
  form : Form
  recognized : ComponentHasForm chart.selected components.action c form
  normalization : NormalizationData (F := F) chart Frob stable c form
  conjugator : AlgebraicGroup A form
  lang_value : normalization.standard.automorphism conjugator * conjugator⁻¹ =
    normalization.twist⁻¹
  frobenius_square : ∀ x,
    derivedFrobenius chart Frob stable (adjustedEmbedding normalization.embedding conjugator x) =
      adjustedEmbedding normalization.embedding conjugator (normalization.standard.automorphism x)
  equivalence : normalization.standard.RationalModel ≃*
    fixedPoints (components.componentFrobenius c).toMonoidHom
  value : ∀ x, (equivalence x).val.val =
    normalization.embedding (conjugator * x.val * conjugator⁻¹)
  inverse_value : ∀ y,
    normalization.embedding (conjugator * (equivalence.symm y).val * conjugator⁻¹) = y.val.val

/-- The finite root deduction supplies the guard before the published
one-component normalization is applied. -/
theorem exists_realized_component (proper : Lstar ≠ ⊤)
    (normalizations : NormalizationSource (F := F) chart Frob stable components)
    (c : ComponentIndex chart.selected) :
    Nonempty (RealizedComponent (F := F) chart Frob stable components c) := by
  obtain ⟨form, recognized⟩ := exists_component_form chart.selected components.action
    (chart.selected_proper proper) c
  obtain ⟨data⟩ := normalizations.realise c form recognized
  obtain ⟨a, ha, square, e, forward, backward⟩ :=
    exists_component_model chart Frob stable components c form data
  exact ⟨⟨form, recognized, data, a, ha, square, e, forward, backward⟩⟩

/-- Constructed choices on the exhaustive original component index. -/
def realizedComponents (proper : Lstar ≠ ⊤)
    (normalizations : NormalizationSource (F := F) chart Frob stable components)
    (c : ComponentIndex chart.selected) :
    RealizedComponent (F := F) chart Frob stable components c :=
  Classical.choice (exists_realized_component chart Frob stable components proper normalizations c)

/-- First retain the actual one-step fixed factors, before any standard model. -/
def originalProduct : L0 Frob.toMonoidHom chart.primalLevi ≃*
    ((c : ComponentIndex chart.selected) → fixedPoints (components.componentFrobenius c).toMonoidHom) :=
  (fixedDerivedEquivL0 chart Frob stable).symm.trans
    (singletonFixedProductEquiv (geometricComponent chart) components.coordinates
      (derivedFrobenius chart Frob stable) components.componentFrobenius components.coordinateEquation)

@[simp] theorem originalProduct_value (x : L0 Frob.toMonoidHom chart.primalLevi)
    (c : ComponentIndex chart.selected) :
    (originalProduct chart Frob stable components x c).val =
      components.coordinates ((fixedDerivedEquivL0 chart Frob stable).symm x).val c := rfl

/-- The product of actual classical matrix fixed models on the same components. -/
def classicalProduct
    (models : ∀ c, RealizedComponent (F := F) chart Frob stable components c) :
    L0 Frob.toMonoidHom chart.primalLevi ≃*
      ((c : ComponentIndex chart.selected) → (models c).normalization.standard.RationalModel) :=
  (originalProduct chart Frob stable components).trans
    (MulEquiv.piCongrRight fun c => (models c).equivalence.symm)

theorem classicalProduct_value
    (models : ∀ c, RealizedComponent (F := F) chart Frob stable components c)
    (x : L0 Frob.toMonoidHom chart.primalLevi) (c : ComponentIndex chart.selected) :
    (models c).normalization.embedding
      ((models c).conjugator * (classicalProduct chart Frob stable components models x c).val *
        (models c).conjugator⁻¹) =
      (components.coordinates ((fixedDerivedEquivL0 chart Frob stable).symm x).val c :
        derivedLevi chart.primalLevi) :=
  (models c).inverse_value (originalProduct chart Frob stable components x c)

section PhysicalEndpoint

variable (p f : ℕ) [CharP F p] [CharP A p] [IsAlgClosed A] [Algebra F A]
variable (N : NormSource 3 F)
variable (points : CliffordFixedPointSource 3 p f F A N Nbar Frob)
variable (dualFrob : MulAut (PCSp A 3))

/-- Output of the full factor window, still conditional on the exact specified
standard-source realization. The index is the computed root components. -/
structure ActualInventory where
  selected_proper : chart.selected ≠ Finset.univ
  primal_proper : chart.primalLevi < SpinSubgroup 3 A Nbar
  field_parameter : Nat.card F = p ^ f
  rational_pairing : RationalPairingSource chart Frob stable p f N points components dualFrob
  no_component_permutation : components.permutation = 1
  root_actor_preserves_components : ∀ (actor : SelectedAction chart.selected)
    (c : ComponentIndex chart.selected), actor.permutation '' c.val = c.val
  configurations : SixCases chart.selected components.action
  models : ∀ c, RealizedComponent (F := F) chart Frob stable components c
  product : L0 Frob.toMonoidHom chart.primalLevi ≃*
    ((c : ComponentIndex chart.selected) → (models c).normalization.standard.RationalModel)
  product_value : ∀ x c, (models c).normalization.embedding
    ((models c).conjugator * (product x c).val * (models c).conjugator⁻¹) =
      (components.coordinates ((fixedDerivedEquivL0 chart Frob stable).symm x).val c :
        derivedLevi chart.primalLevi)
  finite_product : finiteDerived chart Frob p f N points ≃*
    ((c : ComponentIndex chart.selected) → (models c).normalization.standard.RationalModel)
  finite_product_value : ∀ x, finite_product x = product (finiteDerivedEquivL0 chart Frob p f N points x)
  spin_product : actualSpinDerived chart Frob p f N points ≃*
    ((c : ComponentIndex chart.selected) → (models c).normalization.standard.RationalModel)
  spin_product_value : ∀ x, spin_product x =
    product (actualSpinDerivedEquivL0 chart Frob p f N points x)

/-- A genuine manuscript deduction: the paired primal Levi's original rational
derived group has the exhaustively derived classical fixed-factor models.
The caller binds Lstar to the preceding nonprincipal reduction's actual Levi. -/
theorem source_instantiated_factor_inventory (proper : Lstar ≠ ⊤)
    (pairing : RationalPairingSource chart Frob stable p f N points components dualFrob)
    (normalizations : NormalizationSource (F := F) chart Frob stable components) :
    Nonempty (ActualInventory chart Frob stable components p f N points dualFrob) := by
  let models := realizedComponents chart Frob stable components proper normalizations
  let product := classicalProduct chart Frob stable components models
  refine ⟨⟨chart.selected_proper proper, chart.primalLevi_lt_spin proper,
    pairing.parameter_eq, pairing, components.permutation_eq_one, ?_,
    six_cases chart.selected components.action (chart.selected_proper proper), models, product,
    classicalProduct_value chart Frob stable components models,
    (finiteDerivedEquivL0 chart Frob p f N points).trans product, ?_,
    (actualSpinDerivedEquivL0 chart Frob p f N points).trans product, ?_⟩⟩
  · intro actor c
    obtain ⟨i, hi, hroot⟩ := c.property
    rw [hroot]
    exact actor.component_image i
  · intro x
    rfl
  · intro x
    rfl

end PhysicalEndpoint

end ModularRep.PaperProofs.TypeBRankThreeFactorsApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
