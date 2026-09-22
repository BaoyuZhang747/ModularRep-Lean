import ModularRep.PaperProofs.TypeBRegularLeviRationalAction
import ModularRep.PaperProofs.TypeBRegularLeviComponentPointSource
import ModularRep.PaperProofs.TypeBRegularLeviOrbitTransport
import ModularRep.PaperProofs.TypeBReturnCoordinateAction

/-!
# Construction of the regular-Levi product image and actual character orbits

Original component point data constructs every rational factor, conjugation
action, coordinate square and supported projection. The only Lang premise is
the exact central pointwise consequence on the same B and F. Its geometric
source hypotheses remain explicit E2/U in the source contract.

The action on the original subgroup presentation is transported through actual
carrier equivalences. Product-image surjectivity and the character square are
deductions. Neither is an external source input to the character endpoint.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBRegularLeviOrbitAssembly

open TypeBRegularLeviRationalCarriers TypeBRegularLeviSupportedLift
open TypeBRegularLeviCharacterActionAdapter EvenFieldAssumption53Relative
open TypeBRegularLeviComponentPointSource

variable {B C : Type} [Group B] (F : B →* B)
variable (H : Subgroup B) (hH : ∀ h ∈ H, F h ∈ H)
variable (m : C → ℕ) (data : ComponentPointData F H hH m)
variable (central : ∀ b : B, ∃ h : H, ∃ z : Subgroup.center B, b = (h : B) * z)

/-- The constructed identification with the actual rational component factors. -/
def rationalProduct : rationalSubgroup F H ≃* ((c : C) → rationalFactor F H hH m data c) :=
  TypeBRegularLeviRationalAction.rationalDecomposition F H hH m
    (componentGroup F H hH m data) data.cycles data.frobenius data.monomial
    data.coordinates data.frobenius_value

/-- The actual rational action on an actual return-fixed component. -/
def factorAction (c : C) :
    fixedPoints F →* MulAut (rationalFactor F H hH m data c) :=
  TypeBRegularLeviRationalAction.factorAction F H hH m
    (componentGroup F H hH m data) data.cycles data.frobenius data.monomial
    data.coordinates data.frobenius_value central c

/-- All projection and rational-action laws are supplied by checked deductions. -/
def constructedProjection :
    ProjectionData F H hH (rationalFactor F H hH m data) :=
  TypeBRegularLeviProductProjection.projectionData F H hH m
    (componentGroup F H hH m data) data.cycles data.frobenius data.monomial
    data.coordinates data.frobenius_value central
    (factorAction F H hH m data central)
    (TypeBRegularLeviRationalAction.factorAction_value F H hH m
      (componentGroup F H hH m data) data.cycles data.frobenius data.monomial
      data.coordinates data.frobenius_value central)

/-- Literal factor image, rather than a separately supplied diagonal group. -/
abbrev imageGroup (c : C) : Subgroup (MulAut (rationalFactor F H hH m data c)) :=
  (factorAction F H hH m data central c).range

/-- Product map into the literal images of the constructed actual actions. -/
def imageProduct : fixedPoints F →* ((c : C) → imageGroup F H hH m data central c) :=
  TypeBRegularLeviSupportedLift.productAction F H hH
    (rationalFactor F H hH m data) (constructedProjection F H hH m data central)

/-- This is the actual inclusion of a factor image into its automorphism group. -/
def imageAction (c : C) :
    imageGroup F H hH m data central c →* MulAut (rationalFactor F H hH m data c) :=
  (imageGroup F H hH m data central c).subtype

theorem constructed_groupSquare (b : fixedPoints F) :
    MulAut.congr (rationalProduct F H hH m data)
      (TypeBRegularLeviRationalAction.originalAction F H central b) =
    coordinateMulAut (rationalFactor F H hH m data)
      (fun c ↦ ↥(imageGroup F H hH m data central c))
      (imageAction F H hH m data central) (imageProduct F H hH m data central b) := by
  exact TypeBRegularLeviRationalAction.groupSquare F H hH m
    (componentGroup F H hH m data) data.cycles data.frobenius data.monomial
    data.coordinates data.frobenius_value central b

/-- Product-image surjectivity is proved by the original central correction. -/
theorem imageProduct_surjective [Finite C] (lang : CentralLangSource F) :
    Function.Surjective (imageProduct F H hH m data central) :=
  TypeBRegularLeviSupportedLift.productAction_surjective F H hH
    (rationalFactor F H hH m data) (constructedProjection F H hH m data central) lang

/-- Rational factor finiteness is inherited from the original fixed subgroup
through the computed product, rather than introduced as a free source field. -/
theorem rationalFactor_finite [Finite (fixedPoints F)] (c : C) :
    Finite (rationalFactor F H hH m data c) := by
  letI : Finite ((c : C) → rationalFactor F H hH m data c) :=
    Finite.of_equiv (rationalSubgroup F H) (rationalProduct F H hH m data).toEquiv
  exact Finite.of_surjective (fun x : (c : C) → rationalFactor F H hH m data c ↦ x c)
    (TypeBReturnCoordinateAction.coordinate_surjective (rationalFactor F H hH m data) c)

section OriginalCarriers

variable {G M : Type} [Group G] [Group M]
variable (eG : rationalSubgroup F H ≃* G) (eM : fixedPoints F ≃* M)

/-- The action on the original subgroup presentation. Its pointwise
conjugation formula is discharged in the final paired-Levi wrapper. -/
def originalAction : M →* MulAut G :=
  TypeBRegularLeviOrbitTransport.actionOnOriginal eG eM
    (TypeBRegularLeviRationalAction.originalAction F H central)

def originalProduct : G ≃* ((c : C) → rationalFactor F H hH m data c) :=
  eG.symm.trans (rationalProduct F H hH m data)

def originalImageProduct : M →* ((c : C) → imageGroup F H hH m data central c) :=
  (imageProduct F H hH m data central).comp eM.symm.toMonoidHom

theorem original_groupSquare (b : M) :
    MulAut.congr (originalProduct F H hH m data eG)
      (originalAction F H central eG eM b) =
    coordinateMulAut (rationalFactor F H hH m data)
      (fun c ↦ ↥(imageGroup F H hH m data central c))
      (imageAction F H hH m data central)
      (originalImageProduct F H hH m data central eM b) :=
  TypeBRegularLeviOrbitTransport.groupSquareOnOriginal eG eM
    (TypeBRegularLeviRationalAction.originalAction F H central)
    (rationalFactor F H hH m data) (fun c ↦ ↥(imageGroup F H hH m data central c))
    (rationalProduct F H hH m data) (imageAction F H hH m data central)
    (imageProduct F H hH m data central)
    (constructed_groupSquare F H hH m data central) b

theorem originalImageProduct_surjective [Finite C] (lang : CentralLangSource F) :
    Function.Surjective (originalImageProduct F H hH m data central eM) :=
  (imageProduct_surjective F H hH m data central lang).comp eM.symm.surjective

/-- The image in Aut(L0), after the actual product identification, is exactly
the subgroup of all independent automorphisms from the actual factor images. -/
theorem original_action_image [Finite C] (lang : CentralLangSource F) :
    ((MulAut.congr (originalProduct F H hH m data eG)).toMonoidHom.comp
      (originalAction F H central eG eM)).range =
    (coordinateMulAut (rationalFactor F H hH m data)
      (fun c ↦ ↥(imageGroup F H hH m data central c))
      (imageAction F H hH m data central)).range := by
  ext alpha
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨originalImageProduct F H hH m data central eM b,
      (original_groupSquare F H hH m data central eG eM b).symm⟩
  · rintro ⟨d, rfl⟩
    obtain ⟨b, hb⟩ := originalImageProduct_surjective F H hH m data central eM lang d
    refine ⟨b, ?_⟩
    change MulAut.congr (originalProduct F H hH m data eG)
      (originalAction F H central eG eM b) = _
    rw [original_groupSquare, hb]

section Characters

variable [Fintype C] [Finite (fixedPoints F)] [Finite G]
variable {ell : ℕ} {k K : Type}
variable [Field k] [Field K] [CharP k ell] [IsAlgClosed k] [CharZero K]
local instance factorFinite (c : C) : Finite (rationalFactor F H hH m data c) :=
  rationalFactor_finite F H hH m data c

variable (iota : PrimeRegularRootEmbedding ell k K G)
variable (factorRoot : ∀ c, PrimeRegularRootEmbedding ell k K (rationalFactor F H hH m data c))
variable (productSource : TypeBFiniteProductNaturality.ExternalProductData
  (rationalFactor F H hH m data) (iota.alongMulEquiv (originalProduct F H hH m data eG)) factorRoot)

/-- The actual Brauer-character identification with canonically transported
global root and the four-field standard external-product source. -/
def originalCharacters : IBr iota ≃ ((c : C) → IBr (factorRoot c)) :=
  TypeBRegularLeviCharacterOrbit.tupleEquiv (rationalFactor F H hH m data)
    iota (originalProduct F H hH m data eG) factorRoot productSource

/-- The Cartesian-orbit conclusion on the original set of characters.
The action square and product-image surjectivity are both derived above. -/
theorem cartesian_character_orbit (lang : CentralLangSource F) (base : IBr iota) :
    let _ := rightAutomorphismAction iota (originalAction F H central eG eM)
    originalCharacters F H hH m data eG iota factorRoot productSource '' MulAction.orbit M base =
      {theta | ∀ c,
        let _ := rightAutomorphismAction (factorRoot c) (imageAction F H hH m data central c)
        theta c ∈ MulAction.orbit (imageGroup F H hH m data central c)
          (originalCharacters F H hH m data eG iota factorRoot productSource base c)} :=
  TypeBRegularLeviCharacterOrbit.image_original_orbit_eq_coordinate_orbits
    (rationalFactor F H hH m data) (fun c ↦ ↥(imageGroup F H hH m data central c))
    iota (originalProduct F H hH m data eG) factorRoot productSource
    (imageAction F H hH m data central) (originalAction F H central eG eM)
    (originalImageProduct F H hH m data central eM)
    (original_groupSquare F H hH m data central eG eM)
    (originalImageProduct_surjective F H hH m data central eM lang) base

end Characters
end OriginalCarriers

end ModularRep.PaperProofs.TypeBRegularLeviOrbitAssembly


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
