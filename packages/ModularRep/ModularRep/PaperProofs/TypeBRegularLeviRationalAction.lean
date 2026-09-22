import ModularRep.PaperProofs.TypeBRegularLeviProductProjection
import ModularRep.PaperProofs.TypeBRegularLeviCharacterActionAdapter
import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Actual rational conjugation on the regular-Levi component factors

The geometric decomposition B = H Z(B) proves H normal. Conjugation then
acts on its literal Frobenius-fixed subgroup. The previously constructed
fixed-product equivalence provides the rational decomposition and actual
Frobenius-diagonal factor inclusions.

The output at each coordinate depends only on the corresponding input:
after writing b = h z geometrically, its value is conjugation by the first
coordinate of h. This proves that inserting a factor, conjugating, and
evaluating that factor defines an automorphism. Its inverse and the group
homomorphism laws are deductions from the original conjugation action.
No rational action, action-value square, coordinate square, supported lift,
product-image assertion or character conclusion is an input.

The original geometric component/Frobenius identification and geometric
central decomposition remain explicit lower inputs. Their specialization
to the actual paired Levi and derived subgroup belongs to the source
wrapper; no unrelated group is identified with those carriers here.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBRegularLeviRationalAction

open TypeBComponentCycleNormalization
open TypeBRegularLeviRationalCarriers
open TypeBRegularLeviComponentFixedPoints
open TypeBRegularLeviSupportedLift
open TypeBRegularLeviProductProjection
open TypeBRegularLeviCharacterActionAdapter

section OriginalAction

variable {B : Type} [Group B] (F : B →* B) (H : Subgroup B)
variable (decomposition : ∀ b : B, ∃ h : H, ∃ z : Subgroup.center B, b = (h : B) * z)

include decomposition in
/-- Geometric central decomposition proves normality of the displayed H. -/
theorem geometric_normal : H.Normal where
  conj_mem x hx b := by
    obtain ⟨h, z, rfl⟩ := decomposition b
    rw [conjugation_mul_central]
    exact H.mul_mem (H.mul_mem h.property hx) (H.inv_mem h.property)

/-- The original action is literally conjugation in the same rational
ambient group on its actual rational H subgroup. -/
def originalAction : fixedPoints F →* MulAut (rationalSubgroup F H) := by
  letI : H.Normal := geometric_normal H decomposition
  letI : (rationalSubgroup F H).Normal := rational_normal F H
  exact MulAut.conjNormal

@[simp]
theorem originalAction_value (b : fixedPoints F) (x : rationalSubgroup F H) :
    (originalAction F H decomposition b x).1.1 =
      (b : B) * x.1.1 * (b : B)⁻¹ := rfl

end OriginalAction

section Decomposition

variable {B C : Type} [Group B] (F : B →* B)
variable (H : Subgroup B) (hH : ∀ h ∈ H, F h ∈ H)
variable (m : C → ℕ) (V : Index m → Type) [∀ i, Group (V i)]
variable (S : CycleCoordinates m V) (a : MulAut (Original m V))
variable (ha : MonomialAction m V S a) (e : H ≃* Original m V)
variable (hF : ∀ h : H, e (derivedFrobenius F H hH h) = a (e h))

/-- Restrict the original geometric identification to its actual fixed
points. Both directions use the same displayed Frobenius square. -/
def rationalGeometricEquiv : rationalSubgroup F H ≃* fixedPoints a.toMonoidHom where
  toFun x := ⟨e ⟨x.1.1, x.2⟩, by
    change a (e ⟨x.1.1, x.2⟩) = e ⟨x.1.1, x.2⟩
    have hx : derivedFrobenius F H hH ⟨x.1.1, x.2⟩ = ⟨x.1.1, x.2⟩ :=
      Subtype.ext x.1.2
    rw [← hF, hx]⟩
  invFun x := ⟨⟨(e.symm x.1 : H), by
    have hx : derivedFrobenius F H hH (e.symm x.1) = e.symm x.1 := by
      apply e.injective
      rw [hF, e.apply_symm_apply]
      exact x.2
    exact congrArg Subtype.val hx⟩, (e.symm x.1).property⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    change ((e.symm (e ⟨x.1.1, x.2⟩) : H) : B) = x.1.1
    exact congrArg Subtype.val (e.symm_apply_apply ⟨x.1.1, x.2⟩)
  right_inv x := Subtype.ext (e.apply_symm_apply x.1)
  map_mul' x y := Subtype.ext (e.map_mul ⟨x.1.1, x.2⟩ ⟨y.1.1, y.2⟩)

/-- The canonical decomposition on the original rational subgroup. -/
def rationalDecomposition : rationalSubgroup F H ≃* (∀ c, Factor m V S c) :=
  (rationalGeometricEquiv F H hH m V a e hF).trans (fixedProductEquiv m V S a ha)

@[simp]
theorem rationalDecomposition_value (x : rationalSubgroup F H) (c : C) :
    (rationalDecomposition F H hH m V S a ha e hF x c).1 =
      e ⟨x.1.1, x.2⟩ (first m c) := rfl

/-- The original point underlying a tuple is the same inverse geometric
fixed-product element used by the existing factorEmbedding. -/
@[simp]
theorem rationalDecomposition_symm_value (x : ∀ c, Factor m V S c) :
    ((rationalDecomposition F H hH m V S a ha e hF).symm x).1.1 =
      ((e.symm (((fixedProductEquiv m V S a ha).symm x).1) : H) : B) := rfl

end Decomposition

section CoordinateAction

variable {B C : Type} [Group B] (F : B →* B)
variable (H : Subgroup B) (hH : ∀ h ∈ H, F h ∈ H)
variable (m : C → ℕ) (V : Index m → Type) [∀ i, Group (V i)]
variable (S : CycleCoordinates m V) (a : MulAut (Original m V))
variable (ha : MonomialAction m V S a) (e : H ≃* Original m V)
variable (hF : ∀ h : H, e (derivedFrobenius F H hH h) = a (e h))
variable (decomposition : ∀ b : B, ∃ h : H, ∃ z : Subgroup.center B, b = (h : B) * z)

/-- The product action transported from actual original conjugation. -/
def productConjugation : fixedPoints F →* MulAut (∀ c, Factor m V S c) :=
  (MulAut.congr (rationalDecomposition F H hH m V S a ha e hF)).toMonoidHom.comp
    (originalAction F H decomposition)

/-- A geometric central decomposition computes a coordinate of actual
rational conjugation. The H-part need not itself be rational. -/
theorem originalAction_coordinate (b : fixedPoints F) (h : H)
    (z : Subgroup.center B) (hb : (b : B) = (h : B) * z)
    (x : rationalSubgroup F H) (c : C) :
    (rationalDecomposition F H hH m V S a ha e hF
      (originalAction F H decomposition b x) c).1 =
      e h (first m c) * (rationalDecomposition F H hH m V S a ha e hF x c).1 *
        (e h (first m c))⁻¹ := by
  have hx : (⟨(originalAction F H decomposition b x).1.1,
      (originalAction F H decomposition b x).2⟩ : H) =
      h * ⟨x.1.1, x.2⟩ * h⁻¹ := by
    apply Subtype.ext
    rw [originalAction_value, hb, conjugation_mul_central]
    rfl
  change e ⟨(originalAction F H decomposition b x).1.1,
    (originalAction F H decomposition b x).2⟩ (first m c) = _
  rw [hx]
  simp only [map_mul, map_inv, Pi.mul_apply, Pi.inv_apply, rationalDecomposition_value]

/-- The same coordinate computation after transporting to the product. -/
theorem productConjugation_coordinate (b : fixedPoints F) (h : H)
    (z : Subgroup.center B) (hb : (b : B) = (h : B) * z)
    (x : ∀ c, Factor m V S c) (c : C) :
    (productConjugation F H hH m V S a ha e hF decomposition b x c).1 =
      e h (first m c) * (x c).1 * (e h (first m c))⁻¹ := by
  change (rationalDecomposition F H hH m V S a ha e hF
    (originalAction F H decomposition b
      ((rationalDecomposition F H hH m V S a ha e hF).symm x)) c).1 = _
  have hx := originalAction_coordinate F H hH m V S a ha e hF decomposition
    b h z hb ((rationalDecomposition F H hH m V S a ha e hF).symm x) c
  simpa only [MulEquiv.apply_symm_apply] using hx

/-- Each output coordinate depends only on the corresponding input
coordinate; this is proved from geometric conjugation, not sourced. -/
theorem coordinate_depends_only (b : fixedPoints F) (c : C)
    (x y : ∀ d, Factor m V S d) (hxy : x c = y c) :
    productConjugation F H hH m V S a ha e hF decomposition b x c =
      productConjugation F H hH m V S a ha e hF decomposition b y c := by
  obtain ⟨h, z, hb⟩ := decomposition (b : B)
  apply Subtype.ext
  rw [productConjugation_coordinate F H hH m V S a ha e hF decomposition b h z hb,
    productConjugation_coordinate F H hH m V S a ha e hF decomposition b h z hb, hxy]

/-- Insert a factor into the fixed product, conjugate in the original
rational group, and evaluate the same factor. -/
def factorMap (b : fixedPoints F) (c : C) : Factor m V S c →* Factor m V S c :=
  (Pi.evalMonoidHom (fun c => ↥(Factor m V S c)) c).comp
    ((productConjugation F H hH m V S a ha e hF decomposition b).toMonoidHom.comp
      (singleFactor m V S c))

/-- Coordinate dependence identifies the full action with the factor map. -/
theorem productConjugation_factorMap (b : fixedPoints F)
    (x : ∀ c, Factor m V S c) (c : C) :
    productConjugation F H hH m V S a ha e hF decomposition b x c =
      factorMap F H hH m V S a ha e hF decomposition b c (x c) := by
  classical
  apply coordinate_depends_only F H hH m V S a ha e hF decomposition b c
  simp [singleFactor]

/-- The inverse is obtained from inverse ambient conjugation. -/
theorem factorMap_inverse (b : fixedPoints F) (c : C) (x : Factor m V S c) :
    factorMap F H hH m V S a ha e hF decomposition b⁻¹ c
      (factorMap F H hH m V S a ha e hF decomposition b c x) = x := by
  classical
  have hsingle : ∀ y : Factor m V S c, singleFactor m V S c y c = y := by
    intro y
    change Function.update (1 : ∀ d, Factor m V S d) c y c = y
    exact Function.update_self (β := fun d => ↥(Factor m V S d)) c y 1
  have h := productConjugation_factorMap F H hH m V S a ha e hF decomposition b⁻¹
    (productConjugation F H hH m V S a ha e hF decomposition b (singleFactor m V S c x)) c
  change (productConjugation F H hH m V S a ha e hF decomposition b⁻¹
      (productConjugation F H hH m V S a ha e hF decomposition b (singleFactor m V S c x))) c =
    factorMap F H hH m V S a ha e hF decomposition b⁻¹ c
      (factorMap F H hH m V S a ha e hF decomposition b c x) at h
  simpa only [map_inv, MulAut.inv_apply_self, hsingle] using h.symm

/-- The canonical automorphism on an actual rational component factor. -/
def factorAutomorphism (b : fixedPoints F) (c : C) : MulAut (Factor m V S c) where
  toFun := factorMap F H hH m V S a ha e hF decomposition b c
  invFun := factorMap F H hH m V S a ha e hF decomposition b⁻¹ c
  left_inv := factorMap_inverse F H hH m V S a ha e hF decomposition b c
  right_inv x := by
    simpa only [inv_inv] using factorMap_inverse F H hH m V S a ha e hF decomposition b⁻¹ c x
  map_mul' := (factorMap F H hH m V S a ha e hF decomposition b c).map_mul

/-- Actual rational factor conjugation as a homomorphism. -/
def factorAction (c : C) : fixedPoints F →* MulAut (Factor m V S c) where
  toFun b := factorAutomorphism F H hH m V S a ha e hF decomposition b c
  map_one' := by
    classical
    apply MulEquiv.ext
    intro x
    change productConjugation F H hH m V S a ha e hF decomposition 1
      (singleFactor m V S c x) c = x
    simp [singleFactor]
  map_mul' b d := by
    apply MulEquiv.ext
    intro x
    have h := productConjugation_factorMap F H hH m V S a ha e hF decomposition b
      (productConjugation F H hH m V S a ha e hF decomposition d (singleFactor m V S c x)) c
    change productConjugation F H hH m V S a ha e hF decomposition (b * d)
      (singleFactor m V S c x) c = _
    rw [map_mul]
    exact h

/-- The complete group square, with every action on both sides constructed
from actual conjugation. -/
theorem groupSquare (b : fixedPoints F) :
    MulAut.congr (rationalDecomposition F H hH m V S a ha e hF)
      (originalAction F H decomposition b) =
    coordinateMulAut (fun c => ↥(Factor m V S c)) (fun c => MulAut (Factor m V S c))
      (fun _ => MonoidHom.id _) (fun c => factorAction F H hH m V S a ha e hF decomposition c b) := by
  apply MulEquiv.ext
  intro x
  funext c
  exact productConjugation_factorMap F H hH m V S a ha e hF decomposition b x c

/-- The constructed automorphism fixes the actual factor inclusion square
inside the original geometric paired Levi. -/
theorem factorAction_value (c : C) (b : fixedPoints F) (x : Factor m V S c) :
    (factorEmbedding H m V S a ha e c
      (factorAction F H hH m V S a ha e hF decomposition c b x) : B) =
      (b : B) * (factorEmbedding H m V S a ha e c x : B) * (b : B)⁻¹ := by
  classical
  have hsingle : ∀ y : Factor m V S c, singleFactor m V S c y c = y := by
    intro y
    change Function.update (1 : ∀ d, Factor m V S d) c y c = y
    exact Function.update_self (β := fun d => ↥(Factor m V S d)) c y 1
  have hp : productConjugation F H hH m V S a ha e hF decomposition b
      (singleFactor m V S c x) =
      singleFactor m V S c (factorAction F H hH m V S a ha e hF decomposition c b x) := by
    funext d
    rw [productConjugation_factorMap]
    by_cases hdc : d = c
    · subst d
      rw [hsingle, hsingle]
      rfl
    · have hx : singleFactor m V S c x d = 1 := by simp [singleFactor, hdc]
      rw [hx, map_one]
      simp [singleFactor, hdc]
  have ho : originalAction F H decomposition b
      ((rationalDecomposition F H hH m V S a ha e hF).symm (singleFactor m V S c x)) =
      (rationalDecomposition F H hH m V S a ha e hF).symm
        (singleFactor m V S c (factorAction F H hH m V S a ha e hF decomposition c b x)) := by
    apply (rationalDecomposition F H hH m V S a ha e hF).injective
    rw [MulEquiv.apply_symm_apply]
    exact hp
  have hv := congrArg (fun y : rationalSubgroup F H => y.1.1) ho
  rw [originalAction_value] at hv
  exact hv.symm

end CoordinateAction

end ModularRep.PaperProofs.TypeBRegularLeviRationalAction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
