import ModularRep.PaperProofs.TypeBRegularLeviSupportedLift
import ModularRep.PaperProofs.TypeBRegularLeviComponentFixedPoints

/-!
# Actual orbit-supported projections in the geometric component product

The projections in the Lang-correction argument are constructed here by
keeping the coordinates of one actual Frobenius cycle and replacing all
other coordinates by the identity. Their Frobenius, centre and conjugation
laws are deductions. The rational factor embedding is the actual inverse
fixed-product equivalence, hence has the Frobenius-diagonal formula from
the component fixed-point theorem.

Remaining displayed source data are the original geometric decomposition,
the identification of H with its actual geometric components, its original
Frobenius square and monomial cycle equations, central Lang, and the exact
conjugation square of the rational action. The final regular-Levi wrapper
must bind B to the paired geometric Levi and H to its actual derived group;
this file does not assert the full numbered lemma or any later condition.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBRegularLeviProductProjection

open TypeBComponentCycleNormalization
open TypeBRegularLeviRationalCarriers
open TypeBRegularLeviComponentFixedPoints
open TypeBRegularLeviSupportedLift

section Product

variable {C : Type} (m : C → ℕ) (V : Index m → Type)
variable [∀ i, Group (V i)]

local instance : DecidableEq C := Classical.decEq C

/-- The actual geometric projection onto one entire Frobenius cycle. -/
def cycleProjection (c : C) : Original m V →* Original m V := by
  classical
  exact
    { toFun := fun g i => if i.1 = c then g i else 1
      map_one' := by funext i; split_ifs <;> rfl
      map_mul' := by
        intro x y
        funext i
        by_cases hi : i.1 = c <;> simp [hi] }

@[simp]
theorem cycleProjection_value (c : C) (g : Original m V) (i : Index m) :
    cycleProjection m V c g i = if i.1 = c then g i else 1 := by
  classical
  rfl

variable (S : CycleCoordinates m V) (a : MulAut (Original m V))
variable (ha : MonomialAction m V S a)

include ha in
/-- The mask is Frobenius-equivariant because its support is a full cycle
of the original monomial action. -/
theorem cycleProjection_frobenius (c : C) (g : Original m V) :
    cycleProjection m V c (a g) = a (cycleProjection m V c g) := by
  classical
  funext i
  rcases i with ⟨d, j⟩
  refine Fin.lastCases ?_ (fun j => ?_) j
  · change (if d = c then a g (last m d) else 1) =
      a (cycleProjection m V c g) (last m d)
    rw [ha.wrap, ha.wrap]
    by_cases hdc : d = c <;> simp [hdc]
  · change (if d = c then a g ⟨d, j.castSucc⟩ else 1) =
      a (cycleProjection m V c g) ⟨d, j.castSucc⟩
    rw [ha.successor, ha.successor]
    by_cases hdc : d = c <;> simp [hdc]

/-- The literal rational factor is fixed by the actual computed full
return, whose equality with the original full Frobenius power is proved
in `factorReturn_power_value`. -/
abbrev Factor (c : C) := fixedPoints (fullReturn m V S c).toMonoidHom

/-- Insert one rational factor into the actual product of return-fixed
factors. No lift from an inner automorphism image is involved. -/
def singleFactor (c : C) : Factor m V S c →* (∀ d, Factor m V S d) := by
  classical
  exact
    { toFun := fun x => Function.update 1 c x
      map_one' := by funext d; by_cases hdc : d = c <;> simp [hdc]
      map_mul' := by
        intro x y
        funext d
        by_cases hdc : d = c
        · subst d; simp
        · simp [hdc] }

theorem singleFactor_injective (c : C) :
    Function.Injective (singleFactor m V S c) := by
  classical
  intro x y hxy
  have h := congrFun hxy c
  simpa [singleFactor] using h

end Product

section Geometry

variable {B C : Type} [Group B] (F : B →* B)
variable (H : Subgroup B) (hH : ∀ h ∈ H, F h ∈ H)
variable (m : C → ℕ) (V : Index m → Type) [∀ i, Group (V i)]
variable (S : CycleCoordinates m V) (a : MulAut (Original m V))
variable (ha : MonomialAction m V S a)
variable (e : H ≃* Original m V)

/-- The actual orbit-supported projection transported to the original
geometric derived group through its displayed component identification. -/
def geometricProjection (c : C) : H →* H :=
  e.symm.toMonoidHom.comp ((cycleProjection m V c).comp e.toMonoidHom)

@[simp]
theorem geometricProjection_value (c : C) (h : H) :
    e (geometricProjection H m V e c h) = cycleProjection m V c (e h) :=
  e.apply_symm_apply _

include ha in
/-- The original Frobenius square makes the constructed projections
commute with the same restricted Frobenius. -/
theorem geometricProjection_frobenius
    (hF : ∀ h : H, e (derivedFrobenius F H hH h) = a (e h))
    (c : C) (h : H) :
    geometricProjection H m V e c (derivedFrobenius F H hH h) =
      derivedFrobenius F H hH (geometricProjection H m V e c h) := by
  apply e.injective
  rw [geometricProjection_value, hF, hF, geometricProjection_value]
  exact cycleProjection_frobenius m V S a ha c (e h)

/-- The rational factor is embedded by the full Frobenius diagonal, namely
the inverse of the proved fixed-product equivalence, followed by the
original geometric component identification. -/
def factorEmbedding (c : C) : Factor m V S c →* H :=
  e.symm.toMonoidHom.comp
    ((fixedPoints a.toMonoidHom).subtype.comp
      ((fixedProductEquiv m V S a ha).symm.toMonoidHom.comp (singleFactor m V S c)))

@[simp]
theorem factorEmbedding_geometric (c : C) (x : Factor m V S c) :
    e (factorEmbedding H m V S a ha e c x) =
      ((fixedProductEquiv m V S a ha).symm (singleFactor m V S c x)).1 :=
  e.apply_symm_apply _

theorem factorEmbedding_injective (c : C) :
    Function.Injective (factorEmbedding H m V S a ha e c) := by
  intro x y hxy
  apply singleFactor_injective m V S c
  apply (fixedProductEquiv m V S a ha).symm.injective
  apply Subtype.ext
  have h := congrArg e hxy
  simpa only [factorEmbedding_geometric] using h

/-- The constructed inclusion is rational for the original Frobenius on
the original subgroup, not merely for a named factor automorphism. -/
theorem factorEmbedding_rational
    (hF : ∀ h : H, e (derivedFrobenius F H hH h) = a (e h))
    (c : C) (x : Factor m V S c) :
    F (factorEmbedding H m V S a ha e c x : B) =
      (factorEmbedding H m V S a ha e c x : B) := by
  have hh : derivedFrobenius F H hH (factorEmbedding H m V S a ha e c x) =
      factorEmbedding H m V S a ha e c x := by
    apply e.injective
    simp only [hF, factorEmbedding_geometric]
    exact ((fixedProductEquiv m V S a ha).symm (singleFactor m V S c x)).property
  exact congrArg Subtype.val hh

/-- The Frobenius-diagonal factor embedding has identity coordinates on
every other actual cycle. -/
theorem factorEmbedding_off_cycle (c : C) (x : Factor m V S c)
    (i : Index m) (hic : i.1 ≠ c) :
    e (factorEmbedding H m V S a ha e c x) i = 1 := by
  classical
  rw [factorEmbedding_geometric, fixedProductEquiv_symm_value]
  simp [singleFactor, hic]

/-- Geometric central decomposition carries central elements of H into
the actual centre of B. This does not assert a rational decomposition. -/
theorem centre_of_derived_central
    (decomposition : ∀ b : B, ∃ h : H, ∃ z : Subgroup.center B, b = (h : B) * z)
    (h : H) (hh : h ∈ Subgroup.center H) : (h : B) ∈ Subgroup.center B := by
  apply Subgroup.mem_center_iff.mpr
  intro b
  obtain ⟨k, z, rfl⟩ := decomposition b
  have hk : (k : B) * h = (h : B) * k :=
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hh k)
  have hz : (z : B) * h = (h : B) * z :=
    (Subgroup.mem_center_iff.mp z.property (h : B)).symm
  calc
    ((k : B) * z) * h = (k : B) * ((z : B) * h) := mul_assoc _ _ _
    _ = (k : B) * ((h : B) * z) := by rw [hz]
    _ = ((k : B) * h) * z := (mul_assoc _ _ _).symm
    _ = ((h : B) * k) * z := by rw [hk]
    _ = (h : B) * ((k : B) * z) := mul_assoc _ _ _

/-- Centre preservation is proved coordinatewise, then transported to B
using geometric central decomposition. It is not a projection source law. -/
theorem geometricProjection_centre
    (decomposition : ∀ b : B, ∃ h : H, ∃ z : Subgroup.center B, b = (h : B) * z)
    (c : C) (h : H) (hh : (h : B) ∈ Subgroup.center B) :
    (geometricProjection H m V e c h : B) ∈ Subgroup.center B := by
  classical
  apply centre_of_derived_central H decomposition
  apply Subgroup.mem_center_iff.mpr
  intro k
  apply e.injective
  have hk : k * h = h * k := by
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hh (k : B)
  have hp := congrArg e hk
  simp only [map_mul] at hp
  simp only [map_mul, geometricProjection_value]
  funext i
  have hi := congrFun hp i
  by_cases hic : i.1 = c
  · simpa [cycleProjection_value, hic] using hi
  · simp [cycleProjection_value, hic]

/-- On its selected rational factor, the constructed projected H-part
has exactly the original H-part's conjugation. -/
theorem geometricProjection_selected (c : C) (h : H) (x : Factor m V S c) :
    (geometricProjection H m V e c h : B) * (factorEmbedding H m V S a ha e c x : B) *
      (geometricProjection H m V e c h : B)⁻¹ =
    (h : B) * (factorEmbedding H m V S a ha e c x : B) * (h : B)⁻¹ := by
  classical
  have heq : geometricProjection H m V e c h * factorEmbedding H m V S a ha e c x *
      (geometricProjection H m V e c h)⁻¹ =
      h * factorEmbedding H m V S a ha e c x * h⁻¹ := by
    apply e.injective
    simp only [map_mul, map_inv, geometricProjection_value]
    funext i
    by_cases hic : i.1 = c
    · simp only [Pi.mul_apply, Pi.inv_apply, cycleProjection_value, if_pos hic]
    · have hx := factorEmbedding_off_cycle H m V S a ha e c x i hic
      simp only [Pi.mul_apply, Pi.inv_apply, cycleProjection_value, if_neg hic,
        hx, mul_one, one_mul, inv_one, mul_inv_cancel]
  exact congrArg Subtype.val heq

/-- On every other rational factor, the projected H-part centralizes the
actual Frobenius-diagonal embedding. -/
theorem geometricProjection_other (c d : C) (hdc : d ≠ c)
    (h : H) (x : Factor m V S d) :
    (geometricProjection H m V e c h : B) * (factorEmbedding H m V S a ha e d x : B) *
      (geometricProjection H m V e c h : B)⁻¹ =
      (factorEmbedding H m V S a ha e d x : B) := by
  classical
  have heq : geometricProjection H m V e c h * factorEmbedding H m V S a ha e d x *
      (geometricProjection H m V e c h)⁻¹ = factorEmbedding H m V S a ha e d x := by
    apply e.injective
    simp only [map_mul, map_inv, geometricProjection_value]
    funext i
    by_cases hic : i.1 = c
    · have hid : i.1 ≠ d := fun hid => hdc (hid.symm.trans hic)
      have hx := factorEmbedding_off_cycle H m V S a ha e d x i hid
      simp only [Pi.mul_apply, Pi.inv_apply, cycleProjection_value, if_pos hic,
        hx, mul_one, one_mul, inv_one, mul_inv_cancel]
    · simp only [Pi.mul_apply, Pi.inv_apply, cycleProjection_value, if_neg hic,
        one_mul, mul_one, inv_one]
  exact congrArg Subtype.val heq

/-- The existing Lang-lift input is populated with the actual constructed
projections and Frobenius-diagonal inclusions. Only the original geometric
identification/Frobenius data and literal rational conjugation square remain. -/
def projectionData
    (hF : ∀ h : H, e (derivedFrobenius F H hH h) = a (e h))
    (decomposition : ∀ b : B, ∃ h : H, ∃ z : Subgroup.center B, b = (h : B) * z)
    (action : ∀ c, fixedPoints F →* MulAut (Factor m V S c))
    (action_value : ∀ c (b : fixedPoints F) (x : Factor m V S c),
      (factorEmbedding H m V S a ha e c (action c b x) : B) =
        (b : B) * (factorEmbedding H m V S a ha e c x : B) * (b : B)⁻¹) :
    ProjectionData F H hH (fun c => ↥(Factor m V S c)) where
  decomposition := decomposition
  factorEmbedding := factorEmbedding H m V S a ha e
  factorEmbedding_injective := factorEmbedding_injective H m V S a ha e
  factorEmbedding_rational := factorEmbedding_rational F H hH m V S a ha e hF
  project := geometricProjection H m V e
  project_frobenius := geometricProjection_frobenius F H hH m V S a ha e hF
  project_centre := geometricProjection_centre H m V e decomposition
  project_selected := geometricProjection_selected H m V S a ha e
  project_other := geometricProjection_other H m V S a ha e
  factorAction := action
  factorAction_value := action_value

/-- Product-image surjectivity with every geometric projection law now
constructed from the actual component product. No supported rational lift,
projection law, action-surjectivity or orbit assertion is a source input. -/
theorem productAction_surjective [Finite C]
    (hF : ∀ h : H, e (derivedFrobenius F H hH h) = a (e h))
    (decomposition : ∀ b : B, ∃ h : H, ∃ z : Subgroup.center B, b = (h : B) * z)
    (action : ∀ c, fixedPoints F →* MulAut (Factor m V S c))
    (action_value : ∀ c (b : fixedPoints F) (x : Factor m V S c),
      (factorEmbedding H m V S a ha e c (action c b x) : B) =
        (b : B) * (factorEmbedding H m V S a ha e c x : B) * (b : B)⁻¹)
    (lang : CentralLangSource F) :
    Function.Surjective
      (TypeBRegularLeviSupportedLift.productAction F H hH (fun c => ↥(Factor m V S c))
        (projectionData F H hH m V S a ha e hF decomposition action action_value)) :=
  TypeBRegularLeviSupportedLift.productAction_surjective F H hH (fun c => ↥(Factor m V S c))
    (projectionData F H hH m V S a ha e hF decomposition action action_value) lang

end Geometry

end ModularRep.PaperProofs.TypeBRegularLeviProductProjection


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
