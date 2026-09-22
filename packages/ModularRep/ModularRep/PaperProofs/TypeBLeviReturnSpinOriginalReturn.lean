import ModularRep.PaperProofs.TypeBLeviReturnSpinOriginalCarrier
import ModularRep.PaperProofs.TypeBLeviReturnPowerSelection
import ModularRep.PaperProofs.TypeBLeviReturnPowerAutomorphism

/-!
# The positive return from the original field and component coordinates

Only the one-step geometric field dictionary is external: the same point
endomorphism, its component permutation and literal projection values, and
its value under the original FieldData map. Powers of the original finite
actor and the corrected local return are deductions. No normalized return
square, finite field-image membership or character fixation is a source.
The geometric component/pinning interpretation remains the standard E1/U
boundary of the original component presentation.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBLeviReturnSpinOriginalReturn

open TypeBRegularLeviRationalCarriers TypeBComponentCycleNormalization
open TypeBRegularLeviCharacterActionAdapter TypeBLeviRepresentativeCarriers
open TypeBLeviRepresentativeSelection TypeBLeviReturnSpinOriginalCarrier
open TypeBLeviReturnPowerFixedPoints TypeBLeviReturnPowerAutomorphism
open TypeBRegularLeviComponentPointSource TypeBLemma47LeviApplication

section CoordinatePowers

variable {I X Y : Type*} [Group X] [Group Y]

private theorem coordinate_power (projection : I → X →* Y)
    (T : Monoid.End X) (F0 : Monoid.End Y) (sigma : Equiv.Perm I)
    (oneStep : ∀ i x, projection (sigma i) (T x) = F0 (projection i x))
    (n : ℕ) (i : I) (x : X) :
    projection ((sigma ^ n) i) ((T ^ n) x) = (F0 ^ n) (projection i x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [pow_succ']
      change projection (sigma ((sigma ^ n) i)) (T ((T ^ n) x)) =
        F0 ((F0 ^ n) (projection i x))
      rw [oneStep, ih]

private theorem permutation_multiple (sigma : Equiv.Perm I) (u r : ℕ) (i : I)
    (period : (sigma ^ u) i = i) : (sigma ^ (u * r)) i = i := by
  rw [pow_mul]
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [pow_succ']
      change (sigma ^ u) (((sigma ^ u) ^ r) i) = i
      rw [ih, period]

/-- The correction acts trivially on the original defining fixed point.
Only one-step component naturality is used. -/
theorem corrected_coordinate (projection : I → X →* Y)
    (T : Monoid.End X) (F0 F : Monoid.End Y) (sigma : Equiv.Perm I)
    (oneStep : ∀ i x, projection (sigma i) (T x) = F0 (projection i x))
    (h u v q r : ℕ) (hF : F = F0 ^ h)
    (exponent : v + h * q = u * r) (i : I)
    (period : (sigma ^ u) i = i) (x : X) (fixed : (T ^ h) x = x) :
    projection i ((T ^ v) x) = (F ^ q) ((F0 ^ v) (projection i x)) := by
  have sigma_fixed : (sigma ^ (v + h * q)) i = i := by
    rw [exponent]
    exact permutation_multiple sigma u r i period
  have correction : (T ^ (h * q)) x = x :=
    multiple_power_fixed T h q ⟨x, fixed⟩
  have domain_value : (T ^ (v + h * q)) x = (T ^ v) x := by
    rw [pow_add]
    change (T ^ v) ((T ^ (h * q)) x) = (T ^ v) x
    rw [correction]
  have square := coordinate_power projection T F0 sigma oneStep (v + h * q) i x
  rw [sigma_fixed, domain_value] at square
  refine square.trans ?_
  rw [hF, ← pow_mul]
  change (F0 ^ (v + h * q)) (projection i x) =
    (F0 ^ (h * q) * F0 ^ v) (projection i x)
  rw [← pow_add, Nat.add_comm]

end CoordinatePowers

section Original

variable {A : Type} [Group A] {Frob : MulAut A} {Lbar : Subgroup A}
variable [Finite (fixedPoints Frob.toMonoidHom)]
variable {E : Type} [Group E] [Finite E] [IsCyclic E]
variable {C : Type} [Fintype C] {m : C → ℕ}
variable {leviStable : Lbar.map Frob.toMonoidHom = Lbar}
variable {k K : Type} [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable (geometry : PrimalData Frob Lbar leviStable m)
variable (field : FieldData Frob Lbar E)

/-- Projection to the actual embedded geometric component. -/
def componentProjection (i : Index geometry.geometricLength) :
    TypeBLeviRepresentativeGeometry.derivedInside Lbar →* pairedLevi Lbar where
  toFun x := (geometry.components.coordinates x i).1.1
  map_one' := by
    change (geometry.components.coordinates 1 i).1.1 = 1
    rw [map_one]
    rfl
  map_mul' x y := by
    change (geometry.components.coordinates (x * y) i).1.1 =
      (geometry.components.coordinates x i).1.1 *
        (geometry.components.coordinates y i).1.1
    rw [map_mul]
    rfl

/-- One-step field interpretation on the same point carrier and component chart.
These fields contain no local-return, standard-model or character conclusion. -/
structure OriginalFieldData where
  F0 : Monoid.End (pairedLevi Lbar)
  derived_stable : ∀ x ∈ TypeBLeviRepresentativeGeometry.derivedInside Lbar,
    F0 x ∈ TypeBLeviRepresentativeGeometry.derivedInside Lbar
  permutation : Equiv.Perm (Index geometry.geometricLength)
  component_value : ∀ i x,
    componentProjection geometry (permutation i)
      (componentEnd F0 (TypeBLeviRepresentativeGeometry.derivedInside Lbar)
        derived_stable x) = F0 (componentProjection geometry i x)
  ambient_value : ∀ x : pairedLevi Lbar, (F0 x).1 = field.sigma x.1

variable (points : OriginalFieldData geometry field)

/-- The same original N element viewed in the geometric derived subgroup. -/
def geometricPoint (chart : PrimalData Frob Lbar leviStable m) (x : N Frob Lbar) :
    TypeBLeviRepresentativeGeometry.derivedInside Lbar :=
  let y := (TypeBLeviRepresentativeGeometry.rationalDerivedEquiv Frob Lbar leviStable).symm x
  ⟨y.1.1, y.2⟩

/-- Restrict the existing finite field action; no actor on geometric points is supplied. -/
abbrev originalFieldAction : E →* MulAut (N Frob Lbar) :=
  restrictAutomorphismHom (N Frob Lbar) field.fieldOnGamma field.N_stable

abbrev derivedField : Monoid.End (TypeBLeviRepresentativeGeometry.derivedInside Lbar) :=
  componentEnd points.F0 (TypeBLeviRepresentativeGeometry.derivedInside Lbar)
    points.derived_stable

/-- Original finite-generator values agree with the retained geometric map. -/
theorem geometricPoint_generator (x : N Frob Lbar) :
    geometricPoint geometry (originalFieldAction field field.generator x) =
      derivedField geometry field points (geometricPoint geometry x) := by
  apply Subtype.ext
  apply Subtype.ext
  change (field.fieldPoints field.generator x.1.1).1 =
    (points.F0 (geometricPoint geometry x).1).1
  rw [points.ambient_value, field.generatorValue]
  rfl

/-- Every finite field power is interpreted through the same point endomorphism. -/
theorem geometricPoint_field_power (t : ℕ) (x : N Frob Lbar) :
    geometricPoint geometry (originalFieldAction field (field.generator ^ t) x) =
      (derivedField geometry field points ^ t) (geometricPoint geometry x) := by
  induction t with
  | zero =>
      rw [pow_zero, map_one]
      rfl
  | succ t ih =>
      rw [pow_succ', map_mul, pow_succ']
      change geometricPoint geometry
        (originalFieldAction field field.generator
          (originalFieldAction field (field.generator ^ t) x)) =
        derivedField geometry field points ((derivedField geometry field points ^ t) (geometricPoint geometry x))
      rw [geometricPoint_generator geometry field points, ih]

/-- The defining power fixes this original geometric point. -/
theorem geometricPoint_fixed (h : ℕ)
    (hF : TypeBLeviRepresentativeGeometry.pairedFrobenius Frob Lbar leviStable =
      points.F0 ^ h) (x : N Frob Lbar) :
    (derivedField geometry field points ^ h) (geometricPoint geometry x) = geometricPoint geometry x := by
  apply Subtype.ext
  rw [componentEnd_pow_value, ← hF]
  exact ((TypeBLeviRepresentativeGeometry.rationalDerivedEquiv
    Frob Lbar leviStable).symm x).1.2

variable {root : PrimeRegularRootEmbedding 2 k K (L0 Frob.toMonoidHom Lbar)}
variable {theta0 : IBr (rootN Frob Lbar root)}
variable (presentation : Presentation geometry field root theta0) (c : C)

/-- The positive local generator is evaluated through the original product
and the actual power of the prescribed finite field generator. -/
theorem localGenerator_product_value (a : ℕ)
    (tau_value : presentation.tau.1 = field.generator ^ a) (x : N Frob Lbar) :
    presentation.localH c (presentation.localGenerator c)
        (geometry.componentProduct x (first m c)) =
      geometry.componentProduct
        (originalFieldAction field (field.generator ^ (a * (m c + 1))) x) (first m c) := by
  have value := TypeBComponentReturnRestriction.original_return_coordinate
    m geometry.factor presentation.SH
    ((geometry.productField field).comp
      (geometry.orbitStabilizer root field theta0).subtype)
    presentation.tau presentation.hH c (presentation.localGenerator c)
    (geometry.componentProduct x)
  change (geometry.productField field (presentation.tau.1 ^ (m c + 1))
    (geometry.componentProduct x)) (first m c) = _ at value
  rw [tau_value, ← pow_mul] at value
  have product_value :
      geometry.productField field (field.generator ^ (a * (m c + 1)))
          (geometry.componentProduct x) =
        geometry.componentProduct
          (originalFieldAction field (field.generator ^ (a * (m c + 1))) x) := by
    change geometry.componentProduct
      (originalFieldAction field (field.generator ^ (a * (m c + 1)))
        (geometry.componentProduct.symm (geometry.componentProduct x))) = _
    rw [MulEquiv.symm_apply_apply]
  rw [product_value] at value
  exact value.symm

/-- The original positive local return has the corrected ambient value.
The only geometric input is the one-step component/field dictionary above. -/
theorem original_positive_return_value (a h u q r : ℕ)
    (tau_value : presentation.tau.1 = field.generator ^ a)
    (hF : TypeBLeviRepresentativeGeometry.pairedFrobenius Frob Lbar leviStable =
      points.F0 ^ h)
    (return_exponent : a * (m c + 1) + h * q = u * r)
    (period : (points.permutation ^ u)
      (first geometry.geometricLength (first m c)) =
        first geometry.geometricLength (first m c))
    (x : Base m geometry.factor c) :
    (originalBaseEquivRational Frob Lbar leviStable m geometry c
      (presentation.localH c (presentation.localGenerator c) x)).1.1 =
    (pairedFrobeniusEnd Frob Lbar leviStable ^ q)
      ((points.F0 ^ (a * (m c + 1)))
        (originalBaseEquivRational Frob Lbar leviStable m geometry c x).1.1) := by
  obtain ⟨g, hg⟩ := TypeBReturnCoordinateAction.coordinate_surjective
    geometry.factor (first m c) x
  obtain ⟨y, rfl⟩ := geometry.componentProduct.surjective g
  subst x
  rw [localGenerator_product_value geometry field presentation c a tau_value,
    originalBaseEquivRational_componentProduct_value,
    originalBaseEquivRational_componentProduct_value]
  change componentProjection geometry (first geometry.geometricLength (first m c))
      (geometricPoint geometry
        (originalFieldAction field (field.generator ^ (a * (m c + 1))) y)) =
    (pairedFrobeniusEnd Frob Lbar leviStable ^ q)
      ((points.F0 ^ (a * (m c + 1)))
        (componentProjection geometry (first geometry.geometricLength (first m c))
          (geometricPoint geometry y)))
  rw [geometricPoint_field_power geometry field points]
  exact corrected_coordinate (componentProjection geometry)
    (derivedField geometry field points) points.F0
    (TypeBLeviRepresentativeGeometry.pairedFrobenius Frob Lbar leviStable)
    points.permutation points.component_value h u (a * (m c + 1)) q r
    hF return_exponent (first geometry.geometricLength (first m c)) period
    (geometricPoint geometry y) (geometricPoint_fixed geometry field points h hF y)

end Original

end ModularRep.PaperProofs.TypeBLeviReturnSpinOriginalReturn


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
