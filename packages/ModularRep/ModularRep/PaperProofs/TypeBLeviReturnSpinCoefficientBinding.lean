import ModularRep.PaperProofs.TypeBLeviReturnPowerModel

/-!
# The literal Spin coefficient model for the common return Frobenius

The finite and geometric groups are the norm kernels in the specified split
Clifford algebras. The existing fixed-point source supplies their actual
coefficient inclusion, norm compatibility and fixed range. A common
geometric endomorphism is calibrated on scalar and vector generators.
Clifford induction derives both its coefficient square and its defining
power; neither square is a source field.

The finite exponent is explicitly `f = b*s`. In the specified application
with `F0 = phi^c`, the common prime-field exponent is `b = c*u`.
The return identity `u*s = h*d` then gives `f = (c*h)*d`.
No identification `b = u` is made without the special assumption `c = 1`.

The narrow standard boundaries are the existing Clifford fixed-range and
field-action sources and the displayed scalar/vector calibration of the
same common Frobenius. See FLZ type B, Section 2.5, pp. 539--540 and
Section 3.1, p. 541; Geck--Malle, Definition 1.4.1, pp. 40--41 and
Section 1.4.5, p. 42. Their specified inhabitants remain explicit.
The algebraic closure belongs to the defining-characteristic source only.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBLeviReturnSpinCoefficientBinding

open TypeBCliffordCarriers TypeBRegularLeviRationalCarriers
open TypeBLeviReturnPowerFixedPoints TypeBLeviReturnPowerAutomorphism
open TypeBLeviReturnPowerModel

/-- The original field-generator exponent is retained in the return arithmetic. -/
theorem calibrated_exponent (c u h d s : ℕ) (period : u * s = h * d) :
    (c * u) * s = (c * h) * d := by
  rw [Nat.mul_assoc, period, ← Nat.mul_assoc]

private theorem clifford_ringHom_ext {n : ℕ} {F R : Type*}
    [Field F] [Ring R] (T V : Clifford n F →+* R)
    (scalars : ∀ a, T (algebraMap F (Clifford n F) a) =
      V (algebraMap F (Clifford n F) a))
    (vectors : ∀ v, T (CliffordAlgebra.ι (splitForm n F) v) =
      V (CliffordAlgebra.ι (splitForm n F) v)) : T = V := by
  apply RingHom.ext
  intro x
  induction x using CliffordAlgebra.induction with
  | algebraMap a => exact scalars a
  | ι v => exact vectors v
  | mul x y hx hy => simp only [map_mul, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem scalar_power {n : ℕ} {F : Type*} [Field F]
    (T : Clifford n F →+* Clifford n F) (q : ℕ)
    (scalars : ∀ a, T (algebraMap F (Clifford n F) a) =
      algebraMap F (Clifford n F) (a ^ q))
    (t : ℕ) (a : F) :
    (T ^ t) (algebraMap F (Clifford n F) a) =
      algebraMap F (Clifford n F) (a ^ (q ^ t)) := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [pow_succ']
      change T ((T ^ t) (algebraMap F (Clifford n F) a)) = _
      rw [ih, scalars]
      simp only [pow_succ, pow_mul]

private theorem vector_power {n : ℕ} {F : Type*} [Field F]
    (T : Clifford n F →+* Clifford n F) (q : ℕ)
    (vectors : ∀ v, T (CliffordAlgebra.ι (splitForm n F) v) =
      CliffordAlgebra.ι (splitForm n F) (fun j ↦ v j ^ q))
    (t : ℕ) (v : Vector n F) :
    (T ^ t) (CliffordAlgebra.ι (splitForm n F) v) =
      CliffordAlgebra.ι (splitForm n F) (fun j ↦ v j ^ (q ^ t)) := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [pow_succ']
      change T ((T ^ t) (CliffordAlgebra.ι (splitForm n F) v)) = _
      rw [ih, vectors]
      congr 1
      funext j
      simp only [pow_succ, pow_mul]

private theorem pointwise_power_square {G H : Type*} [Group G] [Group H]
    (T : Monoid.End H) (a : MulAut G) (e : G → H)
    (square : ∀ g, T (e g) = e (a g)) (r : ℕ) (g : G) :
    (T ^ r) (e g) = e ((a ^ r) g) := by
  induction r with
  | zero => rfl
  | succ r ih =>
      calc
        (T ^ (r + 1)) (e g) = T ((T ^ r) (e g)) := by
          rw [pow_succ']
          rfl
        _ = T (e ((a ^ r) g)) := congrArg (fun x : H ↦ T x) ih
        _ = e (a ((a ^ r) g)) := square _
        _ = e ((a ^ (r + 1)) g) := by
          rw [pow_succ']
          rfl

section Common

variable {n p b : ℕ} {A : Type} [Field A] {Nbar : NormSource n A}
variable (Φ : Monoid.End (Spin n A Nbar))

/-- Generator calibration for the same common geometric Frobenius.
The ring endomorphism and its value on the actual norm kernel are retained;
no finite return automorphism or finite-model equivalence is supplied. -/
structure CommonFrobeniusData where
  algebraEnd : Clifford n A →+* Clifford n A
  on_scalar : ∀ a : A,
    algebraEnd (algebraMap A (Clifford n A) a) =
      algebraMap A (Clifford n A) (a ^ (p ^ b))
  on_vector : ∀ v : Vector n A,
    algebraEnd (CliffordAlgebra.ι (splitForm n A) v) =
      CliffordAlgebra.ι (splitForm n A) (fun j ↦ v j ^ (p ^ b))
  group_value : ∀ g : Spin n A Nbar,
    toClifford n A (Φ g).1 = algebraEnd (toClifford n A g.1)

variable (data : CommonFrobeniusData (p := p) (b := b) Φ)

theorem common_power_value (t : ℕ) (g : Spin n A Nbar) :
    toClifford n A ((Φ ^ t) g).1 =
      (data.algebraEnd ^ t) (toClifford n A g.1) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [pow_succ']
      change toClifford n A (Φ ((Φ ^ t) g)).1 =
        data.algebraEnd ((data.algebraEnd ^ t) (toClifford n A g.1))
      rw [data.group_value, ih]

end Common

section Coefficients

variable {n p f b s : ℕ} {F A : Type}
variable [Field F] [Finite F] [CharP F p] [Field A] [Algebra F A]
variable {N : NormSource n F} {Nbar : NormSource n A}
variable {Frob : MulAut (SpecialClifford n A)}
variable (source : CliffordFixedPointSource n p f F A N Nbar Frob)
variable (fs : FieldActionSource n F p f source.parameters N)
variable (Φ : Monoid.End (Spin n A Nbar))
variable (data : CommonFrobeniusData (p := p) (b := b) Φ)
variable (exponent : f = b * s)

/-- The coefficient square is derived on Clifford generators. -/
theorem coefficient_square_ring :
    data.algebraEnd.comp source.coefficientMap =
      source.coefficientMap.comp (fs.algebraFrobenius.toRingHom ^ b) := by
  apply clifford_ringHom_ext
  · intro a
    change data.algebraEnd (source.coefficientMap (algebraMap F (Clifford n F) a)) =
      source.coefficientMap
        ((fs.algebraFrobenius.toRingHom ^ b) (algebraMap F (Clifford n F) a))
    rw [source.coefficient_scalar, data.on_scalar,
      scalar_power fs.algebraFrobenius.toRingHom p fs.on_scalar,
      source.coefficient_scalar]
    exact congrArg (algebraMap A (Clifford n A))
      (map_pow (algebraMap F A) a (p ^ b)).symm
  · intro v
    change data.algebraEnd
      (source.coefficientMap (CliffordAlgebra.ι (splitForm n F) v)) =
      source.coefficientMap
        ((fs.algebraFrobenius.toRingHom ^ b) (CliffordAlgebra.ι (splitForm n F) v))
    rw [source.coefficient_vector, data.on_vector,
      vector_power fs.algebraFrobenius.toRingHom p fs.on_vector,
      source.coefficient_vector]
    congr 1
    funext j
    exact (map_pow (algebraMap F A) (v j) (p ^ b)).symm

include exponent in
/-- The defining Frobenius is the calibrated power of the common ring map. -/
theorem defining_algebra :
    data.algebraEnd ^ s = source.algebraFrobenius.toRingHom := by
  apply clifford_ringHom_ext
  · intro a
    rw [scalar_power data.algebraEnd (p ^ b) data.on_scalar]
    change algebraMap A (Clifford n A) (a ^ ((p ^ b) ^ s)) =
      source.algebraFrobenius (algebraMap A (Clifford n A) a)
    rw [source.frobenius_scalar, source.parameters.cardinality, exponent, pow_mul]
  · intro v
    rw [vector_power data.algebraEnd (p ^ b) data.on_vector]
    change CliffordAlgebra.ι (splitForm n A) (fun j ↦ v j ^ ((p ^ b) ^ s)) =
      source.algebraFrobenius (CliffordAlgebra.ι (splitForm n A) v)
    rw [source.frobenius_vector, source.parameters.cardinality, exponent, pow_mul]

include source data exponent in
/-- The defining square on the actual norm kernel follows by injectivity. -/
theorem defining_value (g : Spin n A Nbar) :
    Frob g.1 = ((Φ ^ s) g).1 := by
  apply toClifford_injective n A
  rw [source.frobenius_value, common_power_value Φ data,
    defining_algebra source Φ data exponent]
  rfl

/-- Reorder the literal fixed-point and norm-kernel subtypes. -/
def definingSpinEquiv :
    fixedPoints (Φ ^ s) ≃*
      rationalSubgroup Frob.toMonoidHom (SpinSubgroup n A Nbar) where
  toFun x := ⟨⟨x.1.1, by
    change Frob x.1.1 = x.1.1
    rw [defining_value source Φ data exponent x.1]
    exact congrArg Subtype.val x.2⟩, x.1.2⟩
  invFun y := ⟨⟨y.1.1, y.2⟩, by
    apply Subtype.ext
    change ((Φ ^ s) ⟨y.1.1, y.2⟩).1 = y.1.1
    rw [← defining_value source Φ data exponent ⟨y.1.1, y.2⟩]
    exact y.1.2⟩
  left_inv x := rfl
  right_inv y := rfl
  map_mul' x y := rfl

/-- The actual finite Spin group, with the same coefficient and norm maps. -/
def coefficientEquiv :
    Spin n F N ≃* fixedPoints (Φ ^ s) :=
  (finiteSpinEquiv n p f F A N Nbar Frob source).trans
    (definingSpinEquiv source Φ data exponent).symm

@[simp] theorem coefficientEquiv_value (g : Spin n F N) :
    (coefficientEquiv source Φ data exponent g).1.1 = source.inclusion g.1 := rfl

theorem coefficientEquiv_clifford_value (g : Spin n F N) :
    toClifford n A (coefficientEquiv source Φ data exponent g).1.1 =
      source.coefficientMap (toClifford n F g.1) :=
  source.inclusion_value g.1

theorem coefficientEquiv_symm_value (x : fixedPoints (Φ ^ s)) :
    source.inclusion ((coefficientEquiv source Φ data exponent).symm x).1 = x.1.1 := by
  have value := congrArg (fun y : fixedPoints (Φ ^ s) ↦ y.1.1)
    ((coefficientEquiv source Φ data exponent).apply_symm_apply x)
  simpa only [coefficientEquiv_value] using value

/-- Prime Frobenius powers use the existing full field action. -/
theorem field_power_clifford_value (t : ℕ) (g : SpecialClifford n F) :
    toClifford n F (fs.action (fieldGenerator f ^ t) g) =
      (fs.algebraFrobenius.toRingHom ^ t) (toClifford n F g) := by
  induction t with
  | zero =>
      rw [pow_zero, map_one]
      rfl
  | succ t ih =>
      rw [pow_succ', map_mul, pow_succ']
      change toClifford n F
        (fs.action (fieldGenerator f) (fs.action (fieldGenerator f ^ t) g)) =
        fs.algebraFrobenius ((fs.algebraFrobenius.toRingHom ^ t) (toClifford n F g))
      rw [fs.action_generator, ih]

/-- One common geometric Frobenius is the computed finite field power. -/
theorem coefficient_generator_square (g : Spin n F N) :
    Φ (coefficientEquiv source Φ data exponent g).1 =
      (coefficientEquiv source Φ data exponent
        (spinFieldAction n F fs (fieldGenerator f ^ b) g)).1 := by
  apply Subtype.ext
  apply toClifford_injective n A
  rw [data.group_value, coefficientEquiv_clifford_value,
    coefficientEquiv_clifford_value]
  have square := DFunLike.congr_fun (coefficient_square_ring source fs Φ data)
    (toClifford n F g.1)
  change data.algebraEnd (source.coefficientMap (toClifford n F g.1)) =
    source.coefficientMap
      (toClifford n F (fs.action (fieldGenerator f ^ b) g.1))
  rw [field_power_clifford_value source fs]
  exact square

/-- Iterating the same square gives the positive return exponent `b*r`. -/
theorem coefficient_power_square (r : ℕ) (g : Spin n F N) :
    (Φ ^ r) (coefficientEquiv source Φ data exponent g).1 =
      (coefficientEquiv source Φ data exponent
        (spinFieldAction n F fs (fieldGenerator f ^ (b * r)) g)).1 := by
  let e : Spin n F N → Spin n A Nbar :=
    fun x ↦ (coefficientEquiv source Φ data exponent x).1
  let a : MulAut (Spin n F N) :=
    spinFieldAction n F fs (fieldGenerator f ^ b)
  have square : ∀ x, Φ (e x) = e (a x) :=
    coefficient_generator_square source fs Φ data exponent
  have iterated := pointwise_power_square Φ a e square r g
  have action_power : a ^ r =
      spinFieldAction n F fs (fieldGenerator f ^ (b * r)) :=
    (map_pow (spinFieldAction n F fs) (fieldGenerator f ^ b) r).symm.trans
      (congrArg (spinFieldAction n F fs) (pow_mul (fieldGenerator f) b r).symm)
  exact iterated.trans
    (congrArg (fun action : MulAut (Spin n F N) ↦ e (action g)) action_power)

/-- The canonical fixed-point automorphism has the literal finite field value. -/
theorem coefficient_return_square (r : ℕ) (hs : 0 < s) (g : Spin n F N) :
    fixedPowerAut Φ r s hs (coefficientEquiv source Φ data exponent g) =
      coefficientEquiv source Φ data exponent
        (spinFieldAction n F fs (fieldGenerator f ^ (b * r)) g) := by
  apply Subtype.ext
  exact coefficient_power_square source fs Φ data exponent r g

/-- Conjugation identifies the positive return with an actual full-field actor. -/
theorem coefficient_conjugates_return (r : ℕ) (hs : 0 < s) :
    MulAut.congr (coefficientEquiv source Φ data exponent).symm
      (fixedPowerAut Φ r s hs) =
        spinFieldAction n F fs (fieldGenerator f ^ (b * r)) := by
  let e := coefficientEquiv source Φ data exponent
  apply MulEquiv.ext
  intro g
  apply e.injective
  change e (e.symm (fixedPowerAut Φ r s hs (e g))) =
    e (spinFieldAction n F fs (fieldGenerator f ^ (b * r)) g)
  rw [e.apply_symm_apply]
  exact coefficient_return_square source fs Φ data exponent r hs g

/-- Membership is in the entire prescribed field image, not only a return subgroup. -/
theorem coefficient_return_mem_fieldImage (r : ℕ) (hs : 0 < s) :
    MulAut.congr (coefficientEquiv source Φ data exponent).symm
      (fixedPowerAut Φ r s hs) ∈ (spinFieldAction n F fs).range := by
  rw [coefficient_conjugates_return source fs Φ data exponent]
  exact ⟨fieldGenerator f ^ (b * r), rfl⟩

section Normalized

variable {B : Type*} [Group B]
variable (j : Spin n A Nbar →* B) (U : Subgroup B)
variable (j_injective : Function.Injective j) (j_range : j.range = U)
variable (F0 Fgeo : Monoid.End B) (h u d : ℕ)
variable (hF : Fgeo = F0 ^ h) (fixed_exponent : h * d = u * s)
variable (c : Spin n A Nbar)
variable (generator_value : ∀ x, (F0 ^ u) (j x) = j (c * Φ x * c⁻¹))
variable (a : Spin n A Nbar) (lang_value : Φ a * a⁻¹ = c⁻¹)

/-- Attach the coefficient map to the same single normalized geometric embedding. -/
def normalizedSpinEquiv : Spin n F N ≃* rationalSubgroup (Fgeo ^ d) U :=
  (coefficientEquiv source Φ data exponent).trans
    (normalizedFixedEquiv j U j_injective j_range F0 Fgeo Φ h u d s
      hF fixed_exponent c generator_value a lang_value)

/-- The original positive ambient return becomes the computed full-field power. -/
theorem normalizedSpinEquiv_return_square
    (v q r : ℕ) (return_exponent : v + h * q = u * r) (hs : 0 < s)
    (actualReturn : MulAut (rationalSubgroup (Fgeo ^ d) U))
    (return_value : ∀ y, (actualReturn y).1.1 = (Fgeo ^ q) ((F0 ^ v) y.1.1))
    (g : Spin n F N) :
    actualReturn (normalizedSpinEquiv source Φ data exponent j U j_injective j_range
      F0 Fgeo h u d hF fixed_exponent c generator_value a lang_value g) =
    normalizedSpinEquiv source Φ data exponent j U j_injective j_range
      F0 Fgeo h u d hF fixed_exponent c generator_value a lang_value
        (spinFieldAction n F fs (fieldGenerator f ^ (b * r)) g) := by
  change actualReturn (normalizedFixedEquiv j U j_injective j_range F0 Fgeo Φ h u d s
    hF fixed_exponent c generator_value a lang_value
      (coefficientEquiv source Φ data exponent g)) = _
  rw [normalizedFixedEquiv_return_square j U j_injective j_range F0 Fgeo Φ h u d s
    hF fixed_exponent c generator_value a lang_value v q r return_exponent hs
    actualReturn return_value]
  rw [coefficient_return_square source fs Φ data exponent]
  rfl

end Normalized
end Coefficients

end ModularRep.PaperProofs.TypeBLeviReturnSpinCoefficientBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
