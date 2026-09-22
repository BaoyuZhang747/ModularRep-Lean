import ModularRep.PaperProofs.TypeBRegularLeviOrbitLemma46Relative
import ModularRep.PaperProofs.TypeBCliffordCarriers
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Literal geometric and rational carriers in the Type B regular Levi

Fixed points are equalizers of the specified Frobenius and the identity.
The geometric derived subgroup is the actual subgroup commutator, and the
paired Levi is the actual product with the geometric ambient centre.  No
fixed-point/central-product commutation is assumed.

The identification of these point subgroups with a chosen algebraic Levi,
its geometric derived group and its simple components is an explicit E1/U
boundary (FLZ, Jordan decomposition, proof of Proposition 5.6, p. 31;
Geck--Malle Definition 1.7.1, pp. 80--81).  This file does not replace that
boundary with a predicate asserting the numbered lemma or its conclusions.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBRegularLeviRationalCarriers

open scoped Pointwise commutatorElement
open TypeBRegularLeviOrbitLemma46Relative

section FixedPoints

variable {A : Type*} [Group A]

/-- The actual fixed subgroup of the displayed endomorphism. -/
def fixedPoints (F : A →* A) : Subgroup A := F.eqLocus (MonoidHom.id A)

@[simp] theorem mem_fixedPoints (F : A →* A) (x : A) :
    x ∈ fixedPoints F ↔ F x = x := Iff.rfl

/-- Rational points of a geometric subgroup, as a subgroup of the same
ambient fixed-point group. -/
def rationalSubgroup (F : A →* A) (U : Subgroup A) : Subgroup (fixedPoints F) :=
  U.comap (fixedPoints F).subtype

@[simp] theorem mem_rationalSubgroup (F : A →* A) (U : Subgroup A)
    (x : fixedPoints F) : x ∈ rationalSubgroup F U ↔ x.1 ∈ U := Iff.rfl

theorem rationalSubgroup_mono (F : A →* A) {U V : Subgroup A} (h : U ≤ V) :
    rationalSubgroup F U ≤ rationalSubgroup F V := fun _ hx ↦ h hx

/-- Restrict Frobenius to an actual invariant geometric subgroup. -/
def restrictedFrobenius (F : A →* A) (U : Subgroup A)
    (stable : ∀ x ∈ U, F x ∈ U) : U →* U where
  toFun x := ⟨F x.1, stable x.1 x.2⟩
  map_one' := Subtype.ext F.map_one
  map_mul' x y := Subtype.ext (F.map_mul x.1 y.1)

@[simp] theorem restrictedFrobenius_value (F : A →* A) (U : Subgroup A)
    (stable : ∀ x ∈ U, F x ∈ U) (x : U) :
    (restrictedFrobenius F U stable x).1 = F x.1 := rfl

/-- The two literal fixed-point presentations differ only by the order of
the membership and fixedness proofs in their nested subtypes. -/
def fixedPointsRestrictionEquiv (F : A →* A) (U : Subgroup A)
    (stable : ∀ x ∈ U, F x ∈ U) :
    fixedPoints (restrictedFrobenius F U stable) ≃* rationalSubgroup F U where
  toFun x := ⟨⟨x.1.1, congrArg Subtype.val x.2⟩, x.1.2⟩
  invFun x := ⟨⟨x.1.1, x.2⟩, Subtype.ext x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem fixedPointsRestrictionEquiv_value (F : A →* A) (U : Subgroup A)
    (stable : ∀ x ∈ U, F x ∈ U)
    (x : fixedPoints (restrictedFrobenius F U stable)) :
    (fixedPointsRestrictionEquiv F U stable x).1.1 = x.1.1 := rfl

/-- A group-normalizer inclusion restricts to the same fixed-point carriers. -/
theorem rational_le_normalizer (F : A →* A) (U V : Subgroup A)
    (h : U ≤ Subgroup.normalizer (V : Set A)) :
    rationalSubgroup F U ≤ Subgroup.normalizer (rationalSubgroup F V : Set (fixedPoints F)) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  change y.1 ∈ V ↔ x.1 * y.1 * x.1⁻¹ ∈ V
  exact (Subgroup.mem_normalizer_iff.mp (h hx)) y.1

/-- Normality of a geometric subgroup implies normality in the rational
ambient group. -/
theorem rational_normal (F : A →* A) (U : Subgroup A) [U.Normal] :
    (rationalSubgroup F U).Normal := by
  dsimp [rationalSubgroup]
  infer_instance

/-- A geometric central element that is rational is central in the actual
finite fixed-point group.  The converse is not assumed. -/
theorem rational_center_le_center (F : A →* A) :
    rationalSubgroup F (Subgroup.center A) ≤ Subgroup.center (fixedPoints F) := by
  intro x hx
  apply Subgroup.mem_center_iff.mpr
  intro y
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp hx y.1

end FixedPoints

section GeometricLevi

variable {A : Type*} [Group A]

/-- The geometric derived point subgroup; identifying this with algebraic
derived points is the stated standard algebraic-group input. -/
def derivedLevi (Lbar : Subgroup A) : Subgroup A := ⁅Lbar, Lbar⁆

/-- The paired geometric Levi, with the centre of the geometric ambient
group, not the centre of its rational fixed points. -/
def pairedLevi (Lbar : Subgroup A) : Subgroup A := Lbar ⊔ Subgroup.center A

abbrev L0 (F : A →* A) (Lbar : Subgroup A) := rationalSubgroup F (derivedLevi Lbar)
abbrev L (F : A →* A) (Lbar : Subgroup A) := rationalSubgroup F Lbar
abbrev M (F : A →* A) (Lbar : Subgroup A) := rationalSubgroup F (pairedLevi Lbar)

theorem derivedLevi_le (Lbar : Subgroup A) : derivedLevi Lbar ≤ Lbar :=
  Subgroup.commutator_le_self Lbar

theorem Levi_le_paired (Lbar : Subgroup A) : Lbar ≤ pairedLevi Lbar := le_sup_left

theorem center_le_paired (Lbar : Subgroup A) : Subgroup.center A ≤ pairedLevi Lbar :=
  le_sup_right

theorem paired_le_Levi_normalizer (Lbar : Subgroup A) :
    pairedLevi Lbar ≤ Subgroup.normalizer (Lbar : Set A) := by
  apply sup_le
  · exact Lbar.le_normalizer
  · exact (Subgroup.center_le_centralizer (Lbar : Set A)).trans
      (Subgroup.centralizer_le_normalizer (Lbar : Set A))

theorem paired_le_derived_normalizer (Lbar : Subgroup A) :
    pairedLevi Lbar ≤ Subgroup.normalizer (derivedLevi Lbar : Set A) := by
  apply sup_le
  · exact Subgroup.normalizer_commutator_ge_left Lbar Lbar
  · exact (Subgroup.center_le_centralizer (derivedLevi Lbar : Set A)).trans
      (Subgroup.centralizer_le_normalizer (derivedLevi Lbar : Set A))

theorem L0_le_L (F : A →* A) (Lbar : Subgroup A) : L0 F Lbar ≤ L F Lbar :=
  rationalSubgroup_mono F (derivedLevi_le Lbar)

theorem L_le_M (F : A →* A) (Lbar : Subgroup A) : L F Lbar ≤ M F Lbar :=
  rationalSubgroup_mono F (Levi_le_paired Lbar)

theorem L_normal_M (F : A →* A) (Lbar : Subgroup A) :
    ((L F Lbar).subgroupOf (M F Lbar)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (L_le_M F Lbar)).mpr
    (rational_le_normalizer F (pairedLevi Lbar) Lbar (paired_le_Levi_normalizer Lbar))

theorem L0_normal_L (F : A →* A) (Lbar : Subgroup A) :
    ((L0 F Lbar).subgroupOf (L F Lbar)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (L0_le_L F Lbar)).mpr
    (rational_le_normalizer F Lbar (derivedLevi Lbar)
      (Subgroup.normalizer_commutator_ge_left Lbar Lbar))

theorem L0_normal_M (F : A →* A) (Lbar : Subgroup A) :
    ((L0 F Lbar).subgroupOf (M F Lbar)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer ((L0_le_L F Lbar).trans (L_le_M F Lbar))).mpr
    (rational_le_normalizer F (pairedLevi Lbar) (derivedLevi Lbar)
      (paired_le_derived_normalizer Lbar))

/-- Central factors do not contribute to a commutator. -/
theorem commutator_of_central_factors (l z k w : A)
    (hz : z ∈ Subgroup.center A) (hw : w ∈ Subgroup.center A) :
    ⁅l * z, k * w⁆ = ⁅l, k⁆ := by
  have hz' : ⁅z, k * w⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_center_iff.mp hz (k * w)).symm
  have hw' : ⁅l, w⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hw l)
  rw [commutatorElement_mul_left_eq_conj_mul, hz']
  simp only [mul_one, mul_inv_cancel, one_mul]
  rw [commutatorElement_mul_right_eq_mul_conj, hw']
  group

/-- This is geometric commutator containment, not the generally false
equality between the commutator subgroup of rational points and all
rational points of the geometric derived group. -/
theorem paired_commutator_mem_derived (Lbar : Subgroup A) (x y : A)
    (hx : x ∈ pairedLevi Lbar) (hy : y ∈ pairedLevi Lbar) :
    ⁅x, y⁆ ∈ derivedLevi Lbar := by
  have hx' : x ∈ (Lbar : Set A) * (Subgroup.center A : Set A) := by
    rw [← Subgroup.mul_normal]
    exact hx
  have hy' : y ∈ (Lbar : Set A) * (Subgroup.center A : Set A) := by
    rw [← Subgroup.mul_normal]
    exact hy
  obtain ⟨l, hl, z, hz, rfl⟩ := hx'
  obtain ⟨k, hk, w, hw, rfl⟩ := hy'
  rw [commutator_of_central_factors l z k w hz hw]
  exact Subgroup.commutator_mem_commutator hl hk

theorem rational_commutator_le_L0 (F : A →* A) (Lbar : Subgroup A) :
    _root_.commutator (M F Lbar) ≤ (L0 F Lbar).subgroupOf (M F Lbar) := by
  rw [commutator_def]
  apply Subgroup.commutator_le.mpr
  intro x _ y _
  change ⁅x.1.1, y.1.1⁆ ∈ derivedLevi Lbar
  exact paired_commutator_mem_derived Lbar x.1.1 y.1.1 x.2 y.2

/-- The literal rational quotient `M/L0` is abelian. -/
theorem M_quotient_L0_abelian (F : A →* A) (Lbar : Subgroup A) :
    letI := L0_normal_M F Lbar
    IsMulCommutative (M F Lbar ⧸ (L0 F Lbar).subgroupOf (M F Lbar)) := by
  letI := L0_normal_M F Lbar
  exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
    (rational_commutator_le_L0 F Lbar)

end GeometricLevi

section CompatibleFieldActions

variable {A E : Type*} [Group A] [Group E]

/-- An automorphism preserves the actual geometric centre. -/
theorem automorphism_center_map (a : MulAut A) :
    (Subgroup.center A).map a.toMonoidHom = Subgroup.center A :=
  Subgroup.characteristic_iff_map_eq.mp inferInstance a

theorem derivedLevi_map (Lbar : Subgroup A) (a : MulAut A)
    (hL : Lbar.map a.toMonoidHom = Lbar) :
    (derivedLevi Lbar).map a.toMonoidHom = derivedLevi Lbar := by
  change (⁅Lbar, Lbar⁆ : Subgroup A).map a.toMonoidHom = ⁅Lbar, Lbar⁆
  rw [Subgroup.map_commutator, hL]

theorem pairedLevi_map (Lbar : Subgroup A) (a : MulAut A)
    (hL : Lbar.map a.toMonoidHom = Lbar) :
    (pairedLevi Lbar).map a.toMonoidHom = pairedLevi Lbar := by
  change (Lbar ⊔ Subgroup.center A).map a.toMonoidHom = Lbar ⊔ Subgroup.center A
  rw [Subgroup.map_sup, hL, automorphism_center_map]

/-- Restriction of a specified action on the SAME geometric overgroup.
Commutation with Frobenius is the literal equation making fixed points
invariant; no unspecified extension of a finite field action is used. -/
def fixedPointAction (F : A →* A) (field : E →* MulAut A)
    (commutes : ∀ e x, F (field e x) = field e (F x)) :
    E →* MulAut (fixedPoints F) where
  toFun e :=
    { toFun := fun x ↦ ⟨field e x.1, (commutes e x.1).trans (congrArg (field e) x.2)⟩
      invFun := fun x ↦ ⟨field e⁻¹ x.1,
        (commutes e⁻¹ x.1).trans (congrArg (field e⁻¹) x.2)⟩
      left_inv := by intro x; apply Subtype.ext; simp
      right_inv := by intro x; apply Subtype.ext; simp
      map_mul' := by intro x y; apply Subtype.ext; exact map_mul (field e) x.1 y.1 }
  map_one' := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    simp
  map_mul' e f := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun a : MulAut A ↦ a x.1) (field.map_mul e f)

@[simp] theorem fixedPointAction_value (F : A →* A) (field : E →* MulAut A)
    (commutes : ∀ e x, F (field e x) = field e (F x))
    (e : E) (x : fixedPoints F) :
    (fixedPointAction F field commutes e x).1 = field e x.1 := rfl

theorem rationalSubgroup_action_map (F : A →* A) (field : E →* MulAut A)
    (commutes : ∀ e x, F (field e x) = field e (F x))
    (U : Subgroup A) (stable : ∀ e, U.map (field e).toMonoidHom = U) (e : E) :
    (rationalSubgroup F U).map (fixedPointAction F field commutes e).toMonoidHom =
      rationalSubgroup F U := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change y.1 ∈ U at hy
    change field e y.1 ∈ U
    have h := Subgroup.mem_map_of_mem (field e).toMonoidHom hy
    rw [stable e] at h
    exact h
  · intro hx
    change x.1 ∈ U at hx
    refine ⟨fixedPointAction F field commutes e⁻¹ x, ?_, ?_⟩
    · change field e⁻¹ x.1 ∈ U
      have h := Subgroup.mem_map_of_mem (field e⁻¹).toMonoidHom hx
      rw [stable e⁻¹] at h
      exact h
    · simp

/-- The same specified compatible field action preserves all three
members of the literal normal chain. -/
theorem field_preserves_chain (F : A →* A) (field : E →* MulAut A)
    (commutes : ∀ e x, F (field e x) = field e (F x))
    (Lbar : Subgroup A) (stable : ∀ e, Lbar.map (field e).toMonoidHom = Lbar)
    (e : E) :
    (L0 F Lbar).map (fixedPointAction F field commutes e).toMonoidHom = L0 F Lbar ∧
    (L F Lbar).map (fixedPointAction F field commutes e).toMonoidHom = L F Lbar ∧
    (M F Lbar).map (fixedPointAction F field commutes e).toMonoidHom = M F Lbar := by
  exact ⟨rationalSubgroup_action_map F field commutes (derivedLevi Lbar)
      (fun e ↦ derivedLevi_map Lbar (field e) (stable e)) e,
    rationalSubgroup_action_map F field commutes Lbar stable e,
    rationalSubgroup_action_map F field commutes (pairedLevi Lbar)
      (fun e ↦ pairedLevi_map Lbar (field e) (stable e)) e⟩

end CompatibleFieldActions

section EffectiveSquares

variable {A : Type*} [Group A]

/-- A direct central correction for the ambient regular embedding.  The
geometric factors of a rational element are not assumed rational.  Their
Frobenius defect belongs to the actual centre intersection, whose square is
one; only then are the squares of both factors shown rational. -/
theorem ambient_rational_square_factors (F : MulAut A) (Gbar : Subgroup A)
    (Gstable : ∀ g ∈ Gbar, F g ∈ Gbar)
    (decomposition : ∀ x : A, ∃ g ∈ Gbar, ∃ z ∈ Subgroup.center A, x = g * z)
    (centre_two : ∀ t : A, t ∈ Gbar → t ∈ Subgroup.center A → t ^ 2 = 1)
    (x : fixedPoints F.toMonoidHom) :
    ∃ g : fixedPoints F.toMonoidHom, g ∈ rationalSubgroup F.toMonoidHom Gbar ∧
      ∃ z : fixedPoints F.toMonoidHom,
        z ∈ rationalSubgroup F.toMonoidHom (Subgroup.center A) ∧ x ^ 2 = g * z := by
  obtain ⟨g, hg, z, hz, hx⟩ := decomposition x.1
  have hfixed : F (g * z) = g * z := by rw [← hx]; exact x.2
  have hF : F g * F z = g * z := by simpa only [map_mul] using hfixed
  let t := g⁻¹ * F g
  have htG : t ∈ Gbar := Gbar.mul_mem (Gbar.inv_mem hg) (Gstable g hg)
  have htEq : t = z * (F z)⁻¹ := by
    calc
      t = g⁻¹ * (F g * F z) * (F z)⁻¹ := by dsimp [t]; group
      _ = g⁻¹ * (g * z) * (F z)⁻¹ := by rw [hF]
      _ = z * (F z)⁻¹ := by group
  have hFzCentre : F z ∈ Subgroup.center A := by
    have h := Subgroup.mem_map_of_mem F.toMonoidHom hz
    rw [automorphism_center_map] at h
    exact h
  have htCentre : t ∈ Subgroup.center A := by
    rw [htEq]
    exact (Subgroup.center A).mul_mem hz ((Subgroup.center A).inv_mem hFzCentre)
  have htTwo : t ^ 2 = 1 := centre_two t htG htCentre
  have hFg : F g = g * t := by dsimp [t]; group
  have hFz : F z = t⁻¹ * z := by rw [htEq]; group
  have hgt : Commute g t := Subgroup.mem_center_iff.mp htCentre g
  have htz : Commute t⁻¹ z :=
    (Subgroup.mem_center_iff.mp ((Subgroup.center A).inv_mem htCentre) z).symm
  have hgFixed : F (g ^ 2) = g ^ 2 := by
    rw [map_pow, hFg, hgt.mul_pow, htTwo, mul_one]
  have hzFixed : F (z ^ 2) = z ^ 2 := by
    rw [map_pow, hFz, htz.mul_pow]
    simp only [inv_pow, htTwo, inv_one, one_mul]
  refine ⟨⟨g ^ 2, hgFixed⟩, Gbar.pow_mem hg 2,
    ⟨z ^ 2, hzFixed⟩, (Subgroup.center A).pow_mem hz 2, ?_⟩
  apply Subtype.ext
  change x.1 ^ 2 = g ^ 2 * z ^ 2
  rw [hx]
  exact (show Commute g z from Subgroup.mem_center_iff.mp hz g).mul_pow 2

/-- Exact exponent of `M/(L C_M(L))`, derived from the same literal
fixed-point carriers, geometric intersection and ambient central geometry.
No effective-quotient exponent is an input. -/
theorem effective_quotient_exponent_two (F : MulAut A) (Gbar Lbar : Subgroup A)
    (Gstable : ∀ g ∈ Gbar, F g ∈ Gbar)
    (decomposition : ∀ x : A, ∃ g ∈ Gbar, ∃ z ∈ Subgroup.center A, x = g * z)
    (centre_two : ∀ t : A, t ∈ Gbar → t ∈ Subgroup.center A → t ^ 2 = 1)
    (intersection : pairedLevi Lbar ⊓ Gbar ≤ Lbar) :
    letI := effectiveKernel_normal_of_le_normalizer
      (M F.toMonoidHom Lbar) (L F.toMonoidHom Lbar) (L_le_M F.toMonoidHom Lbar)
      (rational_le_normalizer F.toMonoidHom (pairedLevi Lbar) Lbar
        (paired_le_Levi_normalizer Lbar))
    ∀ q : M F.toMonoidHom Lbar ⧸
      effectiveKernel (M F.toMonoidHom Lbar) (L F.toMonoidHom Lbar), q ^ 2 = 1 := by
  letI := effectiveKernel_normal_of_le_normalizer
    (M F.toMonoidHom Lbar) (L F.toMonoidHom Lbar) (L_le_M F.toMonoidHom Lbar)
    (rational_le_normalizer F.toMonoidHom (pairedLevi Lbar) Lbar
      (paired_le_Levi_normalizer Lbar))
  apply pairedLevi_effectiveQuotient_exponent_two
    (rationalSubgroup F.toMonoidHom Gbar) (M F.toMonoidHom Lbar)
    (L F.toMonoidHom Lbar) (rationalSubgroup F.toMonoidHom (Subgroup.center A))
  · exact rationalSubgroup_mono F.toMonoidHom (center_le_paired Lbar)
  · exact (rational_center_le_center F.toMonoidHom).trans
      (Subgroup.center_le_centralizer (L F.toMonoidHom Lbar : Set (fixedPoints F.toMonoidHom)))
  · intro x hx
    exact intersection hx
  · intro x _
    exact ambient_rational_square_factors F Gbar Gstable decomposition centre_two x

end EffectiveSquares

section DerivedInsidePaired

variable {A : Type*} [Group A]

def geometricDerivedInPaired (Lbar : Subgroup A) : Subgroup (pairedLevi Lbar) :=
  (derivedLevi Lbar).subgroupOf (pairedLevi Lbar)

/-- Canonical identification of the same geometric derived point group. -/
def geometricDerivedEquiv (Lbar : Subgroup A) :
    geometricDerivedInPaired Lbar ≃* derivedLevi Lbar :=
  Subgroup.subgroupOfEquivOfLe ((derivedLevi_le Lbar).trans (Levi_le_paired Lbar))

@[simp] theorem geometricDerivedEquiv_value (Lbar : Subgroup A)
    (h : geometricDerivedInPaired Lbar) :
    (geometricDerivedEquiv Lbar h).1 = h.1.1 := rfl

end DerivedInsidePaired

section LiteralClifford

open TypeBCliffordCarriers

variable (n p f : ℕ) (F Kbar : Type)
variable [Field F] [Finite F] [CharP F p] [Field Kbar] [Algebra F Kbar]
variable (N : NormSource n F) (Nbar : NormSource n Kbar)
variable (Frob : MulAut (SpecialClifford n Kbar))

/-- Exact E1/U descent data for the actual split Clifford polynomial model.
Sources: FLZ type B, §2.5 pp. 539--540 and §3.1 p. 541; Geck--Malle,
Definition 1.4.1 pp. 40--41, Example 1.4.2 p. 41 and §1.4.5 p. 42.
The coefficient and Frobenius maps are fixed on scalar/vector generators.
The fixed-range assertion remains a finite-field descent input; it is not
claimed to follow merely from those generator equations.  No Levi, orbit,
exponent or representation theoretic conclusion is part of this source. -/
structure CliffordFixedPointSource where
  rank : 3 ≤ n
  parameters : OddFieldParameters F p f
  algebraicallyClosed : IsAlgClosed Kbar
  characteristic : CharP Kbar p
  coefficientMap : Clifford n F →+* Clifford n Kbar
  coefficient_scalar : ∀ a : F,
    coefficientMap (algebraMap F (Clifford n F) a) =
      algebraMap Kbar (Clifford n Kbar) (algebraMap F Kbar a)
  coefficient_vector : ∀ v : Vector n F,
    coefficientMap (CliffordAlgebra.ι (splitForm n F) v) =
      CliffordAlgebra.ι (splitForm n Kbar) (fun j ↦ algebraMap F Kbar (v j))
  inclusion : SpecialClifford n F →* SpecialClifford n Kbar
  inclusion_value : ∀ g,
    toClifford n Kbar (inclusion g) = coefficientMap (toClifford n F g)
  inclusion_injective : Function.Injective inclusion
  fixed_range : inclusion.range = fixedPoints Frob.toMonoidHom
  norm_compatible : ∀ g,
    Nbar.norm (inclusion g) = Units.map (algebraMap F Kbar).toMonoidHom (N.norm g)
  algebraFrobenius : Clifford n Kbar ≃+* Clifford n Kbar
  frobenius_scalar : ∀ a : Kbar,
    algebraFrobenius (algebraMap Kbar (Clifford n Kbar) a) =
      algebraMap Kbar (Clifford n Kbar) (a ^ Nat.card F)
  frobenius_vector : ∀ v : Vector n Kbar,
    algebraFrobenius (CliffordAlgebra.ι (splitForm n Kbar) v) =
      CliffordAlgebra.ι (splitForm n Kbar) (fun j ↦ v j ^ Nat.card F)
  frobenius_value : ∀ g,
    toClifford n Kbar (Frob g) = algebraFrobenius (toClifford n Kbar g)
  frobenius_norm : ∀ g, Nbar.norm (Frob g) = Nbar.norm g ^ Nat.card F

variable (S : CliffordFixedPointSource n p f F Kbar N Nbar Frob)

/-- The finite special Clifford group maps into the geometric fixed points. -/
def finiteToFixed : SpecialClifford n F →* fixedPoints Frob.toMonoidHom where
  toFun g := ⟨S.inclusion g, by rw [← S.fixed_range]; exact ⟨g, rfl⟩⟩
  map_one' := Subtype.ext S.inclusion.map_one
  map_mul' g h := Subtype.ext (S.inclusion.map_mul g h)

@[simp] theorem finiteToFixed_value (g : SpecialClifford n F) :
    (finiteToFixed n p f F Kbar N Nbar Frob S g).1 = S.inclusion g := rfl

theorem finiteToFixed_bijective :
    Function.Bijective (finiteToFixed n p f F Kbar N Nbar Frob S) := by
  constructor
  · intro g h heq
    exact S.inclusion_injective (congrArg Subtype.val heq)
  · intro x
    have hx : x.1 ∈ S.inclusion.range := by rw [S.fixed_range]; exact x.2
    obtain ⟨g, hg⟩ := hx
    exact ⟨g, Subtype.ext hg⟩

/-- Canonical descent onto the literal finite special Clifford carrier. -/
def finiteAmbientEquiv : SpecialClifford n F ≃* fixedPoints Frob.toMonoidHom :=
  MulEquiv.ofBijective (finiteToFixed n p f F Kbar N Nbar Frob S)
    (finiteToFixed_bijective n p f F Kbar N Nbar Frob S)

theorem inclusion_spin_iff (g : SpecialClifford n F) :
    S.inclusion g ∈ SpinSubgroup n Kbar Nbar ↔ g ∈ SpinSubgroup n F N := by
  change Nbar.norm (S.inclusion g) = 1 ↔ N.norm g = 1
  rw [S.norm_compatible]
  constructor
  · intro h
    apply Units.ext
    apply (algebraMap F Kbar).injective
    have hv := congrArg (fun z : Kbarˣ ↦ (z : Kbar)) h
    simpa using hv
  · intro h
    rw [h, map_one]

/-- Spin descent uses the same norm and base-change map as ambient descent. -/
def finiteSpinToFixed : Spin n F N →*
    rationalSubgroup Frob.toMonoidHom (SpinSubgroup n Kbar Nbar) where
  toFun g := ⟨finiteToFixed n p f F Kbar N Nbar Frob S g.1,
    (inclusion_spin_iff n p f F Kbar N Nbar Frob S g.1).mpr g.2⟩
  map_one' := Subtype.ext (map_one (finiteToFixed n p f F Kbar N Nbar Frob S))
  map_mul' g h := Subtype.ext
    (map_mul (finiteToFixed n p f F Kbar N Nbar Frob S) g.1 h.1)

theorem finiteSpinToFixed_bijective :
    Function.Bijective (finiteSpinToFixed n p f F Kbar N Nbar Frob S) := by
  constructor
  · intro g h heq
    apply Subtype.ext
    apply S.inclusion_injective
    exact congrArg (fun z : rationalSubgroup Frob.toMonoidHom (SpinSubgroup n Kbar Nbar) ↦
      z.1.1) heq
  · intro x
    obtain ⟨g, hg⟩ := (finiteToFixed_bijective n p f F Kbar N Nbar Frob S).2 x.1
    have hSpin : g ∈ SpinSubgroup n F N := by
      apply (inclusion_spin_iff n p f F Kbar N Nbar Frob S g).mp
      have hval := congrArg Subtype.val hg
      change S.inclusion g = x.1.1 at hval
      rw [hval]
      exact x.2
    exact ⟨⟨g, hSpin⟩, Subtype.ext hg⟩

def finiteSpinEquiv : Spin n F N ≃*
    rationalSubgroup Frob.toMonoidHom (SpinSubgroup n Kbar Nbar) :=
  MulEquiv.ofBijective (finiteSpinToFixed n p f F Kbar N Nbar Frob S)
    (finiteSpinToFixed_bijective n p f F Kbar N Nbar Frob S)

include S in
theorem geometric_fixedPoints_finite (finite : FiniteCliffordSource n F) :
    Finite (fixedPoints Frob.toMonoidHom) := by
  letI := specialClifford_finite n F finite
  exact Finite.of_equiv (SpecialClifford n F)
    (finiteAmbientEquiv n p f F Kbar N Nbar Frob S).toEquiv

include S in
theorem geometricSpin_frobenius_stable :
    ∀ g ∈ SpinSubgroup n Kbar Nbar, Frob g ∈ SpinSubgroup n Kbar Nbar := by
  intro g hg
  change Nbar.norm g = 1 at hg
  change Nbar.norm (Frob g) = 1
  rw [S.frobenius_norm, hg, one_pow]

/-- Lower regular-Levi point data inside the actual special Clifford group.
Identifying `levi` with an algebraic Levi remains U until that construction
is attached.  The central decomposition, intersection and type B centre
bound are exact routine structural inputs, not rational quotient or orbit
conclusions.  Sources: Geck--Malle Definition 1.7.1/Remark 1.7.6;
Malle--Testerman 9.15/Table 9.2. -/
structure LeviPointData where
  levi : Subgroup (SpecialClifford n Kbar)
  levi_le_spin : levi ≤ SpinSubgroup n Kbar Nbar
  frobenius_stable : levi.map Frob.toMonoidHom = levi
  intersection : pairedLevi levi ⊓ SpinSubgroup n Kbar Nbar = levi
  central_decomposition : ∀ x : SpecialClifford n Kbar,
    ∃ g ∈ SpinSubgroup n Kbar Nbar, ∃ z ∈ Subgroup.center (SpecialClifford n Kbar), x = g * z
  central_spin_square : ∀ t : SpecialClifford n Kbar,
    t ∈ SpinSubgroup n Kbar Nbar → t ∈ Subgroup.center (SpecialClifford n Kbar) → t ^ 2 = 1

end LiteralClifford

end ModularRep.PaperProofs.TypeBRegularLeviRationalCarriers


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
