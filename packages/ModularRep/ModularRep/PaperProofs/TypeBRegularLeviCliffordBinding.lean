import ModularRep.PaperProofs.TypeBRegularLeviRationalCarriers

/-!
# Same-point regular-Levi carrier bindings

The generic part identifies the fixed points inside the geometric paired
Levi with the already defined rational subgroups of the ambient fixed-point
group.  The maps only reorder subtype proofs.  The Clifford specialization
then uses the exact base-change inclusion of `CliffordFixedPointSource`.

No algebraic Levi recognition, connected-centre statement, supported lift,
product-action surjectivity, or character-orbit conclusion is assumed here.
The remaining E1/U algebraic interpretation uses Geck--Malle Definition 1.7.1,
pp. 80--81 and Remark 1.7.6, p. 85; the literal Clifford descent source is
FLZ type B Section 2.5, pp. 539--540 and Section 3.1, p. 541, with
Geck--Malle Definition 1.4.1, pp. 40--41 and Section 1.4.5, p. 42.
The generic construction does not identify every regular embedding with
the particular Clifford embedding.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBRegularLeviCliffordBinding

open TypeBRegularLeviRationalCarriers
open TypeBRegularLeviOrbitLemma46Relative
open scoped commutatorElement

section PairedCarriers

variable {A : Type*} [Group A]

/-- The literal geometric paired Levi, inside its original ambient group. -/
abbrev B (Lbar : Subgroup A) := pairedLevi Lbar

/-- The literal geometric derived group, inside the paired Levi. -/
abbrev H (Lbar : Subgroup A) := geometricDerivedInPaired Lbar

variable (Frob : MulAut A) (Lbar : Subgroup A)
variable (stable : Lbar.map Frob.toMonoidHom = Lbar)

include stable in
theorem paired_frobenius_stable :
    ∀ x ∈ B Lbar, Frob x ∈ B Lbar := by
  intro x hx
  have h := Subgroup.mem_map_of_mem Frob.toMonoidHom hx
  rw [pairedLevi_map Lbar Frob stable] at h
  exact h

/-- The actual ambient Frobenius restricted to the paired Levi. -/
def frobeniusB : B Lbar →* B Lbar :=
  restrictedFrobenius Frob.toMonoidHom (B Lbar)
    (paired_frobenius_stable Frob Lbar stable)

@[simp] theorem frobeniusB_value (x : B Lbar) :
    (frobeniusB Frob Lbar stable x).1 = Frob x.1 := rfl

include stable in
theorem geometricH_stable :
    ∀ h ∈ H Lbar, frobeniusB Frob Lbar stable h ∈ H Lbar := by
  intro h hh
  change Frob h.1 ∈ derivedLevi Lbar
  change h.1 ∈ derivedLevi Lbar at hh
  have hx := Subgroup.mem_map_of_mem Frob.toMonoidHom hh
  rw [derivedLevi_map Lbar Frob stable] at hx
  exact hx

/-- The same Frobenius restricted again to the actual derived subgroup. -/
def frobeniusH : H Lbar →* H Lbar :=
  restrictedFrobenius (frobeniusB Frob Lbar stable) (H Lbar)
    (geometricH_stable Frob Lbar stable)

@[simp] theorem frobeniusH_value (h : H Lbar) :
    (frobeniusH Frob Lbar stable h).1.1 = Frob h.1.1 := rfl

/-- Fixed points of the paired subgroup are exactly the earlier `M`.
This is a same-point map, not a rational central-product decomposition. -/
def fixedBEquivM : fixedPoints (frobeniusB Frob Lbar stable) ≃*
    M Frob.toMonoidHom Lbar :=
  fixedPointsRestrictionEquiv Frob.toMonoidHom (B Lbar)
    (paired_frobenius_stable Frob Lbar stable)

@[simp] theorem fixedBEquivM_value
    (x : fixedPoints (frobeniusB Frob Lbar stable)) :
    (fixedBEquivM Frob Lbar stable x).1.1 = x.1.1 := rfl

@[simp] theorem fixedBEquivM_symm_value (x : M Frob.toMonoidHom Lbar) :
    ((fixedBEquivM Frob Lbar stable).symm x).1.1 = x.1.1 := rfl

/-- Rational points of `H` inside `B^F` are the same literal `L0`.
Only the order of the fixedness and subgroup-membership proofs changes. -/
def rationalHEquivL0 :
    rationalSubgroup (frobeniusB Frob Lbar stable) (H Lbar) ≃*
      L0 Frob.toMonoidHom Lbar where
  toFun x := ⟨⟨x.1.1.1, congrArg Subtype.val x.1.2⟩, x.2⟩
  invFun x :=
    ⟨⟨⟨x.1.1, ((derivedLevi_le Lbar).trans (Levi_le_paired Lbar)) x.2⟩,
        Subtype.ext x.1.2⟩, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem rationalHEquivL0_value
    (x : rationalSubgroup (frobeniusB Frob Lbar stable) (H Lbar)) :
    (rationalHEquivL0 Frob Lbar stable x).1.1 = x.1.1.1 := rfl

@[simp] theorem rationalHEquivL0_symm_value (x : L0 Frob.toMonoidHom Lbar) :
    ((rationalHEquivL0 Frob Lbar stable).symm x).1.1.1 = x.1.1 := rfl

/-- The fully restricted geometric derived fixed points also give `L0`. -/
def fixedHEquivL0 : fixedPoints (frobeniusH Frob Lbar stable) ≃*
    L0 Frob.toMonoidHom Lbar :=
  (fixedPointsRestrictionEquiv (frobeniusB Frob Lbar stable) (H Lbar)
    (geometricH_stable Frob Lbar stable)).trans
      (rationalHEquivL0 Frob Lbar stable)

@[simp] theorem fixedHEquivL0_value
    (x : fixedPoints (frobeniusH Frob Lbar stable)) :
    (fixedHEquivL0 Frob Lbar stable x).1.1 = x.1.1.1 := rfl

/-- The subgroup identification is compatible with its actual inclusion in M. -/
theorem rationalH_map_fixedBEquivM :
    (rationalSubgroup (frobeniusB Frob Lbar stable) (H Lbar)).map
        (fixedBEquivM Frob Lbar stable).toMonoidHom =
      (L0 Frob.toMonoidHom Lbar).subgroupOf (M Frob.toMonoidHom Lbar) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨(fixedBEquivM Frob Lbar stable).symm x, hx,
      (fixedBEquivM Frob Lbar stable).apply_symm_apply x⟩

theorem H_normal : (H Lbar).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
    ((derivedLevi_le Lbar).trans (Levi_le_paired Lbar))).mpr
      (paired_le_derived_normalizer Lbar)

theorem rationalH_normal :
    (rationalSubgroup (frobeniusB Frob Lbar stable) (H Lbar)).Normal := by
  letI := H_normal Lbar
  exact rational_normal (frobeniusB Frob Lbar stable) (H Lbar)

/-- Abelianity on the exact fixed-point presentation used by supported lifts. -/
theorem fixedB_quotient_rationalH_abelian :
    letI := rationalH_normal Frob Lbar stable
    IsMulCommutative (fixedPoints (frobeniusB Frob Lbar stable) ⧸
      rationalSubgroup (frobeniusB Frob Lbar stable) (H Lbar)) := by
  letI := rationalH_normal Frob Lbar stable
  apply Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
  rw [commutator_def]
  apply Subgroup.commutator_le.mpr
  intro x _ y _
  change ⁅x.1.1, y.1.1⁆ ∈ derivedLevi Lbar
  exact paired_commutator_mem_derived Lbar x.1.1 y.1.1 x.1.2 y.1.2

end PairedCarriers

section SpecifiedField

variable {A E : Type*} [Group A] [Group E]

/-- Restriction of a specified geometric action to an invariant subgroup. -/
def subgroupField (field : E →* MulAut A) (U : Subgroup A)
    (stable : ∀ e, U.map (field e).toMonoidHom = U) : E →* MulAut U where
  toFun e :=
    { toFun := fun x ↦ ⟨field e x.1, by
        have h := Subgroup.mem_map_of_mem (field e).toMonoidHom x.2
        rw [stable e] at h
        exact h⟩
      invFun := fun x ↦ ⟨field e⁻¹ x.1, by
        have h := Subgroup.mem_map_of_mem (field e⁻¹).toMonoidHom x.2
        rw [stable e⁻¹] at h
        exact h⟩
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

@[simp] theorem subgroupField_value (field : E →* MulAut A) (U : Subgroup A)
    (stable : ∀ e, U.map (field e).toMonoidHom = U) (e : E) (x : U) :
    (subgroupField field U stable e x).1 = field e x.1 := rfl

variable (Frob : MulAut A) (Lbar : Subgroup A)
variable (stable : Lbar.map Frob.toMonoidHom = Lbar)
variable (field : E →* MulAut A)
variable (commutes : ∀ e x, Frob (field e x) = field e (Frob x))
variable (field_stable : ∀ e, Lbar.map (field e).toMonoidHom = Lbar)

def fieldB : E →* MulAut (B Lbar) :=
  subgroupField field (B Lbar) (fun e ↦ pairedLevi_map Lbar (field e) (field_stable e))

include commutes in
theorem fieldB_commutes : ∀ e x,
    frobeniusB Frob Lbar stable (fieldB Lbar field field_stable e x) =
      fieldB Lbar field field_stable e (frobeniusB Frob Lbar stable x) := by
  intro e x
  apply Subtype.ext
  exact commutes e x.1

/-- The action on B^F is derived from the same ambient geometric action. -/
def fieldFixedB : E →* MulAut (fixedPoints (frobeniusB Frob Lbar stable)) :=
  fixedPointAction (frobeniusB Frob Lbar stable) (fieldB Lbar field field_stable)
    (fieldB_commutes Frob Lbar stable field commutes field_stable)

theorem fixedBEquivM_field_value (e : E)
    (x : fixedPoints (frobeniusB Frob Lbar stable)) :
    (fixedBEquivM Frob Lbar stable
      (fieldFixedB Frob Lbar stable field commutes field_stable e x)).1 =
    fixedPointAction Frob.toMonoidHom field commutes e
      (fixedBEquivM Frob Lbar stable x).1 := by
  apply Subtype.ext
  rfl

include field_stable in
theorem H_field_stable (e : E) :
    (H Lbar).map (fieldB Lbar field field_stable e).toMonoidHom = H Lbar := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change field e y.1 ∈ derivedLevi Lbar
    change y.1 ∈ derivedLevi Lbar at hy
    have h := Subgroup.mem_map_of_mem (field e).toMonoidHom hy
    rw [derivedLevi_map Lbar (field e) (field_stable e)] at h
    exact h
  · intro hx
    refine ⟨fieldB Lbar field field_stable e⁻¹ x, ?_, ?_⟩
    · change field e⁻¹ x.1 ∈ derivedLevi Lbar
      change x.1 ∈ derivedLevi Lbar at hx
      have h := Subgroup.mem_map_of_mem (field e⁻¹).toMonoidHom hx
      rw [derivedLevi_map Lbar (field e⁻¹) (field_stable e⁻¹)] at h
      exact h
    · simp

theorem rationalH_field_stable (e : E) :
    (rationalSubgroup (frobeniusB Frob Lbar stable) (H Lbar)).map
        (fieldFixedB Frob Lbar stable field commutes field_stable e).toMonoidHom =
      rationalSubgroup (frobeniusB Frob Lbar stable) (H Lbar) :=
  rationalSubgroup_action_map (frobeniusB Frob Lbar stable)
    (fieldB Lbar field field_stable)
    (fieldB_commutes Frob Lbar stable field commutes field_stable)
    (H Lbar) (H_field_stable Lbar field field_stable) e

end SpecifiedField

section Clifford

open TypeBCliffordCarriers

variable (n p f : ℕ) (F Kbar : Type)
variable [Field F] [Finite F] [CharP F p] [Field Kbar] [Algebra F Kbar]
variable (N : NormSource n F) (Nbar : NormSource n Kbar)
variable (Frob : MulAut (SpecialClifford n Kbar))
variable (S : CliffordFixedPointSource n p f F Kbar N Nbar Frob)
variable (P : LeviPointData n Kbar Nbar Frob)

/-- The finite subgroup is the literal inverse image under the specified
Clifford base-change inclusion, never an independently named carrier. -/
def finiteSubgroup (U : Subgroup (SpecialClifford n Kbar)) :
    Subgroup (SpecialClifford n F) := U.comap S.inclusion

def finiteSubgroupToRational (U : Subgroup (SpecialClifford n Kbar)) :
    finiteSubgroup n p f F Kbar N Nbar Frob S U →*
      rationalSubgroup Frob.toMonoidHom U where
  toFun x := ⟨finiteToFixed n p f F Kbar N Nbar Frob S x.1, x.2⟩
  map_one' := Subtype.ext (map_one (finiteToFixed n p f F Kbar N Nbar Frob S))
  map_mul' x y := Subtype.ext
    (map_mul (finiteToFixed n p f F Kbar N Nbar Frob S) x.1 y.1)

theorem finiteSubgroupToRational_bijective (U : Subgroup (SpecialClifford n Kbar)) :
    Function.Bijective (finiteSubgroupToRational n p f F Kbar N Nbar Frob S U) := by
  constructor
  · intro x y h
    apply Subtype.ext
    apply S.inclusion_injective
    exact congrArg (fun z : rationalSubgroup Frob.toMonoidHom U ↦ z.1.1) h
  · intro x
    obtain ⟨g, hg⟩ := (finiteToFixed_bijective n p f F Kbar N Nbar Frob S).2 x.1
    have hgU : g ∈ finiteSubgroup n p f F Kbar N Nbar Frob S U := by
      change S.inclusion g ∈ U
      have hv := congrArg Subtype.val hg
      change S.inclusion g = x.1.1 at hv
      rw [hv]
      exact x.2
    exact ⟨⟨g, hgU⟩, Subtype.ext hg⟩

/-- Exact descent on every literal geometric subgroup, using the same
ambient fixed-range theorem and the same inclusion as Spin descent. -/
def finiteSubgroupEquiv (U : Subgroup (SpecialClifford n Kbar)) :
    finiteSubgroup n p f F Kbar N Nbar Frob S U ≃*
      rationalSubgroup Frob.toMonoidHom U :=
  MulEquiv.ofBijective (finiteSubgroupToRational n p f F Kbar N Nbar Frob S U)
    (finiteSubgroupToRational_bijective n p f F Kbar N Nbar Frob S U)

@[simp] theorem finiteSubgroupEquiv_value (U : Subgroup (SpecialClifford n Kbar))
    (x : finiteSubgroup n p f F Kbar N Nbar Frob S U) :
    (finiteSubgroupEquiv n p f F Kbar N Nbar Frob S U x).1.1 = S.inclusion x.1 := rfl

abbrev finiteM := finiteSubgroup n p f F Kbar N Nbar Frob S (pairedLevi P.levi)
abbrev finiteL := finiteSubgroup n p f F Kbar N Nbar Frob S P.levi
abbrev finiteL0 := finiteSubgroup n p f F Kbar N Nbar Frob S (derivedLevi P.levi)

def finiteMEquivFixedB : finiteM n p f F Kbar N Nbar Frob S P ≃*
    fixedPoints (frobeniusB Frob P.levi P.frobenius_stable) :=
  (finiteSubgroupEquiv n p f F Kbar N Nbar Frob S (pairedLevi P.levi)).trans
    (fixedBEquivM Frob P.levi P.frobenius_stable).symm

@[simp] theorem finiteMEquivFixedB_value
    (x : finiteM n p f F Kbar N Nbar Frob S P) :
    (finiteMEquivFixedB n p f F Kbar N Nbar Frob S P x).1.1 = S.inclusion x.1 := rfl

def finiteL0EquivRationalH : finiteL0 n p f F Kbar N Nbar Frob S P ≃*
    rationalSubgroup (frobeniusB Frob P.levi P.frobenius_stable) (H P.levi) :=
  (finiteSubgroupEquiv n p f F Kbar N Nbar Frob S (derivedLevi P.levi)).trans
    (rationalHEquivL0 Frob P.levi P.frobenius_stable).symm

@[simp] theorem finiteL0EquivRationalH_value
    (x : finiteL0 n p f F Kbar N Nbar Frob S P) :
    (finiteL0EquivRationalH n p f F Kbar N Nbar Frob S P x).1.1.1 = S.inclusion x.1 := rfl

theorem finiteL_le_spin :
    finiteL n p f F Kbar N Nbar Frob S P ≤ SpinSubgroup n F N := by
  intro g hg
  apply (inclusion_spin_iff n p f F Kbar N Nbar Frob S g).mp
  exact P.levi_le_spin hg

theorem finiteL0_le_finiteL :
    finiteL0 n p f F Kbar N Nbar Frob S P ≤ finiteL n p f F Kbar N Nbar Frob S P :=
  fun _ hx ↦ derivedLevi_le P.levi hx

theorem finiteL_le_finiteM :
    finiteL n p f F Kbar N Nbar Frob S P ≤ finiteM n p f F Kbar N Nbar Frob S P :=
  fun _ hx ↦ Levi_le_paired P.levi hx

include S in
theorem pairedFixed_finite (finite : FiniteCliffordSource n F) :
    Finite (fixedPoints (frobeniusB Frob P.levi P.frobenius_stable)) := by
  letI := geometric_fixedPoints_finite n p f F Kbar N Nbar Frob S finite
  exact Finite.of_equiv (M Frob.toMonoidHom P.levi)
    (fixedBEquivM Frob P.levi P.frobenius_stable).symm.toEquiv

include S in
theorem derivedRational_finite (finite : FiniteCliffordSource n F) :
    Finite (rationalSubgroup (frobeniusB Frob P.levi P.frobenius_stable) (H P.levi)) := by
  letI := pairedFixed_finite n p f F Kbar N Nbar Frob S P finite
  infer_instance

/-- The same actual normal chain is retained after the lower carrier binding. -/
theorem rational_normal_chain :
    ((L0 Frob.toMonoidHom P.levi).subgroupOf (L Frob.toMonoidHom P.levi)).Normal ∧
    ((L Frob.toMonoidHom P.levi).subgroupOf (M Frob.toMonoidHom P.levi)).Normal ∧
    ((L0 Frob.toMonoidHom P.levi).subgroupOf (M Frob.toMonoidHom P.levi)).Normal :=
  ⟨L0_normal_L Frob.toMonoidHom P.levi, L_normal_M Frob.toMonoidHom P.levi,
    L0_normal_M Frob.toMonoidHom P.levi⟩

theorem rational_M_quotient_L0_abelian :
    letI := L0_normal_M Frob.toMonoidHom P.levi
    IsMulCommutative (M Frob.toMonoidHom P.levi ⧸
      (L0 Frob.toMonoidHom P.levi).subgroupOf (M Frob.toMonoidHom P.levi)) :=
  M_quotient_L0_abelian Frob.toMonoidHom P.levi

include S in
/-- The exact effective quotient exponent follows from the literal type B
norm-kernel stability and lower geometric central intersection. -/
theorem rational_effective_quotient_exponent_two :
    letI := effectiveKernel_normal_of_le_normalizer
      (M Frob.toMonoidHom P.levi) (L Frob.toMonoidHom P.levi)
      (L_le_M Frob.toMonoidHom P.levi)
      (rational_le_normalizer Frob.toMonoidHom (pairedLevi P.levi) P.levi
        (paired_le_Levi_normalizer P.levi))
    ∀ q : M Frob.toMonoidHom P.levi ⧸
      effectiveKernel (M Frob.toMonoidHom P.levi) (L Frob.toMonoidHom P.levi), q ^ 2 = 1 :=
  effective_quotient_exponent_two Frob (SpinSubgroup n Kbar Nbar) P.levi
    (geometricSpin_frobenius_stable n p f F Kbar N Nbar Frob S)
    P.central_decomposition P.central_spin_square P.intersection.le

variable {E : Type} [Group E]
variable (field : E →* MulAut (SpecialClifford n Kbar))
variable (commutes : ∀ e x, Frob (field e x) = field e (Frob x))
variable (field_stable : ∀ e, P.levi.map (field e).toMonoidHom = P.levi)

include field_stable in
/-- Preservation uses a specified action on this same geometric Clifford
overgroup.  Extending an intended finite field action remains explicit U. -/
theorem rational_field_preserves_chain (e : E) :
    (L0 Frob.toMonoidHom P.levi).map
      (fixedPointAction Frob.toMonoidHom field commutes e).toMonoidHom =
        L0 Frob.toMonoidHom P.levi ∧
    (L Frob.toMonoidHom P.levi).map
      (fixedPointAction Frob.toMonoidHom field commutes e).toMonoidHom =
        L Frob.toMonoidHom P.levi ∧
    (M Frob.toMonoidHom P.levi).map
      (fixedPointAction Frob.toMonoidHom field commutes e).toMonoidHom =
        M Frob.toMonoidHom P.levi :=
  field_preserves_chain Frob.toMonoidHom field commutes P.levi field_stable e

end Clifford

end ModularRep.PaperProofs.TypeBRegularLeviCliffordBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
