import ModularRep.PaperProofs.TypeBConformalDualCarriers
import ModularRep.PaperProofs.TypeBTwoCommon

/-!
# Odd-order lifts in the literal rank-three projective dual group

The symplectic group is the multiplier kernel in the fixed conformal model.
Its projective image is a subgroup of the quotient by all scalar units.
Odd projective order forces the multiplier to be a square, so every such
element belongs to that image.  In characteristic different from two the
range-restricted projection has exactly the central scalar kernel ±1.
The checked central-double-cover theorem then supplies its unique odd-order
lift.  No identification of the full projective conformal group with the
projective symplectic subgroup is used.
-/

noncomputable section

set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRankThreeNonprincipalDualLift

open TypeBConformalDualCarriers

universe u

variable (F : Type u) [Field F]

/-- The symplectic subgroup of the literal rank-three conformal group. -/
abbrev Sp := (multiplier F 3).ker

/-- Projection onto the full scalar quotient. -/
def projectiveProjection : CSp F 3 →* PCSp F 3 :=
  QuotientGroup.mk' (scalarSubgroup F 3)

/-- Restriction of the scalar quotient map to the multiplier kernel. -/
def symplecticProjection : Sp F →* PCSp F 3 :=
  (projectiveProjection F).comp (multiplier F 3).ker.subtype

/-- The actual projective symplectic subgroup of the conformal quotient. -/
def projectiveSymplecticSubgroup : Subgroup (PCSp F 3) :=
  (symplecticProjection F).range

/-- The image carrier, retaining its inclusion in the full scalar quotient. -/
abbrev PSp := projectiveSymplecticSubgroup F

/-- The symplectic projection with its codomain restricted to its image. -/
def projectionToPSp : Sp F →* PSp F :=
  (symplecticProjection F).rangeRestrict

@[simp]
theorem projectiveProjection_scalar (z : Fˣ) :
    projectiveProjection F (scalar F 3 z) = 1 :=
  (QuotientGroup.eq_one_iff _).2 ⟨z, rfl⟩

/-- The actual negative scalar map belongs to the multiplier kernel. -/
def negativeIdentity : Sp F :=
  ⟨scalar F 3 (-1), by
    change multiplier F 3 (scalar F 3 (-1)) = 1
    rw [multiplier_scalar, neg_one_sq]⟩

theorem negativeIdentity_ne_one (htwo : (2 : F) ≠ 0) :
    negativeIdentity F ≠ 1 := by
  intro h
  have hscalar : scalar F 3 (-1) = scalar F 3 1 := by
    have hvalue := congrArg (fun x : Sp F => (x : CSp F 3)) h
    change scalar F 3 (-1) = (1 : CSp F 3) at hvalue
    rw [map_one]
    exact hvalue
  have hunit : (-1 : Fˣ) = 1 :=
    scalar_injective F 3 (by decide) hscalar
  have hfield : (-1 : F) = 1 := congrArg (fun z : Fˣ => (z : F)) hunit
  apply htwo
  calc
    (2 : F) = 1 + 1 := by norm_num
    _ = -1 + 1 := congrArg (fun t : F => t + 1) hfield.symm
    _ = 0 := neg_add_cancel 1

theorem negativeIdentity_sq : negativeIdentity F ^ 2 = 1 := by
  apply Subtype.ext
  change (scalar F 3 (-1)) ^ 2 = 1
  rw [← map_pow, neg_one_sq, map_one]

theorem negativeIdentity_central :
    negativeIdentity F ∈ Subgroup.center (Sp F) := by
  rw [Subgroup.mem_center_iff]
  intro x
  apply Subtype.ext
  change (x : CSp F 3) * scalar F 3 (-1) =
    scalar F 3 (-1) * (x : CSp F 3)
  exact (scalar_commute F 3 (-1) x.val).symm

theorem symplecticProjection_eq_one_iff (x : Sp F) :
    symplecticProjection F x = 1 ↔
      x = 1 ∨ x = negativeIdentity F := by
  constructor
  · intro hx
    have hxscalar : x.val ∈ scalarSubgroup F 3 :=
      (QuotientGroup.eq_one_iff x.val).1 hx
    obtain ⟨z, hz⟩ := hxscalar
    have hzsq : z ^ 2 = (1 : Fˣ) ^ 2 := by
      rw [one_pow]
      calc
        z ^ 2 = multiplier F 3 (scalar F 3 z) := rfl
        _ = multiplier F 3 x.val := congrArg (multiplier F 3) hz
        _ = 1 := x.property
    rcases Units.eq_or_eq_neg_of_sq_eq_sq z 1 hzsq with hzpos | hzneg
    · left
      apply Subtype.ext
      calc
        x.val = scalar F 3 z := hz.symm
        _ = 1 := by rw [hzpos, map_one]
    · right
      apply Subtype.ext
      change x.val = scalar F 3 (-1)
      simpa only [hzneg] using hz.symm
  · rintro (rfl | rfl)
    · exact (symplecticProjection F).map_one
    · exact projectiveProjection_scalar F (-1)

/-- Every lift has order dividing twice the order of its projective image. -/
theorem orderOf_dvd_twice_projective_order (x : Sp F) :
    orderOf x ∣ 2 * orderOf (symplecticProjection F x) := by
  have hprojection : symplecticProjection F
      (x ^ orderOf (symplecticProjection F x)) = 1 := by
    rw [map_pow, pow_orderOf_eq_one]
  have hsquare : (x ^ orderOf (symplecticProjection F x)) ^ 2 = 1 := by
    rcases (symplecticProjection_eq_one_iff F _).1 hprojection with h | h
    · rw [h, one_pow]
    · rw [h, negativeIdentity_sq]
  apply orderOf_dvd_of_pow_eq_one
  rw [Nat.mul_comm 2 (orderOf (symplecticProjection F x)), pow_mul]
  exact hsquare

/-- Prime-to-order in the projective image passes to every lift away from two. -/
theorem coprime_orderOf_of_projective_order (p : ℕ) (x : Sp F)
    (hpTwo : p.Coprime 2)
    (hpProjection : p.Coprime (orderOf (symplecticProjection F x))) :
    p.Coprime (orderOf x) :=
  Nat.Coprime.of_dvd_right (orderOf_dvd_twice_projective_order F x)
    (Nat.coprime_mul_iff_right.mpr ⟨hpTwo, hpProjection⟩)

/-- The central double cover is proved on the projective image carrier. -/
def centralDoubleCover (htwo : (2 : F) ≠ 0) :
    TypeBTwoCommon.CentralDoubleCover (Ghat := Sp F) (G := PSp F) where
  projection := projectionToPSp F
  surjective := (symplecticProjection F).rangeRestrict_surjective
  kernelElement := negativeIdentity F
  kernelElement_ne_one := negativeIdentity_ne_one F htwo
  kernelElement_sq := negativeIdentity_sq F
  kernelElement_central := negativeIdentity_central F
  projection_eq_one_iff x := by
    have hprojection : projectionToPSp F x = 1 ↔
        symplecticProjection F x = 1 := by
      constructor
      · intro h
        exact congrArg (fun t : PSp F => (t : PCSp F 3)) h
      · intro h
        exact Subtype.ext h
    exact hprojection.trans (symplecticProjection_eq_one_iff F x)

/-- Odd order in the full scalar quotient forces a square multiplier. -/
theorem multiplier_square_of_odd_projective_order (g : CSp F 3)
    (hodd : Odd (orderOf (projectiveProjection F g))) :
    ∃ w : Fˣ, w ^ 2 = multiplier F 3 g := by
  obtain ⟨a, ha⟩ := hodd
  have hpower : projectiveProjection F (g ^ (2 * a + 1)) = 1 := by
    rw [map_pow, ← ha, pow_orderOf_eq_one]
  have hscalar : g ^ (2 * a + 1) ∈ scalarSubgroup F 3 :=
    (QuotientGroup.eq_one_iff _).1 hpower
  obtain ⟨z, hz⟩ := hscalar
  have hmultiplier : (multiplier F 3 g) ^ (2 * a + 1) = z ^ 2 := by
    calc
      (multiplier F 3 g) ^ (2 * a + 1) =
          multiplier F 3 (g ^ (2 * a + 1)) := (map_pow _ _ _).symm
      _ = multiplier F 3 (scalar F 3 z) :=
        congrArg (multiplier F 3) hz.symm
      _ = z ^ 2 := rfl
  refine ⟨z * ((multiplier F 3 g) ^ a)⁻¹, ?_⟩
  calc
    (z * ((multiplier F 3 g) ^ a)⁻¹) ^ 2 =
        z ^ 2 * (((multiplier F 3 g) ^ a) ^ 2)⁻¹ := by
      rw [mul_pow, inv_pow]
    _ = (multiplier F 3 g) ^ (2 * a + 1) *
        (((multiplier F 3 g) ^ a) ^ 2)⁻¹ := by rw [hmultiplier]
    _ = multiplier F 3 g := by
      rw [pow_add, pow_one, Nat.mul_comm 2 a, pow_mul]
      group

/-- Every odd-order element of PCSp lies in the literal symplectic image. -/
theorem odd_mem_projectiveSymplectic {s : PCSp F 3}
    (hs : Odd (orderOf s)) : s ∈ projectiveSymplecticSubgroup F := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (scalarSubgroup F 3) s
  have hodd : Odd (orderOf (projectiveProjection F g)) := by
    change Odd (orderOf ((QuotientGroup.mk' (scalarSubgroup F 3)) g))
    rwa [hg]
  obtain ⟨w, hw⟩ := multiplier_square_of_odd_projective_order F g hodd
  let lift : Sp F := ⟨scalar F 3 w⁻¹ * g, by
    change multiplier F 3 (scalar F 3 w⁻¹ * g) = 1
    rw [map_mul, multiplier_scalar, inv_pow, hw, inv_mul_cancel]⟩
  refine ⟨lift, ?_⟩
  change projectiveProjection F (scalar F 3 w⁻¹ * g) = s
  rw [map_mul, projectiveProjection_scalar, one_mul]
  exact hg

/-- Unique odd-order lifting from the full projective conformal carrier. -/
theorem existsUnique_odd_symplectic_lift (htwo : (2 : F) ≠ 0)
    {s : PCSp F 3} (hs : Odd (orderOf s)) :
    ∃! x : Sp F, symplecticProjection F x = s ∧ Odd (orderOf x) := by
  let image : PSp F := ⟨s, odd_mem_projectiveSymplectic F hs⟩
  have himage : Odd (orderOf image) := by
    simpa only [image, Subgroup.orderOf_mk] using hs
  obtain ⟨x, hx, unique⟩ :=
    (centralDoubleCover F htwo).existsUnique_odd_order_lift himage
  refine ⟨x, ⟨?_, hx.2⟩, ?_⟩
  · exact congrArg (fun t : PSp F => (t : PCSp F 3)) hx.1
  · intro y hy
    apply unique y
    exact ⟨Subtype.ext hy.1, hy.2⟩

end ModularRep.PaperProofs.TypeBRankThreeNonprincipalDualLift


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
