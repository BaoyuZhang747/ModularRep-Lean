import ModularRep.PaperProofs.TypeBRegularLeviRationalCarriers
import Mathlib.Tactic.Group

/-!
# Rational diagonal products from geometric decomposition and Levi Lang

The factors in a geometric central decomposition of a fixed point need
not be fixed. Their common defect lies in the given Levi. A single Lang
solution in that Levi corrects the central factor, yielding a rational
paired-Levi factor and a rational original-group factor.

The Lang source is the one-variable consequence of Malle--Testerman
Theorem 21.7 on the same connected Levi and Steinberg restriction. Its
algebraic applicability and point-carrier identification remain explicit
source obligations. No rational product or bound on the centre is input.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRankThreeJordanDiagonalProduct

open TypeBRegularLeviRationalCarriers
open scoped Pointwise

variable {A : Type*} [Group A]
variable (Frob : MulAut A) (Gbar Lbar : Subgroup A)

/-- The original Levi is stable, and the indicated Lang map is onto it. -/
structure LeviLangSource : Prop where
  stable : ∀ l ∈ Lbar, Frob l ∈ Lbar
  solve : ∀ d : Lbar, ∃ l : Lbar,
    Frob (l : A) * (l : A)⁻¹ = (d : A)

variable (Gstable : ∀ g ∈ Gbar, Frob g ∈ Gbar)
variable (levi_le_G : Lbar ≤ Gbar)
variable (decomposition : ∀ x : A,
  ∃ g ∈ Gbar, ∃ z ∈ Subgroup.center A, x = g * z)
variable (intersection : pairedLevi Lbar ⊓ Gbar ≤ Lbar)
variable (lang : LeviLangSource Frob Lbar)

include Gstable levi_le_G decomposition intersection lang in
/-- Every original fixed point is a product of an original rational-group
element and an element of the SAME rational paired Levi. -/
theorem rational_product (x : fixedPoints Frob.toMonoidHom) :
    ∃ g : rationalSubgroup Frob.toMonoidHom Gbar,
      ∃ m : M Frob.toMonoidHom Lbar,
        x = (g : fixedPoints Frob.toMonoidHom) *
          (m : fixedPoints Frob.toMonoidHom) := by
  obtain ⟨g, hg, z, hz, hx⟩ := decomposition x.val
  have hfixed : Frob (g * z) = g * z := by
    rw [← hx]
    exact x.property
  have hF : Frob g * Frob z = g * z := by
    simpa only [map_mul] using hfixed
  let d : A := g⁻¹ * Frob g
  have hdG : d ∈ Gbar :=
    Gbar.mul_mem (Gbar.inv_mem hg) (Gstable g hg)
  have hdEq : d = z * (Frob z)⁻¹ := by
    calc
      d = g⁻¹ * (Frob g * Frob z) * (Frob z)⁻¹ := by
        dsimp [d]
        group
      _ = g⁻¹ * (g * z) * (Frob z)⁻¹ := by rw [hF]
      _ = z * (Frob z)⁻¹ := by group
  have hFzCentre : Frob z ∈ Subgroup.center A := by
    have h := Subgroup.mem_map_of_mem Frob.toMonoidHom hz
    rw [automorphism_center_map] at h
    exact h
  have hdCentre : d ∈ Subgroup.center A := by
    rw [hdEq]
    exact (Subgroup.center A).mul_mem hz
      ((Subgroup.center A).inv_mem hFzCentre)
  have hdL : d ∈ Lbar :=
    intersection ⟨center_le_paired Lbar hdCentre, hdG⟩
  obtain ⟨l, hl⟩ := lang.solve ⟨d, hdL⟩
  have hFl : Frob (l : A) = d * (l : A) := by
    calc
      Frob (l : A) = (Frob (l : A) * (l : A)⁻¹) * (l : A) := by group
      _ = d * (l : A) := by rw [hl]
  have hdl : d * (l : A) = (l : A) * d :=
    (Subgroup.mem_center_iff.mp hdCentre (l : A)).symm
  have hdFz : d * Frob z = z := by
    rw [hdEq]
    group
  have hmFixed : Frob ((l : A) * z) = (l : A) * z := by
    calc
      Frob ((l : A) * z) = Frob (l : A) * Frob z := Frob.map_mul _ _
      _ = (d * (l : A)) * Frob z := by rw [hFl]
      _ = ((l : A) * d) * Frob z := by rw [hdl]
      _ = (l : A) * (d * Frob z) := mul_assoc _ _ _
      _ = (l : A) * z := by rw [hdFz]
  have hmLevi : (l : A) * z ∈ pairedLevi Lbar :=
    (pairedLevi Lbar).mul_mem (Levi_le_paired Lbar l.property)
      (center_le_paired Lbar hz)
  let m : M Frob.toMonoidHom Lbar := ⟨⟨(l : A) * z, hmFixed⟩, hmLevi⟩
  let gFixed : fixedPoints Frob.toMonoidHom :=
    x * (m : fixedPoints Frob.toMonoidHom)⁻¹
  have hgValue : gFixed.val = g * (l : A)⁻¹ := by
    change x.val * ((l : A) * z)⁻¹ = g * (l : A)⁻¹
    rw [hx]
    group
  have hgRational : gFixed ∈ rationalSubgroup Frob.toMonoidHom Gbar := by
    change gFixed.val ∈ Gbar
    rw [hgValue]
    exact Gbar.mul_mem hg (Gbar.inv_mem (levi_le_G l.property))
  refine ⟨⟨gFixed, hgRational⟩, m, ?_⟩
  change x = (x * (m : fixedPoints Frob.toMonoidHom)⁻¹) *
    (m : fixedPoints Frob.toMonoidHom)
  group

include Gstable levi_le_G decomposition intersection lang in
/-- The product retains the original values in the geometric ambient group. -/
theorem rational_product_values (x : fixedPoints Frob.toMonoidHom) :
    ∃ g : rationalSubgroup Frob.toMonoidHom Gbar,
      ∃ m : M Frob.toMonoidHom Lbar, x.val = g.val.val * m.val.val := by
  obtain ⟨g, m, h⟩ :=
    rational_product Frob Gbar Lbar Gstable levi_le_G decomposition intersection lang x
  exact ⟨g, m, congrArg Subtype.val h⟩

include Gstable levi_le_G decomposition intersection lang in
/-- The literal rational set product is the whole fixed-point group. -/
theorem rational_product_univ :
    (rationalSubgroup Frob.toMonoidHom Gbar : Set (fixedPoints Frob.toMonoidHom)) *
      (M Frob.toMonoidHom Lbar : Set (fixedPoints Frob.toMonoidHom)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨g, m, h⟩ :=
    rational_product Frob Gbar Lbar Gstable levi_le_G decomposition intersection lang x
  exact Set.mem_mul.mpr ⟨g, g.property, m, m.property, h.symm⟩

include Gstable levi_le_G decomposition intersection lang in
theorem rational_sup_eq_top :
    rationalSubgroup Frob.toMonoidHom Gbar ⊔ M Frob.toMonoidHom Lbar = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨g, m, h⟩ :=
    rational_product Frob Gbar Lbar Gstable levi_le_G decomposition intersection lang x
  rw [h]
  exact (rationalSubgroup Frob.toMonoidHom Gbar ⊔ M Frob.toMonoidHom Lbar).mul_mem
    ((show rationalSubgroup Frob.toMonoidHom Gbar ≤
      rationalSubgroup Frob.toMonoidHom Gbar ⊔ M Frob.toMonoidHom Lbar from
        le_sup_left) g.property)
    ((show M Frob.toMonoidHom Lbar ≤
      rationalSubgroup Frob.toMonoidHom Gbar ⊔ M Frob.toMonoidHom Lbar from
        le_sup_right) m.property)

include levi_le_G intersection in
/-- The geometric intersection gives the exact rational intersection. -/
theorem rational_intersection :
    M Frob.toMonoidHom Lbar ⊓ rationalSubgroup Frob.toMonoidHom Gbar =
      L Frob.toMonoidHom Lbar := by
  ext x
  change (x.val ∈ pairedLevi Lbar ∧ x.val ∈ Gbar) ↔ x.val ∈ Lbar
  constructor
  · exact fun hx => intersection hx
  · intro hx
    exact ⟨Levi_le_paired Lbar hx, levi_le_G hx⟩

end ModularRep.PaperProofs.TypeBRankThreeJordanDiagonalProduct


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
