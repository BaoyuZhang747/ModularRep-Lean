import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Logic.Equiv.Basic

/-!
# Transporting equivalences between fibres

This file formalises the abstract orbit argument used when local bijections are combined
over a group orbit.  Equivariant maps `pX : X → I` and `pY : Y → I` make `X` and `Y`
families over the same `A`-set.  A chosen transporter from a base point to every point of one
orbit carries a stabiliser-equivariant equivalence of the base fibres to an equivalence of the
total spaces.  The resulting equivalence preserves the projection to `I` and is
`A`-equivariant.

The theorem is purely about group actions and dependent fibres.  It does not construct the
character-theoretic local bijections to which the manuscript applies this argument.
-/

namespace Formalisation

section FibreTransport

variable {A I X Y : Type*} [Group A]
variable [MulAction A I] [MulAction A X] [MulAction A Y]

/-- The fibre of a map over a point. -/
abbrev Fibre (p : X → I) (i : I) := {x : X // p x = i}

/-- An equivariant projection carries the action of a group element to an equivalence between
the corresponding fibres. -/
def actFibre (p : X → I) (hp : ∀ (a : A) (x : X), p (a • x) = a • p x)
    (a : A) (i : I) : Fibre p i ≃ Fibre p (a • i) where
  toFun x := ⟨a • x.1, by rw [hp, x.2]⟩
  invFun y := ⟨a⁻¹ • y.1, by rw [hp, y.2]; simp⟩
  left_inv x := by
    ext
    simp
  right_inv y := by
    ext
    simp

/-- A chosen transporter `t i` with `t i • i₀ = i` identifies the base fibre with the fibre
over `i`. -/
def fibreFromBase (p : X → I) (hp : ∀ (a : A) (x : X), p (a • x) = a • p x)
    (i₀ : I) (t : I → A) (ht : ∀ i, t i • i₀ = i) (i : I) :
    Fibre p i₀ ≃ Fibre p i where
  toFun x := ⟨t i • x.1, by rw [hp, x.2, ht]⟩
  invFun y := ⟨(t i)⁻¹ • y.1, by
    calc
      p ((t i)⁻¹ • y.1) = (t i)⁻¹ • p y.1 := hp (t i)⁻¹ y.1
      _ = (t i)⁻¹ • i := congrArg ((t i)⁻¹ • ·) y.2
      _ = (t i)⁻¹ • (t i • i₀) := congrArg ((t i)⁻¹ • ·) (ht i).symm
      _ = i₀ := by simp⟩
  left_inv x := by
    ext
    simp
  right_inv y := by
    ext
    simp

@[simp]
theorem fibreFromBase_coe
    (p : X → I) (hp : ∀ (a : A) (x : X), p (a • x) = a • p x)
    (i₀ : I) (t : I → A) (ht : ∀ i, t i • i₀ = i) (i : I) (x : Fibre p i₀) :
    (fibreFromBase p hp i₀ t ht i x).1 = t i • x.1 := by
  rfl

@[simp]
theorem fibreFromBase_symm_coe
    (p : X → I) (hp : ∀ (a : A) (x : X), p (a • x) = a • p x)
    (i₀ : I) (t : I → A) (ht : ∀ i, t i • i₀ = i) (i : I) (x : Fibre p i) :
    ((fibreFromBase p hp i₀ t ht i).symm x).1 = (t i)⁻¹ • x.1 := by
  rfl

/-- An element fixing the base point acts on the fibre over that point. -/
def stabilizerFibreEquiv
    (p : X → I) (hp : ∀ (a : A) (x : X), p (a • x) = a • p x)
    (i₀ : I) (a : A) (ha : a • i₀ = i₀) : Fibre p i₀ ≃ Fibre p i₀ where
  toFun x := ⟨a • x.1, by rw [hp, x.2, ha]⟩
  invFun y := ⟨a⁻¹ • y.1, by
    calc
      p (a⁻¹ • y.1) = a⁻¹ • p y.1 := hp a⁻¹ y.1
      _ = a⁻¹ • i₀ := congrArg (a⁻¹ • ·) y.2
      _ = a⁻¹ • (a • i₀) := congrArg (a⁻¹ • ·) ha.symm
      _ = i₀ := by simp⟩
  left_inv x := by
    ext
    simp
  right_inv y := by
    ext
    simp

@[simp]
theorem stabilizerFibreEquiv_coe
    (p : X → I) (hp : ∀ (a : A) (x : X), p (a • x) = a • p x)
    (i₀ : I) (a : A) (ha : a • i₀ = i₀) (x : Fibre p i₀) :
    (stabilizerFibreEquiv p hp i₀ a ha x).1 = a • x.1 := by
  rfl

/-- Transport an equivalence of the fibres over `i₀` to the fibre over `i`. -/
def transportedFibreEquiv
    (pX : X → I) (pY : Y → I)
    (hpX : ∀ (a : A) (x : X), pX (a • x) = a • pX x)
    (hpY : ∀ (a : A) (y : Y), pY (a • y) = a • pY y)
    (i₀ : I) (t : I → A) (ht : ∀ i, t i • i₀ = i)
    (e₀ : Fibre pX i₀ ≃ Fibre pY i₀) (i : I) :
    Fibre pX i ≃ Fibre pY i :=
  (fibreFromBase pX hpX i₀ t ht i).symm.trans
    (e₀.trans (fibreFromBase pY hpY i₀ t ht i))

@[simp]
theorem transportedFibreEquiv_coe
    (pX : X → I) (pY : Y → I)
    (hpX : ∀ (a : A) (x : X), pX (a • x) = a • pX x)
    (hpY : ∀ (a : A) (y : Y), pY (a • y) = a • pY y)
    (i₀ : I) (t : I → A) (ht : ∀ i, t i • i₀ = i)
    (e₀ : Fibre pX i₀ ≃ Fibre pY i₀) (i : I) (x : Fibre pX i) :
    (transportedFibreEquiv pX pY hpX hpY i₀ t ht e₀ i x).1 =
      t i • (e₀ ((fibreFromBase pX hpX i₀ t ht i).symm x)).1 := by
  rfl

/-- The equivalences transported to all fibres combine into an equivalence of the total
spaces. -/
def transportedEquiv
    (pX : X → I) (pY : Y → I)
    (hpX : ∀ (a : A) (x : X), pX (a • x) = a • pX x)
    (hpY : ∀ (a : A) (y : Y), pY (a • y) = a • pY y)
    (i₀ : I) (t : I → A) (ht : ∀ i, t i • i₀ = i)
    (e₀ : Fibre pX i₀ ≃ Fibre pY i₀) : X ≃ Y :=
  Equiv.ofFiberEquiv (transportedFibreEquiv pX pY hpX hpY i₀ t ht e₀)

theorem transportedEquiv_apply
    (pX : X → I) (pY : Y → I)
    (hpX : ∀ (a : A) (x : X), pX (a • x) = a • pX x)
    (hpY : ∀ (a : A) (y : Y), pY (a • y) = a • pY y)
    (i₀ : I) (t : I → A) (ht : ∀ i, t i • i₀ = i)
    (e₀ : Fibre pX i₀ ≃ Fibre pY i₀) (x : X) :
    transportedEquiv pX pY hpX hpY i₀ t ht e₀ x =
      (transportedFibreEquiv pX pY hpX hpY i₀ t ht e₀ (pX x)) ⟨x, rfl⟩ := by
  rfl

theorem transportedEquiv_formula
    (pX : X → I) (pY : Y → I)
    (hpX : ∀ (a : A) (x : X), pX (a • x) = a • pX x)
    (hpY : ∀ (a : A) (y : Y), pY (a • y) = a • pY y)
    (i₀ : I) (t : I → A) (ht : ∀ i, t i • i₀ = i)
    (e₀ : Fibre pX i₀ ≃ Fibre pY i₀) (x : X) :
    transportedEquiv pX pY hpX hpY i₀ t ht e₀ x =
      t (pX x) •
        (e₀ ((fibreFromBase pX hpX i₀ t ht (pX x)).symm ⟨x, rfl⟩)).1 := by
  rfl

/-- If the equivalence over the base point commutes with every element of its stabiliser,
then its transport to the whole orbit commutes with every element of `A`. -/
theorem transportedEquiv_equivariant
    (pX : X → I) (pY : Y → I)
    (hpX : ∀ (a : A) (x : X), pX (a • x) = a • pX x)
    (hpY : ∀ (a : A) (y : Y), pY (a • y) = a • pY y)
    (i₀ : I) (t : I → A) (ht : ∀ i, t i • i₀ = i)
    (e₀ : Fibre pX i₀ ≃ Fibre pY i₀)
    (he₀ : ∀ (h : A) (hh : h • i₀ = i₀) (x : Fibre pX i₀),
      e₀ (stabilizerFibreEquiv pX hpX i₀ h hh x) =
        stabilizerFibreEquiv pY hpY i₀ h hh (e₀ x))
    (a : A) (x : X) :
    transportedEquiv pX pY hpX hpY i₀ t ht e₀ (a • x) =
      a • transportedEquiv pX pY hpX hpY i₀ t ht e₀ x := by
  let pull : X → Fibre pX i₀ := fun z ↦
    (fibreFromBase pX hpX i₀ t ht (pX z)).symm ⟨z, rfl⟩
  let h : A := (t (pX (a • x)))⁻¹ * a * t (pX x)
  have hh : h • i₀ = i₀ := by
    calc
      h • i₀ = (t (pX (a • x)))⁻¹ • (a • (t (pX x) • i₀)) := by
        simp only [h, mul_smul]
      _ = (t (pX (a • x)))⁻¹ • (a • pX x) := by rw [ht]
      _ = (t (pX (a • x)))⁻¹ • pX (a • x) := by rw [hpX]
      _ = (t (pX (a • x)))⁻¹ • (t (pX (a • x)) • i₀) := by rw [ht]
      _ = i₀ := by simp
  have hpull : pull (a • x) = stabilizerFibreEquiv pX hpX i₀ h hh (pull x) := by
    apply Subtype.ext
    simp only [pull, fibreFromBase_symm_coe, stabilizerFibreEquiv_coe]
    simp [h, mul_smul]
  rw [transportedEquiv_formula, transportedEquiv_formula]
  change t (pX (a • x)) • (e₀ (pull (a • x))).1 =
    a • (t (pX x) • (e₀ (pull x)).1)
  calc
    t (pX (a • x)) • (e₀ (pull (a • x))).1 =
        t (pX (a • x)) •
          (e₀ (stabilizerFibreEquiv pX hpX i₀ h hh (pull x))).1 := by rw [hpull]
    _ = t (pX (a • x)) •
          (stabilizerFibreEquiv pY hpY i₀ h hh (e₀ (pull x))).1 := by
        rw [he₀]
    _ = t (pX (a • x)) • (h • (e₀ (pull x)).1) := by
        rw [stabilizerFibreEquiv_coe]
    _ = a • (t (pX x) • (e₀ (pull x)).1) := by
        simp [h, mul_smul]

/-- The transported equivalence does not depend on the chosen family of transporters.  This
is the well-definedness assertion behind the usual phrase "transport along the orbit". -/
theorem transportedEquiv_independent_of_transporter
    (pX : X → I) (pY : Y → I)
    (hpX : ∀ (a : A) (x : X), pX (a • x) = a • pX x)
    (hpY : ∀ (a : A) (y : Y), pY (a • y) = a • pY y)
    (i₀ : I) (t u : I → A)
    (ht : ∀ i, t i • i₀ = i) (hu : ∀ i, u i • i₀ = i)
    (e₀ : Fibre pX i₀ ≃ Fibre pY i₀)
    (he₀ : ∀ (h : A) (hh : h • i₀ = i₀) (x : Fibre pX i₀),
      e₀ (stabilizerFibreEquiv pX hpX i₀ h hh x) =
        stabilizerFibreEquiv pY hpY i₀ h hh (e₀ x)) :
    transportedEquiv pX pY hpX hpY i₀ t ht e₀ =
      transportedEquiv pX pY hpX hpY i₀ u hu e₀ := by
  ext x
  let pullT : Fibre pX i₀ :=
    (fibreFromBase pX hpX i₀ t ht (pX x)).symm ⟨x, rfl⟩
  let pullU : Fibre pX i₀ :=
    (fibreFromBase pX hpX i₀ u hu (pX x)).symm ⟨x, rfl⟩
  let h : A := (u (pX x))⁻¹ * t (pX x)
  have hh : h • i₀ = i₀ := by
    calc
      h • i₀ = (u (pX x))⁻¹ • (t (pX x) • i₀) := by
        simp only [h, mul_smul]
      _ = (u (pX x))⁻¹ • pX x := by rw [ht]
      _ = (u (pX x))⁻¹ • (u (pX x) • i₀) := by rw [hu]
      _ = i₀ := by simp
  have hpull : pullU = stabilizerFibreEquiv pX hpX i₀ h hh pullT := by
    apply Subtype.ext
    simp only [pullU, pullT, fibreFromBase_symm_coe, stabilizerFibreEquiv_coe]
    simp [h, mul_smul]
  rw [transportedEquiv_formula, transportedEquiv_formula]
  change t (pX x) • (e₀ pullT).1 = u (pX x) • (e₀ pullU).1
  symm
  calc
    u (pX x) • (e₀ pullU).1 =
        u (pX x) • (e₀ (stabilizerFibreEquiv pX hpX i₀ h hh pullT)).1 := by
      rw [hpull]
    _ = u (pX x) •
        (stabilizerFibreEquiv pY hpY i₀ h hh (e₀ pullT)).1 := by
      rw [he₀]
    _ = u (pX x) • (h • (e₀ pullT).1) := by
      rw [stabilizerFibreEquiv_coe]
    _ = t (pX x) • (e₀ pullT).1 := by
      simp [h, mul_smul]

/-- The resulting equivalence preserves the point of the base over which an element lies. -/
theorem transportedEquiv_preserves_base
    (pX : X → I) (pY : Y → I)
    (hpX : ∀ (a : A) (x : X), pX (a • x) = a • pX x)
    (hpY : ∀ (a : A) (y : Y), pY (a • y) = a • pY y)
    (i₀ : I) (t : I → A) (ht : ∀ i, t i • i₀ = i)
    (e₀ : Fibre pX i₀ ≃ Fibre pY i₀) (x : X) :
    pY (transportedEquiv pX pY hpX hpY i₀ t ht e₀ x) = pX x :=
  Equiv.ofFiberEquiv_map
    (transportedFibreEquiv pX pY hpX hpY i₀ t ht e₀) x

end FibreTransport

end Formalisation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
