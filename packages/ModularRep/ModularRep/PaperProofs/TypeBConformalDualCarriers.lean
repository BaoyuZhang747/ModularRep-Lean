import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finite.Prod
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Tactic.Ring

/-!
# Literal conformal symplectic dual carriers for Type B

The underlying vector space and alternating form are fixed here.  A conformal
symplectic element is an actual linear automorphism together with its unit
multiplier and the form-preservation equation.  Scalar translation and the
multiplier calculation used in manuscript Lemma 4.2 are definitions and
theorems on this carrier, not supplied abstract operations.

Feng--C. Li--Zhang, J. Algebra 604 (2022), Section 3.1, pp. 541--542,
identifies the dual finite groups of the special Clifford and Spin groups
with CSp and PCSp, respectively.  The source identification with a chosen
finite field and its rational reductive-group realization remains an E1
input at the consumer.  No rational Lusztig series, block label, or character
correspondence is assumed here.  In particular, PCSp is the quotient by all
nonzero scalars; it is not silently replaced by PSp.
-/

noncomputable section

open scoped BigOperators

namespace ModularRep.PaperProofs.TypeBConformalDualCarriers

universe u

variable (F : Type u) [Field F] (n : ℕ)

/-- The fixed `2n`-dimensional space in the dual conformal symplectic model. -/
abbrev SymplecticSpace := (Fin n → F) × (Fin n → F)

/-- The standard alternating form, in two coordinate blocks. -/
def symplecticForm (v w : SymplecticSpace F n) : F :=
  ∑ i : Fin n, (v.1 i * w.2 i - v.2 i * w.1 i)

theorem symplecticForm_self (v : SymplecticSpace F n) :
    symplecticForm F n v v = 0 := by
  simp [symplecticForm, mul_comm]

theorem symplecticForm_smul_smul (a b : F)
    (v w : SymplecticSpace F n) :
    symplecticForm F n (a • v) (b • w) =
      (a * b) * symplecticForm F n v w := by
  simp only [symplecticForm, Prod.smul_fst, Prod.smul_snd,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- Literal conformal linear maps, retaining the multiplier in their data. -/
def conformalSubgroup :
    Subgroup ((SymplecticSpace F n ≃ₗ[F] SymplecticSpace F n) × Fˣ) where
  carrier := {g | ∀ v w, symplecticForm F n (g.1 v) (g.1 w) =
    (g.2 : F) * symplecticForm F n v w}
  one_mem' := by
    intro v w
    simp
  mul_mem' := by
    intro g h hg hh v w
    change symplecticForm F n (g.1 (h.1 v)) (g.1 (h.1 w)) =
      ((g.2 : F) * (h.2 : F)) * symplecticForm F n v w
    rw [hg, hh, mul_assoc]
  inv_mem' := by
    intro g hg v w
    have h := hg (g.1.symm v) (g.1.symm w)
    simp only [LinearEquiv.apply_symm_apply] at h
    change symplecticForm F n (g.1.symm v) (g.1.symm w) =
      (↑g.2⁻¹ : F) * symplecticForm F n v w
    rw [h]
    simp

/-- The actual conformal symplectic group of the fixed alternating space. -/
abbrev CSp := conformalSubgroup F n

/-- Finiteness follows from the actual functions and scalar values. -/
instance finiteCSp [Finite F] : Finite (CSp F n) := by
  apply Finite.of_injective
    (fun s : CSp F n => ((fun v => s.1.1 v), (s.1.2 : F)))
  intro s t h
  apply Subtype.ext
  apply Prod.ext
  · apply LinearEquiv.ext
    intro v
    exact congrFun (congrArg Prod.fst h) v
  · exact Units.ext (congrArg Prod.snd h)

/-- The conformal multiplier is the second coordinate homomorphism. -/
def multiplier : CSp F n →* Fˣ :=
  (MonoidHom.snd _ _).comp (conformalSubgroup F n).subtype

@[simp]
theorem multiplier_apply (s : CSp F n) : multiplier F n s = s.1.2 := rfl

/-- The actual linear automorphism underlying a conformal element. -/
def linearPart : CSp F n →*
    (SymplecticSpace F n ≃ₗ[F] SymplecticSpace F n) :=
  (MonoidHom.fst _ _).comp (conformalSubgroup F n).subtype

@[simp]
theorem linearPart_apply (s : CSp F n) : linearPart F n s = s.1.1 := rfl

theorem preserves_form (s : CSp F n) (v w : SymplecticSpace F n) :
    symplecticForm F n (linearPart F n s v) (linearPart F n s w) =
      (multiplier F n s : F) * symplecticForm F n v w := s.2 v w

/-- Scalar multiplication by `z` has multiplier `z²`. -/
def scalar : Fˣ →* CSp F n where
  toFun z := ⟨(LinearEquiv.smulOfUnit z, z ^ 2), by
    intro v w
    change symplecticForm F n ((z : F) • v) ((z : F) • w) =
      ((z ^ 2 : Fˣ) : F) * symplecticForm F n v w
    simpa [pow_two] using symplecticForm_smul_smul F n (z : F) (z : F) v w⟩
  map_one' := by
    apply Subtype.ext
    apply Prod.ext
    · apply LinearEquiv.ext
      intro v
      change (1 : F) • v = v
      exact one_smul F v
    · simp
  map_mul' z t := by
    apply Subtype.ext
    apply Prod.ext
    · apply LinearEquiv.ext
      intro v
      change ((z : F) * (t : F)) • v = (z : F) • ((t : F) • v)
      exact mul_smul (z : F) (t : F) v
    · exact mul_pow z t 2

@[simp]
theorem multiplier_scalar (z : Fˣ) : multiplier F n (scalar F n z) = z ^ 2 := rfl

@[simp]
theorem linearPart_scalar_apply (z : Fˣ) (v : SymplecticSpace F n) :
    linearPart F n (scalar F n z) v = (z : F) • v := rfl

theorem scalar_commute (z : Fˣ) (s : CSp F n) :
    scalar F n z * s = s * scalar F n z := by
  apply Subtype.ext
  apply Prod.ext
  · apply LinearEquiv.ext
    intro v
    change (z : F) • s.1.1 v = s.1.1 ((z : F) • v)
    exact (s.1.1.map_smul (z : F) v).symm
  · exact mul_comm (z ^ 2) s.1.2

theorem scalar_central (z : Fˣ) :
    scalar F n z ∈ Subgroup.center (CSp F n) := by
  rw [Subgroup.mem_center_iff]
  intro s
  exact (scalar_commute F n z s).symm

/-- Positive rank ensures that different field scalars give different maps. -/
theorem scalar_injective (hn : 0 < n) : Function.Injective (scalar F n) := by
  intro z t h
  let v : SymplecticSpace F n := (fun _ => 1, fun _ => 0)
  have hv := congrArg
    (fun s : CSp F n => (linearPart F n s v).1 ⟨0, hn⟩) h
  change (z : F) * 1 = (t : F) * 1 at hv
  apply Units.ext
  simpa using hv

/-- Scalar translation of an actual dual-group element. -/
def translate (z : Fˣ) (s : CSp F n) : CSp F n := scalar F n z * s

theorem multiplier_translate (z : Fˣ) (s : CSp F n) :
    multiplier F n (translate F n z s) = z ^ 2 * multiplier F n s := by
  rw [translate, map_mul, multiplier_scalar]

/-- Conjugacy invariance of the actual conformal multiplier. -/
theorem multiplier_eq_of_isConj {s t : CSp F n} (h : IsConj s t) :
    multiplier F n s = multiplier F n t :=
  isConj_iff_eq.mp ((multiplier F n).map_isConj h)

/-- The full scalar subgroup, used for the rational projective conformal model. -/
def scalarSubgroup : Subgroup (CSp F n) := (scalar F n).range

instance scalarSubgroup_normal : (scalarSubgroup F n).Normal where
  conj_mem s hs g := by
    obtain ⟨z, rfl⟩ := hs
    change g * scalar F n z * g⁻¹ ∈ (scalar F n).range
    rw [← scalar_commute F n z g, mul_inv_cancel_right]
    exact ⟨z, rfl⟩

/-- Projective conformal symplectic group: quotient by every nonzero scalar. -/
abbrev PCSp := CSp F n ⧸ scalarSubgroup F n

end ModularRep.PaperProofs.TypeBConformalDualCarriers


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
