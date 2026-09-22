import ModularRep.PaperProofs.TypeBSpinBroueMichelCarriers
import ModularRep.PaperProofs.TypeBConformalDualFieldAction

/-!
# The actual field action on Spin rational-series indices

Positive coordinate Frobenius on PCSp acts on its actual conjugacy classes.
Both order guards are preserved, and forgetting the ell-prime guard is
equivariant. Per-series naturality therefore implies selected-union
stability in the consumer's inverse-pullback convention.

The naturality hypotheses refer to the one prescribed full rational family.
They do not authenticate an arbitrary family as Lusztig series. That exact
published-family and finite-point interpretation remains a source boundary.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBSpinRationalIndexAction

open ModularRep OrdinaryIrreducibleCharacter TypeBCliffordCarriers
open TypeBConformalDualCarriers TypeBConformalDualFieldAction
open TypeBSpinConlonBlockSourceInstantiation TypeBRationalSeriesSource
open TypeBSpinBroueMichelCarriers

variable {n p ell f : ℕ} {F K : Type} [Field F] [Field K]

def fullIndexMap (a : MulAut (PCSp F n)) (i : FullRationalIndex p n F) :
    FullRationalIndex p n F :=
  ⟨ConjClasses.map a.toMonoidHom i.val, by
    obtain ⟨g, hg, hp⟩ := i.property
    refine ⟨a g, ?_, ?_⟩
    · rw [← hg]; rfl
    · simpa only [a.orderOf_eq] using hp⟩

@[simp] theorem fullIndexMap_val (a : MulAut (PCSp F n))
    (i : FullRationalIndex p n F) :
    (fullIndexMap a i).val = ConjClasses.map a.toMonoidHom i.val := rfl

def rationalIndexMap (a : MulAut (PCSp F n)) (i : RationalIndex p ell n F) :
    RationalIndex p ell n F :=
  ⟨ConjClasses.map a.toMonoidHom i.val, by
    obtain ⟨g, hg, hp, he⟩ := i.property
    refine ⟨a g, ?_, ?_, ?_⟩
    · rw [← hg]; rfl
    · simpa only [a.orderOf_eq] using hp
    · simpa only [a.orderOf_eq] using he⟩

@[simp] theorem rationalIndexMap_val (a : MulAut (PCSp F n))
    (i : RationalIndex p ell n F) :
    (rationalIndexMap a i).val = ConjClasses.map a.toMonoidHom i.val := rfl

@[simp] theorem fullIndex_rationalIndexMap (a : MulAut (PCSp F n))
    (i : RationalIndex p ell n F) :
    fullIndex (rationalIndexMap a i) = fullIndexMap a (fullIndex i) := rfl

theorem fullIndexMap_one (i : FullRationalIndex p n F) : fullIndexMap 1 i = i := by
  apply Subtype.ext
  obtain ⟨g, hg, _⟩ := i.property
  rw [fullIndexMap_val, ← hg]
  rfl

theorem fullIndexMap_mul (a b : MulAut (PCSp F n)) (i : FullRationalIndex p n F) :
    fullIndexMap (a * b) i = fullIndexMap a (fullIndexMap b i) := by
  apply Subtype.ext
  obtain ⟨g, hg, _⟩ := i.property
  simp only [fullIndexMap_val, ← hg]
  rfl

theorem rationalIndexMap_one (i : RationalIndex p ell n F) : rationalIndexMap 1 i = i :=
  fullIndex_injective (fullIndexMap_one (fullIndex i))

theorem rationalIndexMap_mul (a b : MulAut (PCSp F n)) (i : RationalIndex p ell n F) :
    rationalIndexMap (a * b) i = rationalIndexMap a (rationalIndexMap b i) :=
  fullIndex_injective (fullIndexMap_mul a b (fullIndex i))

section Field

variable [Finite F] [CharP F p] (parameters : OddFieldParameters F p f)

def fullIndexFieldAction : MulAction (FieldGroup f) (FullRationalIndex p n F) where
  smul e i := fullIndexMap (pcspFieldAction F n parameters e) i
  one_smul i := by
    change fullIndexMap (pcspFieldAction F n parameters 1) i = i
    rw [map_one]
    exact fullIndexMap_one i
  mul_smul e d i := by
    change fullIndexMap (pcspFieldAction F n parameters (e * d)) i =
      fullIndexMap (pcspFieldAction F n parameters e)
        (fullIndexMap (pcspFieldAction F n parameters d) i)
    rw [map_mul]
    exact fullIndexMap_mul _ _ i

def rationalIndexFieldAction : MulAction (FieldGroup f) (RationalIndex p ell n F) where
  smul e i := rationalIndexMap (pcspFieldAction F n parameters e) i
  one_smul i := by
    change rationalIndexMap (pcspFieldAction F n parameters 1) i = i
    rw [map_one]
    exact rationalIndexMap_one i
  mul_smul e d i := by
    change rationalIndexMap (pcspFieldAction F n parameters (e * d)) i =
      rationalIndexMap (pcspFieldAction F n parameters e)
        (rationalIndexMap (pcspFieldAction F n parameters d) i)
    rw [map_mul]
    exact rationalIndexMap_mul _ _ i

theorem rationalIndexFieldAction_val (e : FieldGroup f) (i : RationalIndex p ell n F) :
    letI := rationalIndexFieldAction (n := n) (ell := ell) parameters
    (e • i).val = ConjClasses.map (pcspFieldAction F n parameters e).toMonoidHom i.val := rfl

theorem fullIndex_field (e : FieldGroup f) (i : RationalIndex p ell n F) :
    letI := fullIndexFieldAction (n := n) parameters
    letI := rationalIndexFieldAction (n := n) (ell := ell) parameters
    fullIndex (e • i) = e • fullIndex i := rfl

variable {N : NormSource n F}
    (fs : FieldActionSource n F p f parameters N)
    (S : RationalSeriesSource K (Spin n F N) (FullRationalIndex p n F))

/-- Same-series diagonal naturality implies the precise selected callback.
The actor is actual inverse regular conjugation, as in the frozen consumer. -/
theorem selected_diagonal_stable
    (natural : ∀ (g : SpecialClifford n F) (i : FullRationalIndex p n F)
      (chi : Irr K (Spin n F N)), chi ∈ S.rationalSeries i →
        twist K (Spin n F N) chi (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹)
          ∈ S.rationalSeries i)
    (g : SpecialClifford n F) (chi : Irr K (Spin n F N))
    (hchi : (selectedFamily (ell := ell) S).selectedSeries chi) :
    (selectedFamily (ell := ell) S).selectedSeries
      (twist K (Spin n F N) chi (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹)) := by
  obtain ⟨i, hi⟩ := hchi
  exact ⟨i, natural g (fullIndex i) chi hi⟩

/-- Positive PCSp transport matches inverse pullback of character values.
The selected callback is derived, not accepted as a second source premise. -/
theorem selected_field_stable
    (natural : ∀ (e : FieldGroup f) (i : FullRationalIndex p n F)
      (chi : Irr K (Spin n F N)), chi ∈ S.rationalSeries i →
        twist K (Spin n F N) chi (spinFieldAction n F fs e⁻¹)
          ∈ S.rationalSeries (fullIndexMap (pcspFieldAction F n parameters e) i))
    (e : FieldGroup f) (chi : Irr K (Spin n F N))
    (hchi : (selectedFamily (ell := ell) S).selectedSeries chi) :
    (selectedFamily (ell := ell) S).selectedSeries
      (twist K (Spin n F N) chi (spinFieldAction n F fs e⁻¹)) := by
  obtain ⟨i, hi⟩ := hchi
  exact ⟨rationalIndexMap (pcspFieldAction F n parameters e) i,
    natural e (fullIndex i) chi hi⟩

end Field

end ModularRep.PaperProofs.TypeBSpinRationalIndexAction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
