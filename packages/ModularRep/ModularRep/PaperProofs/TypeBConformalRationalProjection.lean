import ModularRep.PaperProofs.TypeBSpinRationalIndexAction
import ModularRep.PaperProofs.TypeBFLZCentralizerConjugacy

/-!
# The actual CSp-to-PCSp rational parameter projection

The map is the quotient by the full scalar subgroup. The order of an
image divides the original order, so a defining-prime regular CSp
parameter defines a full rational PCSp class. Conjugacy and the checked
coordinate field actions commute with this projection.

This is a K carrier construction. It does not assert semisimple lifting,
surjectivity on classes, a character restriction theorem, or a source
identification of any rational-series predicate. The FLZ §3.1 dual regular
embedding and its rational-point interpretation remain separate from
these literal finite group formulas.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBConformalRationalProjection

open TypeBConformalDualCarriers TypeBConformalDualFieldAction
open TypeBCliffordCarriers TypeBFLZLabelSource TypeBFLZCentralizerConjugacy
open TypeBSpinBroueMichelCarriers TypeBSpinRationalIndexAction

variable {F : Type} [Field F] {p n : ℕ}

/-- The actual quotient by all nonzero scalar maps. -/
def projection (F : Type) [Field F] (n : ℕ) : CSp F n →* PCSp F n :=
  QuotientGroup.mk' (scalarSubgroup F n)

/-- Coprimality descends because the image order divides the original order. -/
theorem projection_order_coprime (r : ℕ) (g : CSp F n)
    (hg : r.Coprime (orderOf g)) : r.Coprime (orderOf (projection F n g)) :=
  hg.of_dvd_right (orderOf_map_dvd (projection F n) g)

/-- A literal semisimple CSp parameter gives a full rational Spin-dual index. -/
def rationalProjection (s : SemisimpleParameter F p n) : FullRationalIndex p n F :=
  ⟨ConjClasses.mk (projection F n s.val), projection F n s.val, rfl,
    projection_order_coprime p s.val s.property⟩

@[simp] theorem rationalProjection_val (s : SemisimpleParameter F p n) :
    (rationalProjection s).val = ConjClasses.mk (projection F n s.val) := rfl

/-- Equality is exactly conjugacy of the actual projected elements. -/
theorem rationalProjection_eq_iff (s t : SemisimpleParameter F p n) :
    rationalProjection s = rationalProjection t ↔
      IsConj (projection F n s.val) (projection F n t.val) := by
  constructor
  · intro h
    exact ConjClasses.mk_eq_mk_iff_isConj.mp
      (congrArg (fun i : FullRationalIndex p n F => i.val) h)
  · intro h
    exact Subtype.ext (ConjClasses.mk_eq_mk_iff_isConj.mpr h)

theorem rationalProjection_eq_of_isConj (s t : SemisimpleParameter F p n)
    (h : IsConj s.val t.val) : rationalProjection s = rationalProjection t :=
  (rationalProjection_eq_iff s t).mpr ((projection F n).map_isConj h)

@[simp] theorem rationalProjection_conj (g : CSp F n)
    (s : SemisimpleParameter F p n) :
    rationalProjection (semisimpleConj g s) = rationalProjection s := by
  have h : IsConj s.val (semisimpleConj g s).val := isConj_iff.mpr ⟨g, rfl⟩
  exact rationalProjection_eq_of_isConj (semisimpleConj g s) s h.symm

/-- Restrict an actual CSp automorphism using preservation of element order. -/
def semisimpleMap (a : MulAut (CSp F n)) (s : SemisimpleParameter F p n) :
    SemisimpleParameter F p n :=
  ⟨a s.val, by
    rw [a.orderOf_eq]
    exact s.property⟩

@[simp] theorem semisimpleMap_val (a : MulAut (CSp F n))
    (s : SemisimpleParameter F p n) : (semisimpleMap a s).val = a s.val := rfl

theorem semisimpleMap_one (s : SemisimpleParameter F p n) :
    semisimpleMap 1 s = s := Subtype.ext rfl

theorem semisimpleMap_mul (a b : MulAut (CSp F n))
    (s : SemisimpleParameter F p n) :
    semisimpleMap (a * b) s = semisimpleMap a (semisimpleMap b s) := Subtype.ext rfl

/-- The arbitrary coordinate field automorphism commutes with the quotient map. -/
theorem projection_automorphism (sigma : F ≃+* F) (g : CSp F n) :
    projection F n (cspAutomorphism F n sigma g) =
      pcspAutomorphism F n sigma (projection F n g) :=
  (pcspAutomorphism_mk F n sigma g).symm

theorem rationalProjection_automorphism (sigma : F ≃+* F)
    (s : SemisimpleParameter F p n) :
    rationalProjection (semisimpleMap (cspAutomorphism F n sigma) s) =
      fullIndexMap (pcspAutomorphism F n sigma) (rationalProjection s) := by
  apply Subtype.ext
  change ConjClasses.mk (projection F n (cspAutomorphism F n sigma s.val)) =
    ConjClasses.mk (pcspAutomorphism F n sigma (projection F n s.val))
  exact congrArg ConjClasses.mk (projection_automorphism sigma s.val)

section Field

variable [Finite F] {f : ℕ} [CharP F p] (parameters : OddFieldParameters F p f)

/-- The same positive field element acts on the actual CSp parameter. -/
def semisimpleField (e : FieldGroup f) (s : SemisimpleParameter F p n) :
    SemisimpleParameter F p n :=
  semisimpleMap (cspFieldAction F n parameters e) s

@[simp] theorem semisimpleField_val (e : FieldGroup f)
    (s : SemisimpleParameter F p n) :
    (semisimpleField parameters e s).val = cspFieldAction F n parameters e s.val := rfl

theorem projection_field (e : FieldGroup f) (g : CSp F n) :
    projection F n (cspFieldAction F n parameters e g) =
      pcspFieldAction F n parameters e (projection F n g) :=
  (pcspFieldAction_mk F n parameters e g).symm

/-- Field compatibility on the exact full rational class, before action notation. -/
theorem rationalProjection_field (e : FieldGroup f) (s : SemisimpleParameter F p n) :
    rationalProjection (semisimpleField parameters e s) =
      fullIndexMap (pcspFieldAction F n parameters e) (rationalProjection s) := by
  apply Subtype.ext
  change ConjClasses.mk (projection F n (cspFieldAction F n parameters e s.val)) =
    ConjClasses.mk (pcspFieldAction F n parameters e (projection F n s.val))
  exact congrArg ConjClasses.mk (projection_field parameters e s.val)

/-- The identical square using the root's already constructed index action. -/
theorem rationalProjection_field_smul (e : FieldGroup f)
    (s : SemisimpleParameter F p n) :
    letI := fullIndexFieldAction (n := n) parameters
    rationalProjection (semisimpleField parameters e s) = e • rationalProjection s :=
  rationalProjection_field parameters e s

end Field

end ModularRep.PaperProofs.TypeBConformalRationalProjection


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
