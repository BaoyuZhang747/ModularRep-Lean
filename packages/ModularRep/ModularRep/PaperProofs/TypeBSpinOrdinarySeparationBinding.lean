import ModularRep.PaperProofs.TypeBSpinDiagonalNormSource
import ModularRep.PaperProofs.TypeBSpinEffectiveSourceBinding
import ModularRep.PaperProofs.TypeBFLZLabelSource

/-!
# Literal ordinary Spin separation and effective stabilizers

FLZ Theorem 3.10, p. 546, separates the field transform of an ordinary
Spin character from a nontrivial regular diagonal transform. The source
below states that theorem on the actual automorphism pullbacks. Its finite
odd-field, rank, nondefining-prime and ordinary splitting scope is explicit.

The norm-square-class diagonal map and effective actions are the existing
constructions. The remaining statements restrict the ordinary theorem to
those actions and their stable selected subtypes. They do not transfer the
statement to Brauer characters or assert a criterion conclusion.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBSpinOrdinarySeparationBinding

open ModularRep OrdinaryIrreducibleCharacter
open TypeBCliffordCarriers TypeBSpinStabilizer TypeBFLZLabelSource
open TypeBCliffordCentreSource TypeBSpinDiagonalFieldQuotient
open TypeBSpinDiagonalNormSource TypeBSpinEffectiveClassActions
open TypeBSpinEffectiveSourceBinding TypeBSpecialCliffordActionAdapter

variable {n p f ell : ℕ} {F K : Type} [Field F] [Field K]

/-- FLZ Theorem 3.10 on every actual ordinary Spin character. Passing to
inverse field and diagonal elements gives these paired pullback conventions.
The nontrivial diagonal condition is literal membership in Spin times the
actual special-Clifford centre. The later Brauer corollary is not used. -/
structure Theorem310Source
    [finiteField : Finite F] [definingCharacteristic : CharP F p]
    [positiveFieldDegree : NeZero f] [finiteClifford : Finite (Clifford n F)]
    (parameters : OddFieldParameters F p f) (scope : Applicability p ell n)
    (N : NormSource n F) (fs : FieldActionSource n F p f parameters N)
    [ordinaryCharacteristic : CharZero K]
    [ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card (Spin n F N))] : Prop where
  separate : ∀ (chi : Irr K (Spin n F N))
      (g : SpecialClifford n F) (e : FieldGroup f),
    g ∉ SpinSubgroup n F N ⊔ Subgroup.center (SpecialClifford n F) →
    OrdinaryIrreducibleCharacter.twist K (Spin n F N) chi
        (spinFieldAction n F fs e⁻¹) =
      OrdinaryIrreducibleCharacter.twist K (Spin n F N) chi
        (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹) →
    OrdinaryIrreducibleCharacter.twist K (Spin n F N) chi
        (spinFieldAction n F fs e⁻¹) = chi ∧
      OrdinaryIrreducibleCharacter.twist K (Spin n F N) chi
        (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹) = chi

variable [Finite F] [CharP F p] [NeZero f] [Finite (Clifford n F)]
variable [CharZero K]
variable (parameters : OddFieldParameters F p f) (scope : Applicability p ell n)
variable (N : NormSource n F) (fs : FieldActionSource n F p f parameters N)
variable (centre : CentreSource n F parameters
  (Nat.le_trans (by decide : 1 ≤ 3) scope.rank))

/-- The same norm-square-class diagonal source used by the Spin block theorem. -/
abbrev diagonalData : DiagonalSource N :=
  diagonalSource n F N parameters (Nat.le_trans (by decide : 1 ≤ 3) scope.rank) centre

/-- The constructed effective action on all ordinary Spin characters. -/
@[instance_reducible]
def ordinaryAction : MulAction (OuterGroup f) (Irr K (Spin n F N)) :=
  MulAction.compHom (Irr K (Spin n F N))
    (effectiveOrdinaryHom (k := K) N (diagonalData parameters scope N centre) fs)

/-- The actual diagonal factor is the inverse regular-conjugation pullback. -/
theorem ordinaryAction_diagonal (g : SpecialClifford n F)
    (chi : Irr K (Spin n F N)) :
    letI := ordinaryAction (K := K) parameters scope N fs centre
    (((diagonalData parameters scope N centre).diagonal g, 1) : OuterGroup f) • chi =
      OrdinaryIrreducibleCharacter.twist K (Spin n F N) chi
        (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹) :=
  effectiveOrdinaryHom_diagonal_apply (k := K) N
    (diagonalData parameters scope N centre) fs g chi

/-- The actual field factor is the inverse coordinate-field pullback. -/
theorem ordinaryAction_field (e : FieldGroup f) (chi : Irr K (Spin n F N)) :
    letI := ordinaryAction (K := K) parameters scope N fs centre
    ((1, e) : OuterGroup f) • chi =
      OrdinaryIrreducibleCharacter.twist K (Spin n F N) chi
        (spinFieldAction n F fs e⁻¹) :=
  effectiveOrdinaryHom_field_apply (k := K) N
    (diagonalData parameters scope N centre) fs e chi

variable [HasEnoughRootsOfUnity K (Nat.card (Spin n F N))]
variable (ordinary : Theorem310Source parameters scope N fs (K := K))

include ordinary in
/-- The source theorem is bound to the constructed effective factors. -/
theorem ordinary_separate (chi : Irr K (Spin n F N))
    (g : SpecialClifford n F) (e : FieldGroup f)
    (hg : g ∉ SpinSubgroup n F N ⊔ Subgroup.center (SpecialClifford n F)) :
    letI := ordinaryAction (K := K) parameters scope N fs centre
    ((1, e) : OuterGroup f) • chi =
        (((diagonalData parameters scope N centre).diagonal g, 1) : OuterGroup f) • chi →
      ((1, e) : OuterGroup f) • chi = chi ∧
        (((diagonalData parameters scope N centre).diagonal g, 1) : OuterGroup f) • chi = chi := by
  letI := ordinaryAction (K := K) parameters scope N fs centre
  intro heq
  have hfield := ordinaryAction_field parameters scope N fs centre e chi
  have hdiag := ordinaryAction_diagonal parameters scope N fs centre g chi
  have h := ordinary.separate chi g e hg (hfield.symm.trans (heq.trans hdiag))
  exact ⟨hfield.trans h.1, hdiag.trans h.2⟩

include ordinary in
/-- The trivial diagonal case and inverse conversion give the full ordinary
product-stabilizer factorization on the actual effective action. -/
theorem ordinary_product_factorization (chi : Irr K (Spin n F N))
    (g : SpecialClifford n F) (e : FieldGroup f) :
    letI := ordinaryAction (K := K) parameters scope N fs centre
    (((diagonalData parameters scope N centre).diagonal g, 1) : OuterGroup f) •
        (((1, e) : OuterGroup f) • chi) = chi ↔
      (((diagonalData parameters scope N centre).diagonal g, 1) : OuterGroup f) • chi = chi ∧
        ((1, e) : OuterGroup f) • chi = chi := by
  letI := ordinaryAction (K := K) parameters scope N fs centre
  let D := diagonalData parameters scope N centre
  constructor
  · intro h
    by_cases hg : g ∈ SpinSubgroup n F N ⊔ Subgroup.center (SpecialClifford n F)
    · have hd : D.diagonal g = 1 := by
        change g ∈ D.diagonal.ker
        rwa [D.kernel]
      have hpair : ((D.diagonal g, 1) : OuterGroup f) = 1 := Prod.ext hd rfl
      change ((D.diagonal g, 1) : OuterGroup f) •
        (((1, e) : OuterGroup f) • chi) = chi at h
      change ((D.diagonal g, 1) : OuterGroup f) • chi = chi ∧
        ((1, e) : OuterGroup f) • chi = chi
      rw [hpair, one_smul] at h ⊢
      exact ⟨rfl, h⟩
    · have hginv : g⁻¹ ∉ SpinSubgroup n F N ⊔
          Subgroup.center (SpecialClifford n F) := by
        intro hi
        apply hg
        simpa using (SpinSubgroup n F N ⊔
          Subgroup.center (SpecialClifford n F)).inv_mem hi
      have heq : ((1, e) : OuterGroup f) • chi =
          ((D.diagonal g⁻¹, 1) : OuterGroup f) • chi := by
        simpa only [map_inv, Prod.inv_mk, inv_one] using (eq_inv_smul_iff.mpr h)
      have he := (ordinary_separate parameters scope N fs centre ordinary chi g⁻¹ e hginv heq).1
      exact ⟨by simpa only [he] using h, he⟩
  · rintro ⟨hg, he⟩
    rw [he, hg]

section Selected

variable (series : Irr K (Spin n F N) → Prop)
variable (diagonalStable : ∀ (g : SpecialClifford n F) (chi : Irr K (Spin n F N)),
  series chi → series (OrdinaryIrreducibleCharacter.twist K (Spin n F N) chi
    (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹)))
variable (fieldStable : ∀ (e : FieldGroup f) (chi : Irr K (Spin n F N)),
  series chi → series (OrdinaryIrreducibleCharacter.twist K (Spin n F N) chi
    (spinFieldAction n F fs e⁻¹)))

include ordinary in
/-- K restriction to the selected subtype with the same constructed action.
The predicate and its stability are deduction parameters, not source fields. -/
theorem selected_separate (chi : OrdinarySeriesCarrier series)
    (g : SpecialClifford n F) (e : FieldGroup f)
    (hg : g ∉ SpinSubgroup n F N ⊔ Subgroup.center (SpecialClifford n F)) :
    letI := selectedSeriesAction N (diagonalData parameters scope N centre) fs
      series diagonalStable fieldStable
    ((1, e) : OuterGroup f) • chi =
        (((diagonalData parameters scope N centre).diagonal g, 1) : OuterGroup f) • chi →
      ((1, e) : OuterGroup f) • chi = chi ∧
        (((diagonalData parameters scope N centre).diagonal g, 1) : OuterGroup f) • chi = chi := by
  letI := selectedSeriesAction N (diagonalData parameters scope N centre) fs
    series diagonalStable fieldStable
  intro heq
  have h := ordinary_separate parameters scope N fs centre ordinary chi.val g e hg
    (congrArg Subtype.val heq)
  exact ⟨Subtype.ext h.1, Subtype.ext h.2⟩

include ordinary in
/-- K restriction of the actual ordinary factorization to any stable selected
family. A later application supplies the same lower rational family. -/
theorem selected_product_factorization (chi : OrdinarySeriesCarrier series)
    (g : SpecialClifford n F) (e : FieldGroup f) :
    letI := selectedSeriesAction N (diagonalData parameters scope N centre) fs
      series diagonalStable fieldStable
    (((diagonalData parameters scope N centre).diagonal g, 1) : OuterGroup f) •
        (((1, e) : OuterGroup f) • chi) = chi ↔
      (((diagonalData parameters scope N centre).diagonal g, 1) : OuterGroup f) • chi = chi ∧
        ((1, e) : OuterGroup f) • chi = chi := by
  letI := selectedSeriesAction N (diagonalData parameters scope N centre) fs
    series diagonalStable fieldStable
  constructor
  · intro h
    have hv := (ordinary_product_factorization parameters scope N fs centre ordinary chi.val g e).mp
      (congrArg Subtype.val h)
    exact ⟨Subtype.ext hv.1, Subtype.ext hv.2⟩
  · rintro ⟨hg, he⟩
    rw [he, hg]

end Selected

end ModularRep.PaperProofs.TypeBSpinOrdinarySeparationBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
