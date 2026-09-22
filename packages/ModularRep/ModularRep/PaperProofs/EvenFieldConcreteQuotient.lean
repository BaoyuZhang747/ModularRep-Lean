import ModularRep.PaperProofs.EvenFieldSourceShaped
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The concrete relative quotient in manuscript Lemma 3.6

This module replaces an arbitrary `RelativeQuotient` by an actual quotient
group and proves the character consequence of the Cabanes--Späth innerness
input.  Once the automorphism induced by the inner-twisted field action is
identified with conjugation by an element of the quotient, every class
function on the quotient is fixed.
-/

namespace ModularRep.PaperProofs.EvenFieldConcreteQuotient

open ModularRep.PaperProofs.EvenFieldSourceShaped

universe uG uV

/-- The relative quotient `N_lambda / M^F'` used in the manuscript. -/
abbrev RelativeQuotient
    (Inertia : Type uG) [Group Inertia]
    (Base : Subgroup Inertia) [Base.Normal] :=
  Inertia ⧸ Base

/-- Class functions on a group, used as the semantic carrier for quotient
characters in the innerness argument. -/
def ClassFunction (Q : Type uG) [Group Q] (Value : Type uV) :=
  {chi : Q → Value // IsConjugationInvariant chi}

instance {Q : Type uG} [Group Q] {Value : Type uV} :
    CoeFun (ClassFunction Q Value) (fun _ ↦ Q → Value) :=
  ⟨fun chi ↦ chi.1⟩

/-- The action on quotient class functions induced by conjugation with `q`. -/
def innerAction
    {Q : Type uG} [Group Q] {Value : Type uV}
    (q : Q) (chi : ClassFunction Q Value) : ClassFunction Q Value :=
  ⟨innerConjugationAction q chi, by
    intro a x
    have h := chi.property (q * a * q⁻¹) (q * x * q⁻¹)
    simpa [innerConjugationAction, mul_assoc] using h⟩

@[simp]
theorem innerAction_apply
    {Q : Type uG} [Group Q] {Value : Type uV}
    (q : Q) (chi : ClassFunction Q Value) (x : Q) :
    innerAction q chi x = chi (q * x * q⁻¹) :=
  rfl

/-- Inner automorphisms fix every quotient class function. -/
theorem innerAction_fixed
    {Q : Type uG} [Group Q] {Value : Type uV}
    (q : Q) (chi : ClassFunction Q Value) :
    innerAction q chi = chi := by
  apply Subtype.ext
  exact innerConjugationAction_fixed q chi chi.property

/-- If the concrete action induced by `tau` is identified with an inner
action, fixation of all quotient characters is a Lean deduction. -/
theorem all_fixed_of_action_eq_inner
    {Q : Type uG} [Group Q] {Value : Type uV}
    (action : ClassFunction Q Value → ClassFunction Q Value)
    (q : Q) (action_eq : action = innerAction q) :
    ∀ chi, action chi = chi := by
  intro chi
  rw [action_eq]
  exact innerAction_fixed q chi

/-- Source contract for the concrete relative quotient.  The character
carrier is definitionally the class functions on `Inertia / Base`; it cannot
be replaced by an unrelated group. -/
structure Data where
  Inertia : Type uG
  inertiaGroup : Group Inertia
  Base : @Subgroup Inertia inertiaGroup
  baseNormal : @Subgroup.Normal Inertia inertiaGroup Base
  Value : Type uV
  quotientAction :
    let _ : Group Inertia := inertiaGroup
    let _ : Base.Normal := baseNormal
    ClassFunction (Inertia ⧸ Base) Value →
      ClassFunction (Inertia ⧸ Base) Value
  innerElement :
    let _ : Group Inertia := inertiaGroup
    let _ : Base.Normal := baseNormal
    Inertia ⧸ Base
  action_eq_inner :
    let _ : Group Inertia := inertiaGroup
    let _ : Base.Normal := baseNormal
    quotientAction = innerAction innerElement

/-- Every quotient character in the concrete source contract is fixed. -/
theorem Data.quotientCharactersFixed (D : Data) :
    let _ : Group D.Inertia := D.inertiaGroup
    let _ : D.Base.Normal := D.baseNormal
    ∀ chi : ClassFunction (D.Inertia ⧸ D.Base) D.Value,
      D.quotientAction chi = chi := by
  letI : Group D.Inertia := D.inertiaGroup
  letI : D.Base.Normal := D.baseNormal
  exact all_fixed_of_action_eq_inner D.quotientAction D.innerElement
    D.action_eq_inner

end ModularRep.PaperProofs.EvenFieldConcreteQuotient


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
