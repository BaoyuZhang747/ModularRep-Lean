import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFiniteFibres
import ModularRep.PaperProofs.SporadicFi24LiteralCarrierBase

/-!
# Cancellation inside a supported sector, with fixed predicates retained

Membership in the sector follows from membership in the selected block.
The same cancellation applies to whole carriers and to fixed subsets;
neither requires an action on the sector subtype.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorFibreCancellation

open SporadicFi24P3Definition44NamedCarrierFiniteFibres

def supportedFixedFibreEquiv {A B : Type*}
    (f : A → B) (P : B → Prop) (T : A → Prop) (b : B) (hb : P b) :
    {a : {a : A // P (f a) ∧ T a} // f a.1 = b} ≃ {a : A // f a = b ∧ T a} :=
  (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun a : A => P (f a) ∧ T a) (fun a : A => f a = b)).trans
      (Equiv.subtypeEquivRight fun a => by
        constructor
        · rintro ⟨⟨_, ht⟩, hab⟩
          exact ⟨hab, ht⟩
        · rintro ⟨hab, ht⟩
          refine ⟨⟨?_, ht⟩, hab⟩
          simpa only [hab] using hb)

theorem supportedFixed_fibre_card_eq {A C B : Type*} [Finite B]
    (f : A → B) (g : C → B) (P : B → Prop) (TA : A → Prop) (TC : C → Prop)
    [Finite {a : A // P (f a) ∧ TA a}] [Finite {c : C // P (g c) ∧ TC c}]
    (b0 : B) (hb0 : P b0)
    (htotal : Nat.card {a : A // P (f a) ∧ TA a} = Nat.card {c : C // P (g c) ∧ TC c})
    (hother : ∀ b : B, P b → b ≠ b0 →
      Nat.card {a : A // f a = b ∧ TA a} = Nat.card {c : C // g c = b ∧ TC c}) :
    Nat.card {a : A // f a = b0 ∧ TA a} = Nat.card {c : C // g c = b0 ∧ TC c} := by
  classical
  let SA := {a : A // P (f a) ∧ TA a}
  let SC := {c : C // P (g c) ∧ TC c}
  have hsame : Nat.card {a : SA // f a.1 = b0} = Nat.card {c : SC // g c.1 = b0} := by
    apply card_fibre_eq_of_other_fibres (fun a : SA => f a.1) (fun c : SC => g c.1) b0 htotal
    intro b hne
    by_cases hb : P b
    · exact (Nat.card_congr (supportedFixedFibreEquiv f P TA b hb)).trans
        ((hother b hb hne).trans (Nat.card_congr (supportedFixedFibreEquiv g P TC b hb)).symm)
    · let _ : IsEmpty {a : SA // f a.1 = b} :=
        ⟨fun a => hb (by simpa only [a.2] using a.1.2.1)⟩
      let _ : IsEmpty {c : SC // g c.1 = b} :=
        ⟨fun c => hb (by simpa only [c.2] using c.1.2.1)⟩
      simp
  exact (Nat.card_congr (supportedFixedFibreEquiv f P TA b0 hb0)).symm.trans
    (hsame.trans (Nat.card_congr (supportedFixedFibreEquiv g P TC b0 hb0)))

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorFibreCancellation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
