import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalAmbient

/-! The identity own-quotient ambient needs innerness only for the chosen
Brauer stabilizer. These are internal constructors: their stabilizer input
is to be derived from the original centre action in a faithful sector. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierStabilizerInnerAmbient

open ModularRep
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnQuotientAutomorphisms
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalAmbient

universe u
variable (P : Definition35Problem.{u}) (psi : Definition35Brauer P)

theorem innerToOriginalStabilizer_surjective_of_stabilizerInner
    (stabilizerInner : ∀ a : MulAction.stabilizer (MulAut P.H)ᵐᵒᵖ psi.1,
      ∃ x : P.H, a.1.unop = MulAut.conj x) :
    Function.Surjective (innerToOriginalStabilizer P psi) := by
  intro a
  obtain ⟨x, hx⟩ := stabilizerInner a
  refine ⟨x⁻¹, ?_⟩
  apply Subtype.ext
  apply MulOpposite.unop_injective
  change MulAut.conj (x⁻¹)⁻¹ = a.1.unop
  simpa only [inv_inv] using hx.symm

theorem originalAction_surjective_of_stabilizerInner
    (stabilizerInner : ∀ a : MulAction.stabilizer (MulAut P.H)ᵐᵒᵖ psi.1,
      ∃ x : P.H, a.1.unop = MulAut.conj x) :
    Function.Surjective (originalAction P psi) :=
  QuotientGroup.lift_surjective_of_surjective (centralCharacterKernel P psi)
    (innerToOriginalStabilizer P psi)
    (innerToOriginalStabilizer_surjective_of_stabilizerInner P psi stabilizerInner) _

def originalStabilizerEquiv_of_stabilizerInner [Group.IsPerfect P.H]
    (stabilizerInner : ∀ a : MulAction.stabilizer (MulAut P.H)ᵐᵒᵖ psi.1,
      ∃ x : P.H, a.1.unop = MulAut.conj x) :
    (CentralCharacterQuotient P psi ⧸ Subgroup.center (CentralCharacterQuotient P psi)) ≃*
      MulAction.stabilizer (MulAut P.H)ᵐᵒᵖ psi.1 :=
  QuotientGroup.liftEquiv (Subgroup.center (CentralCharacterQuotient P psi))
    (originalAction_surjective_of_stabilizerInner P psi stabilizerInner)
    (originalAction_ker P psi).symm

theorem originalStabilizerEquiv_of_stabilizerInner_mk [Group.IsPerfect P.H]
    (stabilizerInner : ∀ a : MulAction.stabilizer (MulAut P.H)ᵐᵒᵖ psi.1,
      ∃ x : P.H, a.1.unop = MulAut.conj x)
    (a : CentralCharacterQuotient P psi) :
    originalStabilizerEquiv_of_stabilizerInner P psi stabilizerInner
      (QuotientGroup.mk' (Subgroup.center (CentralCharacterQuotient P psi)) a) =
        originalAction P psi a := rfl

def identityAmbient_of_stabilizerInner [Group.IsPerfect P.H]
    (hcenter : ¬ P.p ∣ Nat.card (Subgroup.center P.H))
    (stabilizerInner : ∀ a : MulAction.stabilizer (MulAut P.H)ᵐᵒᵖ psi.1,
      ∃ x : P.H, a.1.unop = MulAut.conj x) :
    OriginalSpathAmbient P psi where
  A := CentralCharacterQuotient P psi
  fintypeA := Fintype.ofFinite _
  base := ⊤
  baseEquiv := Subgroup.topEquiv.symm
  baseCentralizer_eq_center := by
    simpa only [Subgroup.coe_top] using
      (Subgroup.centralizer_univ (G := CentralCharacterQuotient P psi))
  centerPrimeTo := center_primeTo P psi hcenter
  originalConjugation := originalConjugation P psi
  conjugation_on_base := originalConjugation_quotient_square P psi
  automorphismQuotientEquiv :=
    originalStabilizerEquiv_of_stabilizerInner P psi stabilizerInner
  automorphismQuotientEquiv_natural := by
    intro a
    rw [originalStabilizerEquiv_of_stabilizerInner_mk]
    exact originalAction_coe P psi a

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierStabilizerInnerAmbient



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
