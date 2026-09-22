import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorAutomorphismTransport
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalAmbient

/-! A group-only adapter for an already constructed own-quotient ambient.
It retains the literal ambient group, base and embedding, and derives its
interpretation through the original automorphism stabilizer. It supplies
no character extension or intermediate block assertion. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorAmbientTransport

open ModularRep
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnCentralQuotient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalAmbient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorAutomorphismTransport

universe u

theorem inverseOpHom_comp_equiv
    {A X Y : Type u} [Group A] [Group X] [Group Y]
    (E : MulAut X ≃* MulAut Y) (rho : A →* MulAut X) :
    (MulEquiv.op E).toMonoidHom.comp (inverseOpHom rho) =
      inverseOpHom (E.toMonoidHom.comp rho) := by
  ext a
  rfl

variable (P : Definition35Problem.{u}) (psi : Definition35Brauer P)
variable [Group.IsPerfect P.H]
variable (E : MulAut P.H ≃* MulAut (CentralCharacterQuotient P psi))
variable (hsquare : ∀ (alpha : MulAut P.H) (x : P.H),
  E alpha (centralCharacterQuotientMap P psi x) =
    centralCharacterQuotientMap P psi (alpha x))
variable (hcenter : ¬ P.p ∣ Nat.card (Subgroup.center P.H))
variable (B : SpathAmbientGroup P psi psi (ownCentralQuotientBrauerSource P psi))

def ambientOfOwnAut : OriginalSpathAmbient P psi where
  A := B.A
  base := B.base
  baseEquiv := B.baseEquiv
  baseCentralizer_eq_center := B.baseCentralizer_eq_center
  centerPrimeTo := B.centerPrimeTo
  originalConjugation := E.symm.toMonoidHom.comp B.conjugation
  conjugation_on_base := by
    intro a x
    have h := hsquare (E.symm (B.conjugation a)) x
    rw [E.apply_symm_apply] at h
    change (B.baseEquiv
      (centralCharacterQuotientMap P psi (E.symm (B.conjugation a) x)) : B.A) = _
    rw [← h]
    exact B.conjugation_on_base a (centralCharacterQuotientMap P psi x)
  automorphismQuotientEquiv := B.automorphismQuotientEquiv.trans
    (stabilizerEquivOfOwnAut P psi E hsquare hcenter).symm
  automorphismQuotientEquiv_natural := by
    intro a
    apply (MulEquiv.op E).injective
    calc
      MulEquiv.op E
          ((B.automorphismQuotientEquiv.trans
            (stabilizerEquivOfOwnAut P psi E hsquare hcenter).symm)
              (QuotientGroup.mk' (Subgroup.center B.A) a)).1 =
          (B.automorphismQuotientEquiv
            (QuotientGroup.mk' (Subgroup.center B.A) a)).1 := by
        change MulOpposite.op (E (E.symm _)) = _
        rw [E.apply_symm_apply]
        exact MulOpposite.op_unop _
      _ = inverseOpHom B.conjugation a :=
        B.automorphismQuotientEquiv_natural a
      _ = MulEquiv.op E
          (inverseOpHom (E.symm.toMonoidHom.comp B.conjugation) a) := by
        change MulOpposite.op (B.conjugation a⁻¹) =
          MulOpposite.op (E (E.symm (B.conjugation a⁻¹)))
        rw [E.apply_symm_apply]

theorem ambientOfOwnAut_base :
    (ambientOfOwnAut P psi E hsquare hcenter B).base = B.base := rfl

theorem ambientOfOwnAut_quotientEmbedding :
    (ambientOfOwnAut P psi E hsquare hcenter B).quotientEmbedding =
      B.base.subtype.comp B.baseEquiv.toMonoidHom := rfl

theorem ambientOfOwnAut_rawMap :
    (ambientOfOwnAut P psi E hsquare hcenter B).rawMap =
      (B.base.subtype.comp B.baseEquiv.toMonoidHom).comp
        (centralCharacterQuotientMap P psi) := rfl

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorAmbientTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
