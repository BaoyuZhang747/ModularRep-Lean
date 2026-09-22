import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientStabilizer

/-! The literal ambient group A=X when X is centreless and all of its
automorphisms are inner. Its canonical quotient acts with the same right /
opposite convention as the named Fischer construction. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIdentityAmbient

open ModularRep
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZCentrelessCentralKernel
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientStabilizer

universe u

theorem conj_ker_eq_center {X : Type u} [Group X] :
    (MulAut.conj : X →* MulAut X).ker = Subgroup.center X := by
  ext x
  change MulAut.conj x = 1 ↔ x ∈ Subgroup.center X
  constructor
  · intro h
    apply Subgroup.mem_center_iff.mpr
    intro y
    have hy : x * y * x⁻¹ = y := DFunLike.congr_fun h y
    exact ((mul_inv_eq_iff_eq_mul).mp hy).symm
  · intro hx
    ext y
    change x * y * x⁻¹ = y
    rw [← Subgroup.mem_center_iff.mp hx y, mul_inv_cancel_right]

def innerToBrauerStabilizer (P : Definition35Problem.{u}) (psi : Definition35Brauer P) :
    P.H →* MulAction.stabilizer (MulAut P.H)ᵐᵒᵖ psi.1 :=
  (inverseOpHom (MulAut.conj : P.H →* MulAut P.H)).codRestrict _ (by
    intro x
    change MulOpposite.op (MulAut.conj x⁻¹) • psi.1 = psi.1
    apply Subtype.ext
    exact PrimeRegularClassFunction.twist_conj psi.1.1 x⁻¹)

theorem innerToBrauerStabilizer_bijective (P : Definition35Problem.{u})
    (hc : Subgroup.center P.H = ⊥) (psi : Definition35Brauer P)
    (allInner : ∀ a : MulAut P.H, ∃ x : P.H, a = MulAut.conj x) :
    Function.Bijective (innerToBrauerStabilizer P psi) := by
  have hi : Function.Injective (MulAut.conj : P.H →* MulAut P.H) :=
    (MulAut.conj : P.H →* MulAut P.H).ker_eq_bot_iff.mp (conj_ker_eq_center.trans hc)
  constructor
  · intro x y h
    apply inv_injective
    apply hi
    exact congrArg (fun z => z.1.unop) h
  · intro a
    obtain ⟨x, hx⟩ := allInner a.1.unop
    refine ⟨x⁻¹, ?_⟩
    apply Subtype.ext
    apply MulOpposite.unop_injective
    change MulAut.conj (x⁻¹)⁻¹ = a.1.unop
    simpa only [inv_inv] using hx.symm

def identityAmbient (P : Definition35Problem.{u})
    (hc : Subgroup.center P.H = ⊥) (psi : Definition35Brauer P)
    (q : CentralQuotientBrauerSource P psi psi)
    (allInner : ∀ a : MulAut P.H, ∃ x : P.H, a = MulAut.conj x) :
    SpathAmbientGroup P psi psi q := by
  let e : P.H ≃* CentralCharacterQuotient P psi :=
    MulEquiv.ofBijective (centralCharacterQuotientMap P psi)
      (centralCharacterQuotientMap_bijective_of_centerless P hc psi)
  let rX := innerToBrauerStabilizer P psi
  let rE := MulEquiv.ofBijective rX (innerToBrauerStabilizer_bijective P hc psi allInner)
  let qS := quotientStabilizerEquiv P hc psi psi q
  let rho : P.H →* MulAut (CentralCharacterQuotient P psi) :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conj : P.H →* MulAut P.H)
  let QE := (QuotientGroup.quotientMulEquivOfEq hc).trans
    (QuotientGroup.quotientBot.trans (rE.trans qS))
  refine {
    A := P.H
    base := ⊤
    baseEquiv := e.symm.trans Subgroup.topEquiv.symm
    baseCentralizer_eq_center := ?_
    centerPrimeTo := ?_
    conjugation := rho
    conjugation_on_base := ?_
    automorphismQuotientEquiv := QE
    automorphismQuotientEquiv_natural := ?_ }
  · simpa only [Subgroup.coe_top] using (Subgroup.centralizer_univ (G := P.H))
  · simpa [hc] using P.iota.prime.not_dvd_one
  · intro a h
    change e.symm (e ((MulAut.conj a) (e.symm h))) = a * e.symm h * a⁻¹
    rw [e.symm_apply_apply]
    rfl
  · intro a
    change (qS (rX (QuotientGroup.quotientBot
      (QuotientGroup.quotientMulEquivOfEq hc (QuotientGroup.mk a))))).1 = _
    rw [QuotientGroup.quotientMulEquivOfEq_mk]
    rfl

theorem identityAmbient_base (P : Definition35Problem.{u})
    (hc : Subgroup.center P.H = ⊥) (psi : Definition35Brauer P)
    (q : CentralQuotientBrauerSource P psi psi)
    (allInner : ∀ a : MulAut P.H, ∃ x : P.H, a = MulAut.conj x) :
    (identityAmbient P hc psi q allInner).base = ⊤ := rfl

theorem identityAmbient_embedding (P : Definition35Problem.{u})
    (hc : Subgroup.center P.H = ⊥) (psi : Definition35Brauer P)
    (q : CentralQuotientBrauerSource P psi psi)
    (allInner : ∀ a : MulAut P.H, ∃ x : P.H, a = MulAut.conj x) :
    (quotientToAmbient P psi psi q (identityAmbient P hc psi q allInner)).comp
      (centralCharacterQuotientMap P psi) = MonoidHom.id P.H := by
  ext x
  exact (MulEquiv.ofBijective (centralCharacterQuotientMap P psi)
    (centralCharacterQuotientMap_bijective_of_centerless P hc psi)).symm_apply_apply x

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIdentityAmbient


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
