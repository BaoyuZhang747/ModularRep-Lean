import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCoverAutomorphismEquiv
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialCentralSector
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnCentralQuotient
import ModularRep.IrreducibleBrauerCharacterSurjectiveDescent

/-! Automorphism and Brauer-stabilizer transport on the original character's
own quotient. The universal map and the literal central-sector equation
produce the equivalence; fixation follows from canonical Brauer inflation. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorAutomorphismTransport

open ModularRep
open ModularRep.IrreducibleBrauerCharacterSurjectiveDescent
open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCoverGroupFacts
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCoverAutomorphismEquiv
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialCentralSector
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnCentralQuotient

universe u

def fullCoverOwnAutEquiv
    (P : Definition35Problem.{u}) (psi : Definition35Brauer P)
    {S : Type u} [Group S] (q : P.H →* S)
    (hq : IsUniversalCentralExtension q)
    (hk : q.ker = Subgroup.center P.H)
    (hZ0 : centralCharacterKernel P psi = Subgroup.center P.H) :
    MulAut P.H ≃* MulAut (CentralCharacterQuotient P psi) :=
  let e : CentralCharacterQuotient P psi ≃* S :=
    QuotientGroup.liftEquiv (centralCharacterKernel P psi)
      hq.1.1 (hZ0.trans hk.symm)
  (fullCoverAutEquiv q hq hk).trans (MulAut.congr e.symm)

theorem fullCoverOwnAutEquiv_square
    (P : Definition35Problem.{u}) (psi : Definition35Brauer P)
    {S : Type u} [Group S] (q : P.H →* S)
    (hq : IsUniversalCentralExtension q)
    (hk : q.ker = Subgroup.center P.H)
    (hZ0 : centralCharacterKernel P psi = Subgroup.center P.H)
    (alpha : MulAut P.H) (x : P.H) :
    fullCoverOwnAutEquiv P psi q hq hk hZ0 alpha
        (centralCharacterQuotientMap P psi x) =
      centralCharacterQuotientMap P psi (alpha x) := by
  let e : CentralCharacterQuotient P psi ≃* S :=
    QuotientGroup.liftEquiv (centralCharacterKernel P psi)
      hq.1.1 (hZ0.trans hk.symm)
  change e.symm (fullCoverAutEquiv q hq hk alpha (q x)) =
    centralCharacterQuotientMap P psi (alpha x)
  rw [fullCoverAutEquiv_apply_q]
  exact e.symm_apply_apply (centralCharacterQuotientMap P psi (alpha x))

theorem pullback_twist_of_square
    {p : ℕ} {K X Y : Type u} [Group X] [Group Y]
    (f : X →* Y) (alpha : MulAut X) (beta : MulAut Y)
    (hsquare : ∀ x, f (alpha x) = beta (f x))
    (chi : PrimeRegularClassFunction K Y p) :
    PrimeRegularClassFunction.pullback f (chi.twist beta) =
      (PrimeRegularClassFunction.pullback f chi).twist alpha := by
  ext x
  exact congrArg chi (Subtype.ext (hsquare x.1).symm)

section Stabilizer

variable (P : Definition35Problem.{u}) (psi : Definition35Brauer P)
variable (E : MulAut P.H ≃* MulAut (CentralCharacterQuotient P psi))
variable (hsquare : ∀ (alpha : MulAut P.H) (x : P.H),
  E alpha (centralCharacterQuotientMap P psi x) =
    centralCharacterQuotientMap P psi (alpha x))
variable (hcenter : ¬ P.p ∣ Nat.card (Subgroup.center P.H))

include hsquare hcenter

theorem ownBrauer_fixed_iff (alpha : MulAut P.H) :
    MulOpposite.op alpha • psi.1 = psi.1 ↔
      MulOpposite.op (E alpha) • ownQuotientBrauer P psi =
        ownQuotientBrauer P psi := by
  suffices hfix : psi.1.1.twist alpha = psi.1.1 ↔
    (ownQuotientBrauer P psi).1.twist (E alpha) =
      (ownQuotientBrauer P psi).1 by
    constructor
    · intro h
      apply Subtype.ext
      exact hfix.mp (congrArg Subtype.val h)
    · intro h
      apply Subtype.ext
      exact hfix.mpr (congrArg Subtype.val h)
  have hprimeTo :
      (Nat.card (centralCharacterQuotientMap P psi).ker).Coprime P.p := by
    change (Nat.card (QuotientGroup.mk' (centralCharacterKernel P psi)).ker).Coprime P.p
    rw [QuotientGroup.ker_mk']
    apply (P.iota.prime.coprime_iff_not_dvd.mpr ?_).symm
    intro h
    exact hcenter (h.trans (Subgroup.card_dvd_of_le
      (show centralCharacterKernel P psi ≤ Subgroup.center P.H from inf_le_left)))
  have hinj :=
    primeRegularClassFunction_pullback_injective_of_ker_card_coprime
        (K := P.K) (centralCharacterQuotientMap P psi)
        (QuotientGroup.mk'_surjective _) hprimeTo
  have hnatural := pullback_twist_of_square
    (centralCharacterQuotientMap P psi) alpha (E alpha)
    (fun x => (hsquare alpha x).symm) (ownQuotientBrauer P psi).1
  constructor
  · intro h
    apply hinj
    exact hnatural.trans
      ((congrArg (fun chi : PrimeRegularClassFunction P.K P.H P.p => chi.twist alpha)
        (ownQuotientBrauer_inflation P psi)).trans
          (h.trans (ownQuotientBrauer_inflation P psi).symm))
  · intro h
    have hpull := congrArg
      (PrimeRegularClassFunction.pullback (centralCharacterQuotientMap P psi)) h
    exact (congrArg (fun chi : PrimeRegularClassFunction P.K P.H P.p => chi.twist alpha)
      (ownQuotientBrauer_inflation P psi)).symm.trans
        (hnatural.symm.trans (hpull.trans (ownQuotientBrauer_inflation P psi)))

def stabilizerEquivOfOwnAut :
    MulAction.stabilizer (MulAut P.H)ᵐᵒᵖ psi.1 ≃*
      MulAction.stabilizer
        (MulAut (CentralCharacterQuotient P psi))ᵐᵒᵖ
        (ownQuotientBrauer P psi) where
  toFun a :=
    ⟨MulOpposite.op (E a.1.unop),
      (ownBrauer_fixed_iff P psi E hsquare hcenter a.1.unop).mp a.2⟩
  invFun b :=
    ⟨MulOpposite.op (E.symm b.1.unop), by
      apply (ownBrauer_fixed_iff P psi E hsquare hcenter (E.symm b.1.unop)).mpr
      have hb : MulOpposite.op b.1.unop • ownQuotientBrauer P psi =
          ownQuotientBrauer P psi := b.2
      simpa only [E.apply_symm_apply] using hb⟩
  left_inv a := by
    apply Subtype.ext
    apply MulOpposite.unop_injective
    exact E.symm_apply_apply a.1.unop
  right_inv b := by
    apply Subtype.ext
    apply MulOpposite.unop_injective
    exact E.apply_symm_apply b.1.unop
  map_mul' a b := by
    apply Subtype.ext
    apply MulOpposite.unop_injective
    exact E.map_mul b.1.unop a.1.unop

theorem stabilizerEquivOfOwnAut_coe
    (a : MulAction.stabilizer (MulAut P.H)ᵐᵒᵖ psi.1) :
    (stabilizerEquivOfOwnAut P psi E hsquare hcenter a).1 =
      MulOpposite.op (E a.1.unop) := rfl

end Stabilizer

section TrivialSector

variable (P : Definition35Problem.{u}) (psi : Definition35Brauer P)
variable {S : Type u} [Group S] (q : P.H →* S)
variable (hq : IsUniversalCentralExtension q)
variable (hs : IsSimpleGroup S) (hna : ¬ IsMulCommutative S)
variable (hcenter : ¬ P.p ∣ Nat.card (Subgroup.center P.H))
variable (hglobal : ∀ z : PrimeRegularElement (G := Subgroup.center P.H) P.p,
  psi.1.1 (PrimeRegularElement.map (Subgroup.center P.H).subtype z) =
    psi.1.1 ⟨1, isPrimeRegular_one⟩)

def trivialSectorAutEquiv : MulAut P.H ≃* MulAut (CentralCharacterQuotient P psi) :=
  fullCoverOwnAutEquiv P psi q hq
    (ker_eq_center_of_simple_quotient q hq.1 hs hna)
    (centralCharacterKernel_eq_center_of_trivial_sector P psi hcenter hglobal)

theorem trivialSectorAutEquiv_square (alpha : MulAut P.H) (x : P.H) :
    trivialSectorAutEquiv P psi q hq hs hna hcenter hglobal alpha
        (centralCharacterQuotientMap P psi x) =
      centralCharacterQuotientMap P psi (alpha x) :=
  fullCoverOwnAutEquiv_square P psi q hq _ _ alpha x

def trivialSectorStabilizerEquiv :
    MulAction.stabilizer (MulAut P.H)ᵐᵒᵖ psi.1 ≃*
      MulAction.stabilizer
        (MulAut (CentralCharacterQuotient P psi))ᵐᵒᵖ
        (ownQuotientBrauer P psi) :=
  stabilizerEquivOfOwnAut P psi
    (trivialSectorAutEquiv P psi q hq hs hna hcenter hglobal)
    (trivialSectorAutEquiv_square P psi q hq hs hna hcenter hglobal) hcenter

end TrivialSector

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorAutomorphismTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
