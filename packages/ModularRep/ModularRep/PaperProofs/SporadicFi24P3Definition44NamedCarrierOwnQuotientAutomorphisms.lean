import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnCentralQuotient

/-! The own central quotient acts through the ORIGINAL Brauer automorphism
stabilizer. No assertion about the full automorphism group of the quotient
is used. The right action is the left action of the opposite group. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnQuotientAutomorphisms

open ModularRep
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralKernelGroup

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

variable (P : Definition35Problem.{u}) (psi : Definition35Brauer P)

def innerToOriginalStabilizer :
    P.H →* MulAction.stabilizer (MulAut P.H)ᵐᵒᵖ psi.1 :=
  (inverseOpHom (MulAut.conj : P.H →* MulAut P.H)).codRestrict _ (by
    intro x
    change MulOpposite.op (MulAut.conj x⁻¹) • psi.1 = psi.1
    apply Subtype.ext
    exact PrimeRegularClassFunction.twist_conj psi.1.1 x⁻¹)

theorem innerToOriginalStabilizer_ker :
    (innerToOriginalStabilizer P psi).ker = Subgroup.center P.H := by
  ext x
  change innerToOriginalStabilizer P psi x = 1 ↔ x ∈ Subgroup.center P.H
  rw [Subtype.ext_iff]
  change MulOpposite.op (MulAut.conj x⁻¹) = MulOpposite.op (1 : MulAut P.H) ↔
    x ∈ Subgroup.center P.H
  rw [MulOpposite.op_inj]
  change x⁻¹ ∈ (MulAut.conj : P.H →* MulAut P.H).ker ↔ x ∈ Subgroup.center P.H
  rw [conj_ker_eq_center, inv_mem_iff]

theorem innerToOriginalStabilizer_surjective
    (allInner : ∀ a : MulAut P.H, ∃ x : P.H, a = MulAut.conj x) :
    Function.Surjective (innerToOriginalStabilizer P psi) := by
  intro a
  obtain ⟨x, hx⟩ := allInner a.1.unop
  refine ⟨x⁻¹, ?_⟩
  apply Subtype.ext
  apply MulOpposite.unop_injective
  change MulAut.conj (x⁻¹)⁻¹ = a.1.unop
  simpa only [inv_inv] using hx.symm

def originalAction :
    CentralCharacterQuotient P psi →* MulAction.stabilizer (MulAut P.H)ᵐᵒᵖ psi.1 :=
  QuotientGroup.lift (centralCharacterKernel P psi) (innerToOriginalStabilizer P psi)
    (by rw [innerToOriginalStabilizer_ker]; exact inf_le_left)

theorem originalAction_mk (x : P.H) :
    originalAction P psi (centralCharacterQuotientMap P psi x) =
      innerToOriginalStabilizer P psi x := rfl

theorem originalAction_ker [Group.IsPerfect P.H] :
    (originalAction P psi).ker = Subgroup.center (CentralCharacterQuotient P psi) := by
  rw [originalAction, QuotientGroup.ker_lift, innerToOriginalStabilizer_ker]
  exact (center_eq_map_center_of_le_center (centralCharacterKernel P psi) inf_le_left).symm

theorem originalAction_surjective
    (allInner : ∀ a : MulAut P.H, ∃ x : P.H, a = MulAut.conj x) :
    Function.Surjective (originalAction P psi) :=
  QuotientGroup.lift_surjective_of_surjective (centralCharacterKernel P psi)
    (innerToOriginalStabilizer P psi) (innerToOriginalStabilizer_surjective P psi allInner) _

def originalStabilizerEquiv [Group.IsPerfect P.H]
    (allInner : ∀ a : MulAut P.H, ∃ x : P.H, a = MulAut.conj x) :
    (CentralCharacterQuotient P psi ⧸ Subgroup.center (CentralCharacterQuotient P psi)) ≃*
      MulAction.stabilizer (MulAut P.H)ᵐᵒᵖ psi.1 :=
  QuotientGroup.liftEquiv (Subgroup.center (CentralCharacterQuotient P psi))
    (originalAction_surjective P psi allInner) (originalAction_ker P psi).symm

theorem originalStabilizerEquiv_mk [Group.IsPerfect P.H]
    (allInner : ∀ a : MulAut P.H, ∃ x : P.H, a = MulAut.conj x)
    (a : CentralCharacterQuotient P psi) :
    originalStabilizerEquiv P psi allInner
      (QuotientGroup.mk' (Subgroup.center (CentralCharacterQuotient P psi)) a) =
        originalAction P psi a := rfl

def originalConjugation : CentralCharacterQuotient P psi →* MulAut P.H :=
  QuotientGroup.lift (centralCharacterKernel P psi) (MulAut.conj : P.H →* MulAut P.H)
    (by rw [conj_ker_eq_center]; exact inf_le_left)

theorem originalConjugation_mk (x : P.H) :
    originalConjugation P psi (centralCharacterQuotientMap P psi x) = MulAut.conj x := rfl

theorem originalAction_coe (a : CentralCharacterQuotient P psi) :
    (originalAction P psi a).1 = inverseOpHom (originalConjugation P psi) a := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (centralCharacterKernel P psi) a
  rfl

theorem originalConjugation_quotient_square (a : CentralCharacterQuotient P psi) (x : P.H) :
    centralCharacterQuotientMap P psi (originalConjugation P psi a x) =
      a * centralCharacterQuotientMap P psi x * a⁻¹ := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (centralCharacterKernel P psi) a
  change centralCharacterQuotientMap P psi (g * x * g⁻¹) = _
  simp only [map_mul, map_inv]

theorem center_card_dvd [Group.IsPerfect P.H] :
    Nat.card (Subgroup.center (CentralCharacterQuotient P psi)) ∣ Nat.card (Subgroup.center P.H) := by
  rw [center_eq_map_center_of_le_center (centralCharacterKernel P psi) inf_le_left]
  exact Subgroup.card_map_dvd (Subgroup.center P.H) (centralCharacterQuotientMap P psi)

theorem center_primeTo [Group.IsPerfect P.H]
    (hcenter : ¬ P.p ∣ Nat.card (Subgroup.center P.H)) :
    ¬ P.p ∣ Nat.card (Subgroup.center (CentralCharacterQuotient P psi)) := by
  intro h
  exact hcenter (dvd_trans h (center_card_dvd P psi))

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnQuotientAutomorphisms



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
