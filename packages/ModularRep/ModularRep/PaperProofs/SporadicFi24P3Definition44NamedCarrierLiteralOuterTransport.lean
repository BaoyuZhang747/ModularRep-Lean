import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCoverGroupFacts

/-! Transport the literal outer quotient through a group equivalence.
The original universal map identifies the full-centre-kernel own quotient
with the same simple quotient, so its outer order is bound only once. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierLiteralOuterTransport

open ModularRep
open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCoverGroupFacts

universe u

private theorem opAutCongr_innerInverse
    {G H : Type u} [Group G] [Group H] (e : G ≃* H) (x : G) :
    MulEquiv.op (MulAut.congr e)
        (RepresentationWeight.innerInverseOpHom (G := G) x) =
      RepresentationWeight.innerInverseOpHom (G := H) (e x) := by
  apply MulOpposite.unop_injective
  change MulAut.congr e (MulAut.conj (x⁻¹)) = MulAut.conj ((e x)⁻¹)
  ext y
  change e (x⁻¹ * e.symm y * (x⁻¹)⁻¹) =
    (e x)⁻¹ * y * ((e x)⁻¹)⁻¹
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem innerInverseRange_map_congr
    {G H : Type u} [Group G] [Group H] (e : G ≃* H) :
    (RepresentationWeight.innerInverseOpHom (G := G)).range.map
        (MulEquiv.op (MulAut.congr e)).toMonoidHom =
      (RepresentationWeight.innerInverseOpHom (G := H)).range := by
  ext a
  constructor
  · rintro ⟨b, ⟨x, rfl⟩, rfl⟩
    exact ⟨e x, (opAutCongr_innerInverse e x).symm⟩
  · rintro ⟨y, rfl⟩
    refine ⟨RepresentationWeight.innerInverseOpHom (G := G) (e.symm y),
      ⟨e.symm y, rfl⟩, ?_⟩
    change MulEquiv.op (MulAut.congr e)
        (RepresentationWeight.innerInverseOpHom (G := G) (e.symm y)) =
      RepresentationWeight.innerInverseOpHom (G := H) y
    simpa only [MulEquiv.apply_symm_apply] using
      opAutCongr_innerInverse e (e.symm y)

def literalOuterQuotientEquiv
    {G H : Type u} [Group G] [Group H] (e : G ≃* H) :
    LiteralOuterQuotient G ≃* LiteralOuterQuotient H :=
  QuotientGroup.congr
    (RepresentationWeight.innerInverseOpHom (G := G)).range
    (RepresentationWeight.innerInverseOpHom (G := H)).range
    (MulEquiv.op (MulAut.congr e)) (innerInverseRange_map_congr e)

theorem literalOuterQuotient_card_congr
    {G H : Type u} [Group G] [Group H] (e : G ≃* H) :
    Nat.card (LiteralOuterQuotient G) = Nat.card (LiteralOuterQuotient H) :=
  Nat.card_congr (literalOuterQuotientEquiv e).toEquiv

theorem ownOuterCardTwo_of_centerKernel
    (P : Definition35Problem.{u}) (psi : Definition35Brauer P)
    {S : Type u} [Group S] (q : P.H →* S)
    (hq : IsUniversalCentralExtension q)
    (hs : IsSimpleGroup S) (hna : ¬ IsMulCommutative S)
    (hZ0 : centralCharacterKernel P psi = Subgroup.center P.H)
    (hOuterS : Nat.card (LiteralOuterQuotient S) = 2) :
    Nat.card (LiteralOuterQuotient (CentralCharacterQuotient P psi)) = 2 := by
  let e : CentralCharacterQuotient P psi ≃* S :=
    QuotientGroup.liftEquiv (centralCharacterKernel P psi) hq.1.1
      (hZ0.trans (ker_eq_center_of_simple_quotient q hq.1 hs hna).symm)
  exact (literalOuterQuotient_card_congr e).trans hOuterS

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierLiteralOuterTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
