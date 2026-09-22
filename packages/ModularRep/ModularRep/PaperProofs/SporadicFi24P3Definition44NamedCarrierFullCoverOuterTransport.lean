import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCoverAutomorphismEquiv
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualOuterQuotient

/-! The same full cover transports its actual opposite outer quotient. -/
noncomputable section
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCoverOuterTransport
open ModularRep
open EvenFieldFLZ318FixedTheoremGate
open SporadicFi24P3Definition44NamedCarrierFullCoverAutomorphismEquiv
open SporadicFi24P3Definition44NamedCarrierActualOuterQuotient

universe u
variable {X S : Type u} [Group X] [Group S]
variable (q : X →* S) (hq : IsUniversalCentralExtension q)
variable (hk : q.ker = Subgroup.center X)

theorem fullCoverOpAut_innerInverse (x : X) :
    MulEquiv.op (fullCoverAutEquiv q hq hk)
        (RepresentationWeight.innerInverseOpHom (G := X) x) =
      RepresentationWeight.innerInverseOpHom (G := S) (q x) := by
  apply MulOpposite.unop_injective
  change fullCoverAutEquiv q hq hk (MulAut.conj x⁻¹) = MulAut.conj ((q x)⁻¹)
  simpa only [map_inv] using fullCoverAutEquiv_conj q hq hk x⁻¹

theorem fullCover_innerInverseRange_map :
    (RepresentationWeight.innerInverseOpHom (G := X)).range.map
        (MulEquiv.op (fullCoverAutEquiv q hq hk)).toMonoidHom =
      (RepresentationWeight.innerInverseOpHom (G := S)).range := by
  ext a
  constructor
  · rintro ⟨b, ⟨x, rfl⟩, rfl⟩
    exact ⟨q x, (fullCoverOpAut_innerInverse q hq hk x).symm⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := hq.1.1 y
    exact ⟨RepresentationWeight.innerInverseOpHom (G := X) x,
      ⟨x, rfl⟩, fullCoverOpAut_innerInverse q hq hk x⟩

def fullCoverLiteralOuterEquiv : LiteralOuterQuotient X ≃* LiteralOuterQuotient S :=
  QuotientGroup.congr
    (RepresentationWeight.innerInverseOpHom (G := X)).range
    (RepresentationWeight.innerInverseOpHom (G := S)).range
    (MulEquiv.op (fullCoverAutEquiv q hq hk))
    (fullCover_innerInverseRange_map q hq hk)

include q hq hk in
theorem fullCoverLiteralOuter_card :
    Nat.card (LiteralOuterQuotient X) = Nat.card (LiteralOuterQuotient S) :=
  Nat.card_congr (fullCoverLiteralOuterEquiv q hq hk).toEquiv

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCoverOuterTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
