import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnQuotientAutomorphisms

/-! An ambient carrier using the original group's Brauer stabilizer.
This is an internal literal target, not a source interface. Its raw map
has the exact central character kernel; injectivity of that raw map is
not required when the kernel is nontrivial. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalAmbient

open ModularRep
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnQuotientAutomorphisms

universe u

structure OriginalSpathAmbient (P : Definition35Problem.{u}) (psi : Definition35Brauer P) where
  A : Type u
  [groupA : Group A]
  [fintypeA : Fintype A]
  base : Subgroup A
  [baseNormal : base.Normal]
  baseEquiv : CentralCharacterQuotient P psi ≃* base
  baseCentralizer_eq_center : Subgroup.centralizer (base : Set A) = Subgroup.center A
  centerPrimeTo : ¬ P.p ∣ Nat.card (Subgroup.center A)
  originalConjugation : A →* MulAut P.H
  conjugation_on_base : ∀ (a : A) (x : P.H),
    (baseEquiv (centralCharacterQuotientMap P psi (originalConjugation a x)) : A) =
      a * (baseEquiv (centralCharacterQuotientMap P psi x) : A) * a⁻¹
  automorphismQuotientEquiv : A ⧸ Subgroup.center A ≃*
    MulAction.stabilizer (MulAut P.H)ᵐᵒᵖ psi.1
  automorphismQuotientEquiv_natural : ∀ a : A,
    (automorphismQuotientEquiv (QuotientGroup.mk' (Subgroup.center A) a)).1 =
      inverseOpHom originalConjugation a

attribute [instance] OriginalSpathAmbient.groupA OriginalSpathAmbient.fintypeA
  OriginalSpathAmbient.baseNormal

namespace OriginalSpathAmbient

variable {P : Definition35Problem.{u}} {psi : Definition35Brauer P}
variable (B : OriginalSpathAmbient P psi)

def quotientEmbedding : CentralCharacterQuotient P psi →* B.A :=
  B.base.subtype.comp B.baseEquiv.toMonoidHom

theorem quotientEmbedding_injective : Function.Injective B.quotientEmbedding := by
  intro x y h
  apply B.baseEquiv.injective
  exact Subtype.ext h

def rawMap : P.H →* B.A := B.quotientEmbedding.comp (centralCharacterQuotientMap P psi)

theorem rawMap_ker : B.rawMap.ker = centralCharacterKernel P psi := by
  ext x
  change B.quotientEmbedding (centralCharacterQuotientMap P psi x) = 1 ↔
    x ∈ centralCharacterKernel P psi
  constructor
  · intro h
    have hx : centralCharacterQuotientMap P psi x = 1 := by
      apply B.quotientEmbedding_injective
      simpa only [map_one] using h
    exact (QuotientGroup.eq_one_iff x).mp hx
  · intro h
    have hx : centralCharacterQuotientMap P psi x = 1 :=
      (QuotientGroup.eq_one_iff x).mpr h
    rw [hx, map_one]

end OriginalSpathAmbient

def identityOriginalAmbient (P : Definition35Problem.{u}) (psi : Definition35Brauer P)
    [Group.IsPerfect P.H]
    (hcenter : ¬ P.p ∣ Nat.card (Subgroup.center P.H))
    (allInner : ∀ a : MulAut P.H, ∃ x : P.H, a = MulAut.conj x) :
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
  automorphismQuotientEquiv := originalStabilizerEquiv P psi allInner
  automorphismQuotientEquiv_natural := by
    intro a
    rw [originalStabilizerEquiv_mk]
    exact originalAction_coe P psi a

theorem identityOriginalAmbient_base (P : Definition35Problem.{u}) (psi : Definition35Brauer P)
    [Group.IsPerfect P.H]
    (hcenter : ¬ P.p ∣ Nat.card (Subgroup.center P.H))
    (allInner : ∀ a : MulAut P.H, ∃ x : P.H, a = MulAut.conj x) :
    (identityOriginalAmbient P psi hcenter allInner).base = ⊤ := rfl

theorem identityOriginalAmbient_rawMap (P : Definition35Problem.{u}) (psi : Definition35Brauer P)
    [Group.IsPerfect P.H]
    (hcenter : ¬ P.p ∣ Nat.card (Subgroup.center P.H))
    (allInner : ∀ a : MulAut P.H, ∃ x : P.H, a = MulAut.conj x) :
    (identityOriginalAmbient P psi hcenter allInner).rawMap = centralCharacterQuotientMap P psi := rfl

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalAmbient


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
