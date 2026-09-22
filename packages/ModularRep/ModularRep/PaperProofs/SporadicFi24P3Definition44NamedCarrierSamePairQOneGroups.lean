import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualNormalizerBase

/-! Q=1 geometry for the exact retained local ambient subgroup. -/
noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSamePairQOneGroups

open ModularRep
open SporadicFi24P3Definition44NamedCarrierActualNormalizerBase
universe u
variable {G A : Type u} [Group G] [Group A]

def ambientEquivOfEqTop (D : Subgroup A) (hD : D = ⊤) : D ≃* A :=
  (MulEquiv.subgroupCongr hD).trans Subgroup.topEquiv

theorem ambientEquivOfEqTop_toMonoidHom (D : Subgroup A) (hD : D = ⊤) :
    (ambientEquivOfEqTop D hD).toMonoidHom = D.subtype := by
  ext x
  rfl

theorem embeddedNormalizer_eq_top (i : G →* A) (Q : Subgroup G) (hQ : Q = ⊥) :
    embeddedNormalizer i Q = ⊤ := by
  change Subgroup.normalizer (Q.map i : Set A) = ⊤
  rw [hQ, Subgroup.map_bot]
  exact Subgroup.normalizer_eq_top (⊥ : Subgroup A)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSamePairQOneGroups


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
