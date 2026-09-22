import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnNormalizerBrauer
import ModularRep.CentralBrauerInterval

/-! Literal quotient-kernel, saturation and interval facts for the same
own-character quotient and same raw weight. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnQuotientGroupFacts

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralNormalizer
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnNormalizerBrauer

universe u
variable (P : Definition35Problem.{u}) (psi : Definition35Brauer P)
variable (V : CharacterWeight P.p P.K P.H)

local instance problemPrime : Fact P.p.Prime := ⟨P.iota.prime⟩

theorem own_quotient_ker :
    (centralCharacterQuotientMap P psi).ker = centralCharacterKernel P psi :=
  QuotientGroup.ker_mk' _

theorem own_quotient_ker_central :
    (centralCharacterQuotientMap P psi).ker ≤ Subgroup.center P.H := by
  rw [own_quotient_ker]
  exact inf_le_left

theorem own_quotient_ker_primeTo
    (hprimeTo : ¬ P.p ∣ Nat.card (centralCharacterKernel P psi)) :
    ¬ P.p ∣ Nat.card (centralCharacterQuotientMap P psi).ker := by
  rwa [own_quotient_ker]

theorem own_normalizer_ker_central :
    (ownNormalizerMap P psi V).ker ≤
      Subgroup.center (Subgroup.normalizer (V.subgroup : Set P.H)) := by
  rw [ownNormalizerMap, centralNormalizerMap_ker]
  exact subgroupOf_le_center _ _ inf_le_left

theorem own_normalizer_ker_card :
    Nat.card (ownNormalizerMap P psi V).ker = Nat.card (centralCharacterKernel P psi) := by
  rw [ownNormalizerMap, centralNormalizerMap_ker]
  exact Nat.card_congr
    (localCentralKernelEquiv (centralCharacterKernel P psi) V.subgroup inf_le_left).toEquiv

theorem own_normalizer_ker_primeTo
    (hprimeTo : ¬ P.p ∣ Nat.card (centralCharacterKernel P psi)) :
    ¬ P.p ∣ Nat.card (ownNormalizerMap P psi V).ker := by
  rwa [own_normalizer_ker_card]

variable (hprimeTo : ¬ P.p ∣ Nat.card (centralCharacterKernel P psi))
variable (normalizers : NavarroTiep23cFixedCentralQuotientSource
  (centralCharacterKernel P psi) (show centralCharacterKernel P psi ≤ Subgroup.center P.H from inf_le_left)
  hprimeTo V.subgroup V.radical)

include hprimeTo normalizers in
theorem own_normalizer_saturated (g : P.H) :
    g ∈ Subgroup.normalizer (V.subgroup : Set P.H) ↔
      centralCharacterQuotientMap P psi g ∈
        Subgroup.normalizer (V.subgroup.map (centralCharacterQuotientMap P psi) :
          Set (CentralCharacterQuotient P psi)) := by
  let N := Subgroup.normalizer (V.subgroup : Set P.H)
  let Nbar := Subgroup.normalizer (V.subgroup.map (centralCharacterQuotientMap P psi) :
    Set (CentralCharacterQuotient P psi))
  have hker : (centralCharacterQuotientMap P psi).ker ≤ N :=
    (own_quotient_ker_central P psi).trans (Subgroup.center_le_normalizer (V.subgroup : Set P.H))
  have hpre : Nbar.comap (centralCharacterQuotientMap P psi) = N := by
    rw [show Nbar = N.map (centralCharacterQuotientMap P psi) from normalizers.normalizer_image.symm,
      Subgroup.comap_map_eq_self hker]
  change g ∈ N ↔ g ∈ Nbar.comap (centralCharacterQuotientMap P psi)
  rw [hpre]

include hprimeTo normalizers in
theorem ownNormalizerInterval :
    CentralBrauerInterval (p := P.p)
      (V.subgroup.map (centralCharacterQuotientMap P psi))
      (Subgroup.normalizer (V.subgroup.map (centralCharacterQuotientMap P psi) :
        Set (CentralCharacterQuotient P psi))) := by
  exact {
    isPGroup := normalizers.radical_image.isPGroup
    pCentralizer_le := sup_le (V.subgroup.map (centralCharacterQuotientMap P psi)).le_normalizer
      (Subgroup.centralizer_le_normalizer _)
    le_normalizer := le_rfl }

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnQuotientGroupFacts


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
