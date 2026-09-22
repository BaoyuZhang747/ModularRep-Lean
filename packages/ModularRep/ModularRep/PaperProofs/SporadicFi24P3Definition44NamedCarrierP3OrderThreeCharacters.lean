import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3OrderThreeData
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3FullOrdinaryCharacters
import ModularRep.PaperProofs.CharacterWeightRepresentativeFibre

/-! Complete degree coverage of the actual normalizer quotient excludes
local defect-zero characters. No enumeration of distinct actual characters,
splitting-field hypothesis or supplied defect-zero conclusion is required. -/

noncomputable section
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3OrderThreeCharacters
open ModularRep ModularRep.CharacterWeight
open SporadicFi24P3Definition44NamedCarrierP3OrderThreeData
open SporadicFi24P3Definition44NamedCarrierP3FullOrdinaryCharacters

universe u
variable {K H : Type u} [Field K] [CharZero K] [Group H] [Fintype H]

theorem not_defectZero_of_degree_cover
    (hOrder : Nat.card H = 29713078886400)
    (degreeCover : ∀ chi : OrdinaryIrreducibleCharacter.Irr K H,
      ∃ r : Fin 125, chi 1 = (quotientDegrees r : K))
    (chi : OrdinaryIrreducibleCharacter.Irr K H) :
    ¬ IsDefectZeroOrdinaryCharacter 3 chi := by
  intro hz
  obtain ⟨r, hr⟩ := degreeCover chi
  have hpart := (ordinary_defectZero_iff_degree 3 chi (quotientDegrees r) hr).mp hz
  have hdvd := Nat.ordProj_dvd (quotientDegrees r) 3
  rw [hpart, hOrder, quotient_order_three_part] at hdvd
  exact full_part_not_dvd_degree r hdvd

theorem local_defectZero_isEmpty
    {G : Type u} [Group G] [Fintype G]
    (U : RadicalSubgroup (p := 3) (G := G))
    (hOrder : Nat.card (NormalizerQuotient U.1) = 29713078886400)
    (degreeCover : ∀ chi : OrdinaryIrreducibleCharacter.Irr K (NormalizerQuotient U.1),
      ∃ r : Fin 125, chi 1 = (quotientDegrees r : K)) :
    IsEmpty (LocalDefectZeroCharacter (K := K) U) := by
  let _ : Fintype (NormalizerQuotient U.1) := Fintype.ofFinite _
  exact ⟨fun theta => not_defectZero_of_degree_cover hOrder degreeCover theta.1 theta.2⟩

theorem radicalClass_ne_of_empty_local
    {G : Type u} [Group G] [Fintype G]
    (U : RadicalSubgroup (p := 3) (G := G))
    (hEmpty : IsEmpty (LocalDefectZeroCharacter (K := K) U))
    (w : ConjugacyClass (p := 3) (K := K) (G := G)) :
    radicalClass w ≠
      (Quotient.mk'' U : RadicalConjugacyClass (p := 3) (G := G)) := by
  intro hw
  let _ := hEmpty
  exact isEmptyElim
    ((localDefectZeroEquivWeightRadicalFibre (K := K) (by decide) U).symm ⟨w, hw⟩)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3OrderThreeCharacters


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
