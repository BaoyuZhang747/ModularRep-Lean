import ModularRep.DefectNormalizerCarrier

/-!
# Finite subgroup sandwiches in a normalizer

This file contains only finite group cardinality and subgroup-containment
arguments.  Local subgroups of `N_G(P)` are compared with subgroups of `G`
only after applying the normalizer subtype map.
-/

namespace Subgroup

universe u

variable {G : Type u} [Group G]

/-- Conjugate subgroups of a finite group have the same cardinality. -/
theorem AreConjugate.card_eq [Finite G]
    {A B : Subgroup G} (h : A.AreConjugate B) :
    Nat.card A = Nat.card B := by
  rcases h with ⟨g, rfl⟩
  exact Subgroup.card_map_of_injective (K := B)
    (MulAut.conj g).injective

/-- If `P ≤ A`, `A` is conjugate to `B`, and `B ≤ P`, then `P = A`. -/
theorem eq_of_le_of_areConjugate_of_le [Finite G]
    {P A B : Subgroup G}
    (hPA : P ≤ A) (hAB : A.AreConjugate B) (hBP : B ≤ P) :
    P = A := by
  apply Subgroup.eq_of_le_of_card_ge hPA
  calc
    Nat.card A = Nat.card B := hAB.card_eq
    _ ≤ Nat.card P := Subgroup.card_le_of_le hBP

end Subgroup

namespace ModularRep

universe u

variable {G : Type u} [Group G]

/-- A subgroup of `N_G(P)` lying above the copy of `P`, whose ambient image
lies below a subgroup conjugate to `P`, is exactly that copy of `P`.

Both local subgroups are compared only after mapping them into `G`. -/
theorem defectSubgroupInNormalizer_eq_of_le_map_le_conjugate
    [Finite G] {P : Subgroup G}
    {D : Subgroup (defectNormalizer P)} {E : Subgroup G}
    (hPND : defectSubgroupInNormalizer P ≤ D)
    (hDE : D.map (defectNormalizer P).subtype ≤ E)
    (hEP : E.AreConjugate P) :
    D = defectSubgroupInNormalizer P := by
  have hP_le_Dmap : P ≤ D.map (defectNormalizer P).subtype := by
    calc
      P = (defectSubgroupInNormalizer P).map
          (defectNormalizer P).subtype :=
        (defectSubgroupInNormalizer_map_subtype P).symm
      _ ≤ D.map (defectNormalizer P).subtype :=
        Subgroup.map_mono hPND
  have hP_le_E : P ≤ E := hP_le_Dmap.trans hDE
  have hP_eq_E : P = E :=
    Subgroup.eq_of_le_of_areConjugate_of_le hP_le_E hEP le_rfl
  have hDmap_eq_P : D.map (defectNormalizer P).subtype = P := by
    apply le_antisymm
    · exact hDE.trans (le_of_eq hP_eq_E.symm)
    · exact hP_le_Dmap
  apply map_normalizerSubtype_injective (P := P)
  calc
    D.map (defectNormalizer P).subtype = P := hDmap_eq_P
    _ = (defectSubgroupInNormalizer P).map
          (defectNormalizer P).subtype :=
      (defectSubgroupInNormalizer_map_subtype P).symm

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
