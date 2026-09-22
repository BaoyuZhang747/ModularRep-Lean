import ModularRep.CentralClassSumExpansion
import ModularRep.BlockIdempotentInCenter
import ModularRep.Navarro415416RawClassSource
import ModularRep.NormalizerCentralBrauerClassSums

/-!
# Class-sum range adapter for Navarro (4.15)--(4.16)

The one raw E1 coefficient/intersection field is used locally to choose a
global class for each nonzero local class coefficient.  The finite selected
sum is then an actual preimage under the normalizer central Brauer map.  No
choice function is exported.
-/

namespace ModularRep

open scoped BigOperators MonoidAlgebra

noncomputable section

variable {p : Nat} {k G LocalBlock : Type*}
variable [Field k] [CharP k p] [IsAlgClosed k]
variable [Group G] [Fintype G] [Fintype LocalBlock] [Fact p.Prime]
variable {P : Subgroup G}
local instance classSumAdapterPropDecidable (Q : Prop) : Decidable Q :=
  Classical.propDecidable Q
variable {localBlockIdempotent :
  LocalBlock → k[defectNormalizer P]}
variable {localBlocks : BlockIdempotentDecomposition localBlockIdempotent}
variable {localHasDefect :
  LocalBlock → Subgroup (defectNormalizer P) → Prop}

omit [IsAlgClosed k] in
private theorem conjugacyClassSum_fintype_irrel
    {H : Type*} [Group H]
    (i₁ i₂ : Fintype H) (g : H) :
    @conjugacyClassSum k H _ _ i₁ g =
      @conjugacyClassSum k H _ _ i₂ g := by
  cases Subsingleton.elim i₁ i₂
  rfl

omit [IsAlgClosed k] in
private theorem centralClassSumExpansion_fintype_irrel
    {H : Type*} [Group H]
    (i₁ i₂ : Fintype H)
    (j₁ j₂ : Fintype (ConjClasses H))
    (z : GroupAlgebraCenter k H)
    (h :
      (@Finset.univ (ConjClasses H) j₁).sum (fun K ↦
        centralClassCoeff z K •
          @conjugacyClassSumOfClass k H _ _ i₁ K) = z) :
    (@Finset.univ (ConjClasses H) j₂).sum (fun K ↦
      centralClassCoeff z K •
        @conjugacyClassSumOfClass k H _ _ i₂ K) = z := by
  cases Subsingleton.elim i₁ i₂
  cases Subsingleton.elim j₁ j₂
  exact h

omit [IsAlgClosed k] [Fintype G] in
private theorem blockIdempotent_centralClassCoeff_eq_rawCoeff
    (b : LocalBlock) (K : ConjClasses (defectNormalizer P)) :
    centralClassCoeff (localBlocks.blockIdempotentInCenter b) K =
      ((localBlocks.primitiveBlockOfIndex b).1 :
        k[defectNormalizer P]).coeff (conjugacyClassRepresentative K) := by
  have hRepresentative :
      ConjClasses.mk (conjugacyClassRepresentative K) = K :=
    Classical.choose_spec (ConjClasses.exists_rep K)
  calc
    centralClassCoeff (localBlocks.blockIdempotentInCenter b) K =
        centralClassCoeff (localBlocks.blockIdempotentInCenter b)
          (ConjClasses.mk (conjugacyClassRepresentative K)) :=
      congrArg (centralClassCoeff (localBlocks.blockIdempotentInCenter b))
        hRepresentative.symm
    _ = ((localBlocks.primitiveBlockOfIndex b).1 :
          k[defectNormalizer P]).coeff
          (conjugacyClassRepresentative K) := rfl

omit [IsAlgClosed k] in
private theorem normalizerCentralBrauerMap_smul_conjugacyClassSum_eq
    [Fintype (defectNormalizer P)]
    (hP : IsPGroup p P)
    (e : GroupAlgebraCenter k (defectNormalizer P))
    (K : ConjClasses (defectNormalizer P)) (g : G)
    (hIntersection :
      ∀ x : defectNormalizer P,
        x ∈ (ConjClasses.mk (conjugacyClassRepresentative K)).carrier ↔
          ((x : G) ∈ (ConjClasses.mk g).carrier ∧
            (x : G) ∈ Subgroup.centralizer (P : Set G))) :
    normalizerCentralBrauerMap (k := k) (p := p) P hP
        (centralClassCoeff e K • conjugacyClassSum (k := k) g) =
      centralClassCoeff e K • conjugacyClassSumOfClass (k := k) K := by
  rw [map_smul]
  rw [normalizerCentralBrauerMap_conjugacyClassSum_eq_of_intersection
    (k := k) (p := p) P hP g (conjugacyClassRepresentative K)
      hIntersection]
  simp only [conjugacyClassSumOfClass]
  apply congrArg (fun z : GroupAlgebraCenter k (defectNormalizer P) ↦
    centralClassCoeff e K • z)
  apply conjugacyClassSum_fintype_irrel

private theorem exists_global_class_for_nonzero_block_coefficient
    (hP : IsPGroup p P)
    (S : Navarro415416RawClassSource P hP localBlocks localHasDefect)
    (b : LocalBlock)
    (hb : localHasDefect b (defectSubgroupInNormalizer P))
    (K : ConjClasses (defectNormalizer P))
    (hK : centralClassCoeff (localBlocks.blockIdempotentInCenter b) K ≠ 0) :
    ∃ g : G, ∀ x : defectNormalizer P,
      x ∈ (ConjClasses.mk (conjugacyClassRepresentative K)).carrier ↔
        ((x : G) ∈ (ConjClasses.mk g).carrier ∧
          (x : G) ∈ Subgroup.centralizer (P : Set G)) := by
  apply S.localP_nonzero_coeff_has_global_intersection b hb
  intro hzero
  apply hK
  exact (blockIdempotent_centralClassCoeff_eq_rawCoeff b K).trans hzero

private noncomputable def chosenGlobalClass
    (hP : IsPGroup p P)
    (S : Navarro415416RawClassSource P hP localBlocks localHasDefect)
    (b : LocalBlock)
    (hb : localHasDefect b (defectSubgroupInNormalizer P))
    (K : ConjClasses (defectNormalizer P)) : G := by
  classical
  exact if hK :
      centralClassCoeff (localBlocks.blockIdempotentInCenter b) K ≠ 0 then
    Classical.choose
      (exists_global_class_for_nonzero_block_coefficient hP S b hb K hK)
  else 1

private theorem chosenGlobalClass_spec
    (hP : IsPGroup p P)
    (S : Navarro415416RawClassSource P hP localBlocks localHasDefect)
    (b : LocalBlock)
    (hb : localHasDefect b (defectSubgroupInNormalizer P))
    (K : ConjClasses (defectNormalizer P))
    (hK :
      centralClassCoeff (localBlocks.blockIdempotentInCenter b) K ≠ 0) :
    ∀ x : defectNormalizer P,
      x ∈ (ConjClasses.mk (conjugacyClassRepresentative K)).carrier ↔
        ((x : G) ∈
            (ConjClasses.mk (chosenGlobalClass hP S b hb K)).carrier ∧
          (x : G) ∈ Subgroup.centralizer (P : Set G)) := by
  classical
  simpa only [chosenGlobalClass, dif_pos hK] using
    Classical.choose_spec
      (exists_global_class_for_nonzero_block_coefficient hP S b hb K hK)

private theorem normalizerCentralBrauerMap_chosenTerm_eq
    (hP : IsPGroup p P)
    (S : Navarro415416RawClassSource P hP localBlocks localHasDefect)
    (b : LocalBlock)
    (hb : localHasDefect b (defectSubgroupInNormalizer P))
    (K : ConjClasses (defectNormalizer P)) :
    normalizerCentralBrauerMap (k := k) (p := p) P hP
        (centralClassCoeff (localBlocks.blockIdempotentInCenter b) K •
          conjugacyClassSum (k := k) (chosenGlobalClass hP S b hb K)) =
      centralClassCoeff (localBlocks.blockIdempotentInCenter b) K •
        conjugacyClassSumOfClass (k := k) K := by
  classical
  by_cases hK :
      centralClassCoeff (localBlocks.blockIdempotentInCenter b) K ≠ 0
  · exact normalizerCentralBrauerMap_smul_conjugacyClassSum_eq
      hP (localBlocks.blockIdempotentInCenter b) K
        (chosenGlobalClass hP S b hb K)
        (chosenGlobalClass_spec hP S b hb K hK)
  · rw [map_smul]
    have hzero :
        centralClassCoeff (localBlocks.blockIdempotentInCenter b) K = 0 :=
      not_ne_iff.mp hK
    rw [hzero]
    simp

private noncomputable def normalizerCentralBrauerPreimage
    (hP : IsPGroup p P)
    (S : Navarro415416RawClassSource P hP localBlocks localHasDefect)
    (b : LocalBlock)
    (hb : localHasDefect b (defectSubgroupInNormalizer P)) :
    GroupAlgebraCenter k G := by
  classical
  exact ∑ K : ConjClasses (defectNormalizer P),
      centralClassCoeff (localBlocks.blockIdempotentInCenter b) K •
        conjugacyClassSum (k := k) (chosenGlobalClass hP S b hb K)

private theorem normalizerCentralBrauerMap_preimage_eq_expansion
    (hP : IsPGroup p P)
    (S : Navarro415416RawClassSource P hP localBlocks localHasDefect)
    (b : LocalBlock)
    (hb : localHasDefect b (defectSubgroupInNormalizer P)) :
    normalizerCentralBrauerMap (k := k) (p := p) P hP
        (normalizerCentralBrauerPreimage hP S b hb) =
      ∑ K : ConjClasses (defectNormalizer P),
        centralClassCoeff (localBlocks.blockIdempotentInCenter b) K •
          conjugacyClassSumOfClass (k := k) K := by
  classical
  rw [normalizerCentralBrauerPreimage, map_sum]
  apply Finset.sum_congr rfl
  intro K _
  exact normalizerCentralBrauerMap_chosenTerm_eq hP S b hb K

omit [IsAlgClosed k] in
private theorem blockIdempotent_centralClassSumExpansion
    (b : LocalBlock) :
    (∑ K : ConjClasses (defectNormalizer P),
      centralClassCoeff (localBlocks.blockIdempotentInCenter b) K •
        conjugacyClassSumOfClass (k := k) K) =
      localBlocks.blockIdempotentInCenter b := by
  apply centralClassSumExpansion_fintype_irrel
  exact centralClassSumExpansion (localBlocks.blockIdempotentInCenter b)

private theorem normalizerCentralBrauerMap_preimage_eq_blockIdempotent
    (hP : IsPGroup p P)
    (S : Navarro415416RawClassSource P hP localBlocks localHasDefect)
    (b : LocalBlock)
    (hb : localHasDefect b (defectSubgroupInNormalizer P)) :
    normalizerCentralBrauerMap (k := k) (p := p) P hP
        (normalizerCentralBrauerPreimage hP S b hb) =
      localBlocks.blockIdempotentInCenter b := by
  exact (normalizerCentralBrauerMap_preimage_eq_expansion hP S b hb).trans
    (blockIdempotent_centralClassSumExpansion b)

/-- A local block idempotent with the nominated local defect lies in the
actual range of the normalizer central Brauer map. -/
theorem Navarro415416RawClassSource.localBlockIdempotent_mem_normalizerCentralBrauerMap_range
    (hP : IsPGroup p P)
    (S : Navarro415416RawClassSource P hP localBlocks localHasDefect)
    (b : LocalBlock)
    (hb : localHasDefect b (defectSubgroupInNormalizer P)) :
    localBlocks.blockIdempotentInCenter b ∈
      LinearMap.range
        (normalizerCentralBrauerMap (k := k) (p := p) P hP).toLinearMap := by
  exact ⟨normalizerCentralBrauerPreimage hP S b hb,
    normalizerCentralBrauerMap_preimage_eq_blockIdempotent hP S b hb⟩

end

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
