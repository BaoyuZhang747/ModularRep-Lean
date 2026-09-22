import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPCoreDefectContainment
import ModularRep.Navarro417FirstParagraphUpperDefectSource

/-! A numerical local defect bound identifies the normal copy of the radical.
The computed induced block then has that same ambient defect: its own central
character supplies the lower support, and the uniform First Main upper witness
supplies the opposite containment. No ambient block role is an input. -/

noncomputable section
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3LocalDefectCore
open ModularRep
open SporadicFi24P3Definition44NamedCarrierPCoreDefectContainment

local instance normalizerFintype {G : Type*} [Group G] [Fintype G]
    (P : Subgroup G) : Fintype (defectNormalizer P) := Fintype.ofFinite _

theorem normalizerCopy_card {G : Type*} [Group G] (P : Subgroup G) :
    Nat.card (defectSubgroupInNormalizer P) = Nat.card P := by
  calc
    Nat.card (defectSubgroupInNormalizer P) =
        Nat.card ((defectSubgroupInNormalizer P).map
          (defectNormalizer P).subtype) :=
      (Subgroup.card_map_of_injective
        (K := defectSubgroupInNormalizer P)
        (defectNormalizer P).subtype_injective).symm
    _ = Nat.card P := by rw [defectSubgroupInNormalizer_map_subtype]

theorem localHasDefect_copy_of_card_bound
    {p : ℕ} {k G B : Type*}
    [Field k] [CharP k p] [IsAlgClosed k]
    [Group G] [Fintype G] [Fintype B] [Fact p.Prime]
    (P : Subgroup G) (hP : IsPGroup p P)
    {e : B → k[defectNormalizer P]}
    (blocks : BlockIdempotentDecomposition e)
    (existence : Navarro417LocalDefectExistenceSource P blocks)
    (b : B)
    (bound : ∀ D, navarro417LocalHasDefect (p := p) blocks b D →
      Nat.card D ≤ Nat.card P) :
    navarro417LocalHasDefect (p := p) blocks b
      (defectSubgroupInNormalizer P) := by
  obtain ⟨D, hD⟩ := existence.exists_representative b
  have hle : defectSubgroupInNormalizer P ≤ D :=
    (defectSubgroupInNormalizer_le_pCore hP).trans
      ((navarro408PCoreDefectSource P blocks).pCore_le_representative hD)
  have hcard : Nat.card D ≤ Nat.card (defectSubgroupInNormalizer P) :=
    (bound D hD).trans_eq (normalizerCopy_card P).symm
  have heq : defectSubgroupInNormalizer P = D :=
    Subgroup.eq_of_le_of_card_ge hle hcard
  rw [← heq] at hD
  exact hD

theorem localHasDefect_copy_of_defectOrder
    {p : ℕ} {k G B : Type*}
    [Field k] [CharP k p] [IsAlgClosed k]
    [Group G] [Fintype G] [Fintype B] [Fact p.Prime]
    (P : Subgroup G) (hP : IsPGroup p P)
    {e : B → k[defectNormalizer P]}
    (blocks : BlockIdempotentDecomposition e)
    (existence : Navarro417LocalDefectExistenceSource P blocks)
    (defectExponent : B → ℕ)
    (orderLaw : ∀ b D, navarro417LocalHasDefect (p := p) blocks b D →
      Nat.card D = p ^ defectExponent b)
    (b : B) (hcard : p ^ defectExponent b ≤ Nat.card P) :
    navarro417LocalHasDefect (p := p) blocks b
      (defectSubgroupInNormalizer P) := by
  apply localHasDefect_copy_of_card_bound P hP blocks existence b
  intro D hD
  exact (orderLaw b D hD).le.trans hcard

theorem inducedBlock_has_nonzero_support
    {p : ℕ} {k G L A : Type*}
    [Field k] [CharP k p] [IsAlgClosed k]
    [Group G] [Fintype G] [Fintype L] [Fintype A] [Fact p.Prime]
    (P : Subgroup G) (hP : IsPGroup p P)
    {el : L → k[defectNormalizer P]} {ea : A → k[G]}
    (localBlocks : BlockIdempotentDecomposition el)
    (ambientBlocks : BlockIdempotentDecomposition ea)
    (localCatalogue : BlockCentralCharacterCatalogue localBlocks)
    (S414 : Navarro414IntervalCentralCharacterSource
      (normalizerCentralBrauerInterval hP) localBlocks localCatalogue)
    (ambientCatalogue : BlockCentralCharacterCatalogue ambientBlocks) (b : L) :
    HasNonzeroCentralBrauerRestriction ambientBlocks
      (navarro414InducedBlock S414 ambientCatalogue b) P := by
  let B := navarro414InducedBlock S414 ambientCatalogue b
  let z := ambientBlocks.blockIdempotentInCenter B
  have hcc := congrArg (fun f : GroupAlgebraCenter k G →ₐ[k] k => f z)
    (navarro414InducedBlock_centralCharacter S414 ambientCatalogue b)
  have hv : localCatalogue.centralCharacter b
      (centralBrauerMapTo (k := k) (p := p) P (defectNormalizer P) hP
        (Subgroup.centralizer_le_normalizer (P : Set G)) le_rfl z) = 1 :=
    hcc.symm.trans (ambientCatalogue.centralCharacter_own B)
  have hn : centralBrauerMapTo (k := k) (p := p) P (defectNormalizer P) hP
      (Subgroup.centralizer_le_normalizer (P : Set G)) le_rfl z ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hv
    exact zero_ne_one hv
  apply (hasNonzeroCentralBrauerRestriction_iff_map_ne_zero
    (p := p) ambientBlocks B P hP).2
  intro hz
  apply hn
  apply Subtype.ext
  change ((centralBrauerMapTo (k := k) (p := p) P (defectNormalizer P) hP
    (Subgroup.centralizer_le_normalizer (P : Set G)) le_rfl z :
      GroupAlgebraCenter k (defectNormalizer P)) : k[defectNormalizer P]) = 0
  rw [centralBrauerMapTo_apply, hz, Subalgebra.coe_zero, map_zero]

theorem inducedBlock_has_exact_defect
    {p : ℕ} {k G L A : Type*}
    [Field k] [CharP k p] [IsAlgClosed k]
    [Group G] [Fintype G] [Fintype L] [Fintype A] [Fact p.Prime]
    (P : Subgroup G) (hP : IsPGroup p P)
    {el : L → k[defectNormalizer P]} {ea : A → k[G]}
    (localBlocks : BlockIdempotentDecomposition el)
    (ambientBlocks : BlockIdempotentDecomposition ea)
    (localCatalogue : BlockCentralCharacterCatalogue localBlocks)
    (S414 : Navarro414IntervalCentralCharacterSource
      (normalizerCentralBrauerInterval hP) localBlocks localCatalogue)
    (ambientCatalogue : BlockCentralCharacterCatalogue ambientBlocks)
    (upper : Navarro417FirstParagraphUpperDefectSource P hP
      localBlocks ambientBlocks localCatalogue S414 ambientCatalogue)
    (b : L) (hb : navarro417LocalHasDefect (p := p) localBlocks b
      (defectSubgroupInNormalizer P)) :
    navarro417AmbientHasDefect (p := p) ambientBlocks
      (navarro414InducedBlock S414 ambientCatalogue b) P := by
  obtain ⟨E, hE, hEP⟩ := upper.localP_selectedInduction_has_ambient_defect_le b hb
  have hPE : P.IsSubconjugate E :=
    (hE.support411.nonzero_iff_isSubconjugate P hP).mp
      (inducedBlock_has_nonzero_support P hP localBlocks ambientBlocks
        localCatalogue S414 ambientCatalogue b)
  have heq : E = P := hPE.eq_of_le hEP
  simpa only [heq] using hE

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3LocalDefectCore


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
