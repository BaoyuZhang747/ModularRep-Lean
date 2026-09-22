import ModularRep.Navarro415416ClassSumAdapter
import ModularRep.Navarro417PhaseASupport

/-!
# Restricted injectivity for Navarro (4.17)

The repaired raw Navarro (4.15)--(4.16) source puts each nominated local
block idempotent in the actual range of the normalizer central Brauer map.
Together with the Phase-A central character equality, this separates a local
block of literal normalizer defect from every other local block with the same
selected induced target.  Canonical support then gives the singleton image
and the corresponding block-idempotent equality.

This layer assumes no existence of defect representatives, p-core theorem,
mapped defect containment, upper defect bound, sector coverage, or block
equivalence.
-/

namespace ModularRep

open scoped BigOperators MonoidAlgebra

noncomputable section

/-- Equal composites agree on every element in the linear range of the
intermediate algebra homomorphism. -/
theorem algHom_eq_on_of_comp_eq_of_mem_linearRange
    {R A B : Type*}
    [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) (lambda mu : B →ₐ[R] R)
    (hcomp : lambda.comp f = mu.comp f)
    {y : B} (hy : y ∈ LinearMap.range f.toLinearMap) :
    lambda y = mu y := by
  rcases hy with ⟨x, hx⟩
  have heval := congrArg (fun phi : A →ₐ[R] R ↦ phi x) hcomp
  change lambda (f x) = mu (f x) at heval
  change f x = y at hx
  rw [hx] at heval
  exact heval

variable {p : Nat} {k G LocalBlock AmbientBlock : Type*}
variable [Field k] [CharP k p] [IsAlgClosed k]
variable [Group G] [Fintype G]
variable [Fintype LocalBlock] [Fintype AmbientBlock] [Fact p.Prime]
variable {P : Subgroup G}

local instance : Fintype (defectNormalizer P) := Fintype.ofFinite _

variable {localBlockIdempotent :
  LocalBlock → k[defectNormalizer P]}
variable {ambientBlockIdempotent : AmbientBlock → k[G]}

/-- If the left local block has literal defect `P` on the normalizer carrier,
then no other local block has the same Phase-A selected target. -/
theorem navarro417PhaseAInductionMap_eq_imp_eq_of_localP_left
    (hP : IsPGroup p P)
    (localBlocks : BlockIdempotentDecomposition localBlockIdempotent)
    (localHasDefect :
      LocalBlock → Subgroup (defectNormalizer P) → Prop)
    {ambientBlocks : BlockIdempotentDecomposition ambientBlockIdempotent}
    (localCatalogue : BlockCentralCharacterCatalogue localBlocks)
    (S414 : Navarro414IntervalCentralCharacterSource
      (normalizerCentralBrauerInterval (p := p) hP)
      localBlocks localCatalogue)
    (ambientCatalogue : BlockCentralCharacterCatalogue ambientBlocks)
    (S415416 : Navarro415416RawClassSource
      P hP localBlocks localHasDefect)
    {b₁ b₂ : LocalBlock}
    (hb₁ : localHasDefect b₁ (defectSubgroupInNormalizer P))
    (hTarget :
      navarro417PhaseAInductionMap hP S414 ambientCatalogue b₁ =
        navarro417PhaseAInductionMap hP S414 ambientCatalogue b₂) :
    b₁ = b₂ := by
  classical
  have hCharacter₁ :=
    navarro414InducedBlock_centralCharacter S414 ambientCatalogue b₁
  have hCharacter₂ :=
    navarro414InducedBlock_centralCharacter S414 ambientCatalogue b₂
  have hAmbient :
      ambientCatalogue.centralCharacter
          (navarro417PhaseAInductionMap hP S414 ambientCatalogue b₁) =
        ambientCatalogue.centralCharacter
          (navarro417PhaseAInductionMap hP S414 ambientCatalogue b₂) :=
    congrArg ambientCatalogue.centralCharacter hTarget
  have hComp :
      (localCatalogue.centralCharacter b₁).comp
          (normalizerCentralBrauerMap (k := k) (p := p) P hP) =
        (localCatalogue.centralCharacter b₂).comp
          (normalizerCentralBrauerMap (k := k) (p := p) P hP) := by
    exact hCharacter₁.symm.trans (hAmbient.trans hCharacter₂)
  have hRange :=
    S415416.localBlockIdempotent_mem_normalizerCentralBrauerMap_range
      hP b₁ hb₁
  have hEval := algHom_eq_on_of_comp_eq_of_mem_linearRange
    (normalizerCentralBrauerMap (k := k) (p := p) P hP)
    (localCatalogue.centralCharacter b₁)
    (localCatalogue.centralCharacter b₂) hComp hRange
  by_contra hNe
  have hOther :=
    localCatalogue.centralCharacter_other (Ne.symm hNe)
  have hImpossible : (1 : k) = 0 := by
    calc
      1 = localCatalogue.centralCharacter b₁
          (localBlocks.blockIdempotentInCenter b₁) :=
        (localCatalogue.centralCharacter_own b₁).symm
      _ = localCatalogue.centralCharacter b₂
          (localBlocks.blockIdempotentInCenter b₁) := hEval
      _ = 0 := hOther
  exact one_ne_zero hImpossible

/-- For a local block of literal normalizer defect, the canonical support of
the image of its selected ambient target is exactly that one local block. -/
theorem navarro417PhaseANormalizerSupport_selected_eq_singleton
    (hP : IsPGroup p P)
    (localBlocks : BlockIdempotentDecomposition localBlockIdempotent)
    (localHasDefect :
      LocalBlock → Subgroup (defectNormalizer P) → Prop)
    (ambientBlocks : BlockIdempotentDecomposition ambientBlockIdempotent)
    (localCatalogue : BlockCentralCharacterCatalogue localBlocks)
    (S414 : Navarro414IntervalCentralCharacterSource
      (normalizerCentralBrauerInterval (p := p) hP)
      localBlocks localCatalogue)
    (ambientCatalogue : BlockCentralCharacterCatalogue ambientBlocks)
    (S415416 : Navarro415416RawClassSource
      P hP localBlocks localHasDefect)
    (b : LocalBlock)
    (hb : localHasDefect b (defectSubgroupInNormalizer P)) :
    navarro417PhaseANormalizerSupport hP localBlocks ambientBlocks
        (navarro417PhaseAInductionMap hP S414 ambientCatalogue b) =
      {b} := by
  classical
  apply Finset.ext
  intro C
  rw [Finset.mem_singleton]
  constructor
  · intro hC
    have hSameTarget :=
      (mem_navarro417PhaseANormalizerSupport_iff_inductionMap_eq
        hP localBlocks ambientBlocks localCatalogue S414 ambientCatalogue
        (navarro417PhaseAInductionMap hP S414 ambientCatalogue b) C).1 hC
    exact (navarro417PhaseAInductionMap_eq_imp_eq_of_localP_left
      (b₁ := b) (b₂ := C) hP localBlocks localHasDefect localCatalogue S414
        ambientCatalogue S415416 hb hSameTarget.symm).symm
  · intro hCb
    subst C
    exact (mem_navarro417PhaseANormalizerSupport_iff_inductionMap_eq
      hP localBlocks ambientBlocks localCatalogue S414 ambientCatalogue
      (navarro417PhaseAInductionMap hP S414 ambientCatalogue b) b).2 rfl

/-- The normalizer central Brauer image of the selected ambient block
idempotent is the original local block idempotent. -/
theorem normalizerCentralBrauerMap_selectedBlockIdempotent_eq
    (hP : IsPGroup p P)
    (localBlocks : BlockIdempotentDecomposition localBlockIdempotent)
    (localHasDefect :
      LocalBlock → Subgroup (defectNormalizer P) → Prop)
    (ambientBlocks : BlockIdempotentDecomposition ambientBlockIdempotent)
    (localCatalogue : BlockCentralCharacterCatalogue localBlocks)
    (S414 : Navarro414IntervalCentralCharacterSource
      (normalizerCentralBrauerInterval (p := p) hP)
      localBlocks localCatalogue)
    (ambientCatalogue : BlockCentralCharacterCatalogue ambientBlocks)
    (S415416 : Navarro415416RawClassSource
      P hP localBlocks localHasDefect)
    (b : LocalBlock)
    (hb : localHasDefect b (defectSubgroupInNormalizer P)) :
    normalizerCentralBrauerMap (k := k) (p := p) P hP
        (ambientBlocks.blockIdempotentInCenter
          (navarro417PhaseAInductionMap hP S414 ambientCatalogue b)) =
      localBlocks.blockIdempotentInCenter b := by
  have hSupport :=
    navarro417PhaseANormalizerSupport_selected_eq_singleton
      hP localBlocks localHasDefect ambientBlocks localCatalogue S414
      ambientCatalogue S415416 b hb
  have hSum := sum_centralBrauerMapToLocalSupport_eq
    P (defectNormalizer P) hP
    (Subgroup.centralizer_le_normalizer (P : Set G)) le_rfl
    (ambientBlocks.primitiveBlockOfIndex
      (navarro417PhaseAInductionMap hP S414 ambientCatalogue b))
    localBlocks
  change (∑ C ∈ navarro417PhaseANormalizerSupport hP localBlocks
      ambientBlocks
        (navarro417PhaseAInductionMap hP S414 ambientCatalogue b),
      localBlockIdempotent C) =
    centralBrauerMapToPrimitiveImage P (defectNormalizer P) hP
      (Subgroup.centralizer_le_normalizer (P : Set G)) le_rfl
      (ambientBlocks.primitiveBlockOfIndex
        (navarro417PhaseAInductionMap hP S414 ambientCatalogue b)) at hSum
  rw [hSupport] at hSum
  simp only [Finset.sum_singleton] at hSum
  apply Subtype.ext
  change ((normalizerCentralBrauerMap (k := k) (p := p) P hP
      (ambientBlocks.blockIdempotentInCenter
        (navarro417PhaseAInductionMap hP S414 ambientCatalogue b)) :
      GroupAlgebraCenter k (defectNormalizer P)) :
    k[defectNormalizer P]) = localBlockIdempotent b
  rw [← navarro417PhaseAPrimitiveImage_eq_normalizerMap
    (k := k) (p := p) hP ambientBlocks
      (navarro417PhaseAInductionMap hP S414 ambientCatalogue b)]
  exact hSum.symm

end

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
