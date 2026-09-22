import ModularRep.PaperProofs.TypeBRankThreeNonprincipalSeriesBinding
import ModularRep.PaperProofs.TypeBRankThreeJordanPacketCarriers

/-!
# The ambient modular idempotent at the retained Broue--Michel label

The finite sum uses the constructed specified block index of the same full
ordinary rational family. No packet, block subset or new union source is
supplied. Its algebraic support is exactly that index fibre. The selected
nonprincipal reduction can enter through its existing association proof.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra BigOperators

namespace ModularRep.PaperProofs.TypeBRankThreeJordanAmbientPacket

open ModularRep OrdinaryIrreducibleCharacter FDRepSimpleClassKZero
open TypeBCliffordCarriers TypeBConformalDualCarriers
open TypeBOrdinaryBlockSplitting TypeBRankThreeNonprincipalSeriesBinding
open TypeBSpinBroueMichelCarriers

attribute [local instance] Classical.propDecidable

variable {p f : ℕ} {F K O k : Type}
  [Field F] [Finite F] [CharP F p]
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharZero K] [CharP k 2] [IsAlgClosed k]
  {N : NormSource 3 F} [Finite (Spin 3 F N)]
  (parameters : OddFieldParameters F p f)
  (Msys : ModularSystem 2 K O k)
  (iota : PrimeRegularRootEmbedding 2 k K (Spin 3 F N))
  [Fintype (LiteralPrimitiveBlock k (Spin 3 F N))]
  (blocks : BlockIdempotentDecomposition
    (fun c : LiteralPrimitiveBlock k (Spin 3 F N) => c.val))
  [HasEnoughRootsOfUnity K (Nat.card (Spin 3 F N))]
  (ordinary : OrdinaryBlockSource Msys iota
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) blocks)
  (series : Sources parameters Msys iota
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) blocks ordinary)

/-- The existing constructed index, retaining the same specified selector. -/
abbrev indexOf (c : LiteralPrimitiveBlock k (Spin 3 F N)) :=
  blockSeries parameters Msys iota
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
    blocks ordinary series c

/-- All actual primitive blocks with this same admissible rational label. -/
def blocksAt (s : AdmissibleParameter (p := p) (ell := 2) (n := 3) (F := F)) :
    Finset (LiteralPrimitiveBlock k (Spin 3 F N)) := by
  classical
  exact Finset.univ.filter fun c =>
    indexOf parameters Msys iota blocks ordinary series c = parameterIndex s

theorem mem_blocksAt
    (s : AdmissibleParameter (p := p) (ell := 2) (n := 3) (F := F))
    (c : LiteralPrimitiveBlock k (Spin 3 F N)) :
    c ∈ blocksAt parameters Msys iota blocks ordinary series s ↔
      indexOf parameters Msys iota blocks ordinary series c = parameterIndex s := by
  classical
  simp only [blocksAt, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The literal modular union idempotent is the sum of these primitive blocks. -/
def idempotent
    (s : AdmissibleParameter (p := p) (ell := 2) (n := 3) (F := F)) :
    k[Spin 3 F N] :=
  ∑ c ∈ blocksAt parameters Msys iota blocks ordinary series s, c.val

/-- Orthogonality computes every primitive product with the union. -/
theorem mul_idempotent
    (s : AdmissibleParameter (p := p) (ell := 2) (n := 3) (F := F))
    (c : LiteralPrimitiveBlock k (Spin 3 F N)) :
    c.val * idempotent parameters Msys iota blocks ordinary series s =
      if indexOf parameters Msys iota blocks ordinary series c = parameterIndex s
      then c.val else 0 := by
  classical
  by_cases hc : indexOf parameters Msys iota blocks ordinary series c = parameterIndex s
  · rw [if_pos hc]
    have mem := (mem_blocksAt parameters Msys iota blocks ordinary series s c).mpr hc
    exact blocks.complete.toCompleteOrthogonalIdempotents.toOrthogonalIdempotents.mul_sum_of_mem mem
  · rw [if_neg hc]
    apply blocks.complete.toCompleteOrthogonalIdempotents.toOrthogonalIdempotents.mul_sum_of_notMem
    intro mem
    apply hc
    exact (mem_blocksAt parameters Msys iota blocks ordinary series s c).mp mem

/-- Every primitive block is fixed precisely at the same constructed index. -/
theorem support_iff
    (s : AdmissibleParameter (p := p) (ell := 2) (n := 3) (F := F))
    (c : LiteralPrimitiveBlock k (Spin 3 F N)) :
    c.val * idempotent parameters Msys iota blocks ordinary series s = c.val ↔
      indexOf parameters Msys iota blocks ordinary series c = parameterIndex s := by
  classical
  rw [mul_idempotent]
  by_cases hc : indexOf parameters Msys iota blocks ordinary series c = parameterIndex s
  · simp [hc]
  · simp [hc, Ne.symm c.property.ne_zero]

/-- The actual finite block sum is central. -/
theorem idempotent_central
    (s : AdmissibleParameter (p := p) (ell := 2) (n := 3) (F := F)) :
    IsMulCentral (idempotent parameters Msys iota blocks ordinary series s) := by
  refine ⟨?_, fun x y => (mul_assoc _ x y).symm, fun x y => mul_assoc x y _⟩
  intro x
  change idempotent parameters Msys iota blocks ordinary series s * x =
    x * idempotent parameters Msys iota blocks ordinary series s
  simp only [idempotent, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  exact (c.property.central.comm x).eq

/-- Orthogonality also proves idempotence of that same sum. -/
theorem idempotent_idempotent
    (s : AdmissibleParameter (p := p) (ell := 2) (n := 3) (F := F)) :
    IsIdempotentElem (idempotent parameters Msys iota blocks ordinary series s) := by
  exact blocks.complete.toCompleteOrthogonalIdempotents.toOrthogonalIdempotents.isIdempotentElem_sum

/-- The ordinary family and the modular sum have exactly the same block support. -/
theorem ordinary_support_iff
    (s : AdmissibleParameter (p := p) (ell := 2) (n := 3) (F := F))
    (chi : Irr K (Spin 3 F N)) :
    (ordinary.physical.ordinaryBlock chi).val *
        idempotent parameters Msys iota blocks ordinary series s =
      (ordinary.physical.ordinaryBlock chi).val ↔
    indexedOrdinaryUnion series.family parameters.prime Nat.prime_two
      (two_ne_defining parameters) (parameterIndex s) chi := by
  rw [support_iff]
  exact (TypeBSpinBroueMichelSourceBinding.ordinaryUnion_iff_blockSeries
    series.family parameters.prime Nat.prime_two (two_ne_defining parameters)
    Msys iota (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
    blocks ordinary series.unions (parameterIndex s) chi).symm

/-- The retained association puts its original specified block in this same sum. -/
theorem associated_support
    (c : LiteralPrimitiveBlock k (Spin 3 F N))
    (s : AdmissibleParameter (p := p) (ell := 2) (n := 3) (F := F))
    (associated : Associated parameters Msys iota
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
      blocks ordinary series c s.val) :
    c.val * idempotent parameters Msys iota blocks ordinary series s = c.val := by
  obtain ⟨chi, hchi⟩ := ordinary.physical.ordinaryBlock_surjective c
  obtain ⟨regular, support⟩ := associated
  have hUnion := support chi hchi
  have hFix := (ordinary_support_iff parameters Msys iota blocks ordinary series s chi).mpr hUnion
  simpa only [hchi] using hFix

end ModularRep.PaperProofs.TypeBRankThreeJordanAmbientPacket


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
