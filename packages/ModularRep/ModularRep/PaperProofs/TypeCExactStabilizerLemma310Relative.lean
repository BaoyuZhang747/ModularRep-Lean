import ModularRep.PaperProofs.OddConformalProposition311Relative
import ModularRep.CyclicOuterBAW

/-!
# The exact stabiliser in the odd-field type C argument

This file formalises the group-theoretic passage from manuscript Lemma 3.10
to Proposition 3.11.  If `J` is the stabiliser of a block inside the
tensor-and-field semidirect product `N ⋊ E`, then the subgroup denoted by
`D = J ∩ N` in the manuscript is the kernel of the field projection
restricted to `J`.  Lean constructs the resulting embedding `J / D → E`
and derives the `2`-hypoelementary hypothesis needed for Conlon's theorem.

The only result-specific premise in this deduction is the cardinality bound
`|D| ≤ 2` obtained from Li's block labels.  No normality, quotient
embedding, quotient cyclicity, `2`-hypoelementarity, or equivariant bijection
is assumed.
-/

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeCExactStabilizerLemma310Relative

open ExactGrothendieckGroup
open FDRepSimpleClassKZero
open DecompositionBasicSetBridge
open BlockFibreRestriction
open IntegralBasicSetBridge
open ManuscriptVerification.ConlonStabilizerBridge
open OddConformalProposition311Relative

noncomputable section

universe u

variable {N E : Type u} [Group N] [Group E]

/-- The field projection restricted to a subgroup of the tensor-and-field
semidirect product. -/
def fieldProjection (phi : E →* MulAut N)
    (J : Subgroup (N ⋊[phi] E)) : J →* E :=
  SemidirectProduct.rightHom.comp J.subtype

/-- The kernel of the restricted field projection is exactly the intersection
of `J` with the embedded tensor factor. -/
theorem fieldProjection_ker_eq_comap_leftFactor
    (phi : E →* MulAut N)
    (J : Subgroup (N ⋊[phi] E)) :
    (fieldProjection phi J).ker =
      ((SemidirectProduct.inl : N →* N ⋊[phi] E).range).comap J.subtype := by
  rw [SemidirectProduct.range_inl_eq_ker_rightHom]
  ext x
  change
    fieldProjection phi J x = 1 ↔
      (SemidirectProduct.rightHom : N ⋊[phi] E →* E) x.1 = 1
  rfl

/-- Elementwise form of the identification `D = J ∩ N`. -/
theorem mem_fieldProjection_ker_iff
    (phi : E →* MulAut N)
    (J : Subgroup (N ⋊[phi] E)) (x : J) :
    x ∈ (fieldProjection phi J).ker ↔ x.1.2 = 1 := by
  simp [fieldProjection]

/-- The first-isomorphism-theorem embedding of the exact stabiliser quotient
in the cyclic field group. -/
def quotientEmbedding (phi : E →* MulAut N)
    (J : Subgroup (N ⋊[phi] E)) :
    J ⧸ (fieldProjection phi J).ker →* E :=
  (fieldProjection phi J).range.subtype.comp
    (QuotientGroup.quotientKerEquivRange
      (fieldProjection phi J)).toMonoidHom

theorem quotientEmbedding_injective
    (phi : E →* MulAut N)
    (J : Subgroup (N ⋊[phi] E)) :
    Function.Injective (quotientEmbedding phi J) :=
  (fieldProjection phi J).range.subtype_injective.comp
    (QuotientGroup.quotientKerEquivRange
      (fieldProjection phi J)).injective

/-- The exact quotient `J / D` is cyclic because it embeds in the cyclic
field factor. -/
theorem exactStabilizer_quotient_isCyclic
    [IsCyclic E]
    (phi : E →* MulAut N)
    (J : Subgroup (N ⋊[phi] E)) :
    IsCyclic (J ⧸ (fieldProjection phi J).ker) :=
  isCyclic_of_injective (quotientEmbedding phi J)
    (quotientEmbedding_injective phi J)

/-- The complete group-theoretic conclusion of Lemma 3.10, obtained from the
literal semidirect-product stabiliser and the label-theoretic order bound. -/
theorem exactStabilizer_isTwoHypoelementary
    [Finite N] [Finite E] [IsCyclic E]
    (phi : E →* MulAut N)
    (J : Subgroup (N ⋊[phi] E))
    (hcard : Nat.card (fieldProjection phi J).ker ≤ 2) :
    IsPHypoelementary 2 J :=
  isTwoHypoelementary_of_small_normal_quotient_embedding
    (fieldProjection phi J).ker hcard
    (quotientEmbedding phi J)
    (quotientEmbedding_injective phi J)

/-- Every subgroup of the exact block stabiliser is also
`2`-hypoelementary, as asserted in Lemma 3.10. -/
theorem exactStabilizer_subgroup_isTwoHypoelementary
    [Finite N] [Finite E] [IsCyclic E]
    (phi : E →* MulAut N)
    (J : Subgroup (N ⋊[phi] E))
    (hcard : Nat.card (fieldProjection phi J).ker ≤ 2)
    (K : Subgroup J) :
    IsPHypoelementary 2 K :=
  isPHypoelementary_subgroup 2
    (exactStabilizer_isTwoHypoelementary phi J hcard) K

variable {p : ℕ} {K k G Basic BlockIndex : Type u}
variable [Field K] [Field k] [CharZero K]
variable [Group G] [Finite G] [CharP k p] [IsAlgClosed k]
variable [Finite Basic]

/-- Proposition 3.11 with the exact stabiliser deduction internalised.

Compared with `proposition_3_11_relative`, this theorem does not accept a
normal subgroup, an embedding of its quotient in a cyclic group, or the
injectivity of that embedding.  These data are constructed from the literal
field projection on `J`; the application supplies only Li's bound on its
kernel. -/
theorem proposition_3_11_of_exactStabilizer
    [Finite N] [Finite E] [IsCyclic E]
    (phi : E →* MulAut N)
    (J : Subgroup (N ⋊[phi] E))
    (iota : PrimeRegularRootEmbedding p k K G)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    [MulAction J Basic] [MulAction J (IBr iota)]
    [Fintype BlockIndex]
    {blockIdempotent : BlockIndex → k[G]}
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (block : BlockIndex)
    {decomposition : FDRepKZero K G →+ FDRepKZero k G}
    (basicSet : RestrictedIntegralBasicSetOnIBr
      iota hinj Basic decomposition)
    (ordinaryBlock : Basic → BlockIndex)
    (hblockDiagonal : BlockDiagonalLinearEquiv ordinaryBlock
      (irreducibleBrauerCharacterBlock iota hinj blocks)
      basicSet.linearEquiv)
    (tensorFieldActions : LabelledKZeroActionData (A := J)
      basicSet.toRestrictedIntegralBasicSet)
    (reductionNatural : DecompositionNatural (A := J) decomposition
      tensorFieldActions.ordinaryAction tensorFieldActions.modularAction)
    (hOrdinaryBlockStable : ∀ (j : J) (x : Basic),
      ordinaryBlock x = block → ordinaryBlock (j • x) = block)
    (hBrauerBlockStable : ∀ (j : J) (varphi : IBr iota),
      irreducibleBrauerCharacterBlock iota hinj blocks varphi = block →
        irreducibleBrauerCharacterBlock iota hinj blocks (j • varphi) =
          block)
    (hcard : Nat.card (fieldProjection phi J).ker ≤ 2)
    (conlon : PaperProofs.ConlonBasicSet.PadicConlonMarkDetection.{u, u}
      (p := 2) (A := J))
    (burnside :
      PaperProofs.ConlonBasicSet.PublishedBurnsideMarkInjectivity.{u, u}
        (A := J)) :
    let _ : MulAction J (BlockFibre ordinaryBlock block) :=
      stableBlockFibreMulAction ordinaryBlock block hOrdinaryBlockStable
    let _ : MulAction J
        (BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks)
          block) :=
      stableBlockFibreMulAction
        (irreducibleBrauerCharacterBlock iota hinj blocks) block
        hBrauerBlockStable
    ∃ e : BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks)
        block ≃ BlockFibre ordinaryBlock block,
      ∀ (j : J)
        (varphi : BlockFibre
          (irreducibleBrauerCharacterBlock iota hinj blocks) block),
        e (j • varphi) = j • e varphi := by
  exact proposition_3_11_relative
    iota hinj blocks block basicSet ordinaryBlock hblockDiagonal
    tensorFieldActions reductionNatural hOrdinaryBlockStable
    hBrauerBlockStable (fieldProjection phi J).ker hcard
    (quotientEmbedding phi J)
    (quotientEmbedding_injective phi J) conlon burnside

end

end ModularRep.PaperProofs.TypeCExactStabilizerLemma310Relative


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
