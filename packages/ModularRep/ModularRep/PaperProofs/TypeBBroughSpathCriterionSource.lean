import ModularRep.PaperProofs.TypeBCriterionHypotheses
import ModularRep.PaperProofs.TypeBFullBlockCondition

/-!
# The exact universal one-way Brough--Spath source boundary

This module fixes a published theorem's input and output independently of
Spin or special Clifford groups. No arbitrary result proposition, family,
matching, character-triple relation or Type B conclusion is a parameter of
the certificate. Its input is the literal all-blocks specialization in
`TypeBCriterionHypotheses`. Its output is the independently defined complete
`TypeBFullBlockCondition.FamilyWitness` on the family COMPUTED from those
same input blocks, roots and local reductions, and the same cover.

Primary source chain:

* Brough--Spath, Bull. Lond. Math. Soc. 54 (2022), 466--481,
  Theorem 4.5, pp. 476--477 (local TeX `NewIndBAWCond`), for all blocks.
  The allowed acting group is specialized to the abelian alternative, and
  abelianness of the full outer automorphism group implies the required
  orbit-stabilizer alternative. The four extension hypotheses are retained.
* Hypothesis 2.13 and Lemmas 2.14--2.15, pp. 471--472, define both `J_G`
  values as the actual downstairs inertia times the same Hall preimage.
  The stronger all-pairs equality in the domain therefore implies the
  source clause for its authentic constituents and covered weights. No
  caller-supplied DGN correspondence is used in this certificate.
* Definition 4.3, p. 475, and Remark 4.4, pp. 475--476, specify the literal
  central character quotient, ambient group, character extensions and
  every intermediate block induction equality used in the output.
* Koshitani--Spath, J. Group Theory 19 (2016), 777--813, Lemma 3.3,
  p. 783, passes from block witnesses on an automorphism transversal to
  Spath's global condition. Spath, J. Group Theory 16 (2013),
  159--220, Definition 4.1, p. 182, specifies the radical fibres, central
  scalar-character compatibility and trivial-radical normalization. The
  last normalization includes equality of the two extension characters.

The theorem is used only in this direction. The target's quotient Brauer
and weight completeness, fixed root convention, conjugate representative
transport and central character quotients are source-to-Lean identification
obligations, not consequences of an arbitrary relative witness. Their
standard mathematics is E1; the published criterion and block/global
passage are E2. The literal identification of this complete Lean output
with these source formulations remains U until that audit is discharged.
This file supplies NO inhabitant of the certificate and proves NO
unconditional instance of the published criterion or of the Type B target.

The `SpathCoefficientField` hypothesis and common-root guards in the input
are essential. An arbitrary algebraically closed modular field need not be
algebraic over its prime field, and a fixed ordinary-to-modular block
selector cannot be used with unrelated root embeddings.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBBroughSpathCriterionSource

open ModularRep FDRepSimpleClassKZero
open CyclicOuterLemma37Concrete
open TypeCWeightTensorFieldAction
open TypeBCriterionHypotheses

/-- The general published one-way implication, with its entire domain and
its single fixed literal output. It is an external E2/U certificate, not a
Type B-specific assumed conclusion. It accepts no caller-selected target. -/
structure Theorem45Certificate : Prop where
  allBlocks : ∀ {ell : ℕ} {k K M E : Type}
      [Field k] [Field K] [CharP k ell] [IsAlgClosed k] [CharZero K]
      [IsAlgClosed K] [Group M] [Finite M] [Group E] [Finite E]
      (G : Subgroup M) [G.Normal] (field : E →* MulAut M)
      (action : NaturalAction G field)
      (iotaM : PrimeRegularRootEmbedding ell k K M)
      (iotaG : PrimeRegularRootEmbedding ell k K G)
      [Fintype (LiteralPrimitiveBlock k M)]
      [Fintype (LiteralPrimitiveBlock k G)]
      (blocks : BlockData (ell := ell) (k := k) (K := K) G)
      (hinjM : IrreducibleBrauerCharacterInjectivity iotaM)
      (hinvariant :
        TypeCConformalActionAdapter.FieldInvariantSubgroup.IsInvariant G field)
      (D : TypeCConformalActionAdapter.OrdinaryReductionEquiv
        (k := k) (K := K) G field hinvariant)
      (productFormula : BrauerLinearTensorProductFormula iotaM)
      (radicalKernel : RadicalKernelLiftInput (p := ell) G field hinvariant D)
      (hypotheses : AllBlocksHypotheses G field action iotaM iotaG
        blocks hinjM hinvariant D productFormula radicalKernel),
    Nonempty (TypeBFullBlockCondition.FamilyWitness
      (downstairsFamily G iotaG blocks hypotheses.prime
        hypotheses.brauer_injective_downstairs hypotheses.localReduction)
      hypotheses.cover)

section Apply

variable {ell : ℕ} {k K M E : Type}
variable [Field k] [Field K] [CharP k ell] [IsAlgClosed k] [CharZero K]
variable [IsAlgClosed K] [Group M] [Finite M] [Group E] [Finite E]
variable (G : Subgroup M) [G.Normal] (field : E →* MulAut M)
variable (action : NaturalAction G field)
variable (iotaM : PrimeRegularRootEmbedding ell k K M)
variable (iotaG : PrimeRegularRootEmbedding ell k K G)
variable [Fintype (LiteralPrimitiveBlock k M)]
variable [Fintype (LiteralPrimitiveBlock k G)]
variable (blocks : BlockData (ell := ell) (k := k) (K := K) G)
variable (hinjM : IrreducibleBrauerCharacterInjectivity iotaM)
variable (hinvariant :
  TypeCConformalActionAdapter.FieldInvariantSubgroup.IsInvariant G field)
variable (D : TypeCConformalActionAdapter.OrdinaryReductionEquiv
  (k := k) (K := K) G field hinvariant)
variable (productFormula : BrauerLinearTensorProductFormula iotaM)
variable (radicalKernel : RadicalKernelLiftInput (p := ell) G field hinvariant D)
variable (hypotheses : AllBlocksHypotheses G field action iotaM iotaG
  blocks hinjM hinvariant D productFormula radicalKernel)

/-- Apply the fixed general certificate to its literal hypotheses. This
does not authenticate or construct that external certificate. -/
def witness (source : Theorem45Certificate) :
    TypeBFullBlockCondition.FamilyWitness
      (downstairsFamily G iotaG blocks hypotheses.prime
        hypotheses.brauer_injective_downstairs hypotheses.localReduction)
      hypotheses.cover :=
  Classical.choice (source.allBlocks G field action iotaM iotaG blocks
    hinjM hinvariant D productFormula radicalKernel hypotheses)

end Apply

end ModularRep.PaperProofs.TypeBBroughSpathCriterionSource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
