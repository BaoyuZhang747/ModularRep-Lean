import ModularRep.PaperProofs.SporadicFi24LiteralCarrierBase
import ModularRep.PaperProofs.CyclicOuterLemma37ActualBlockFibres

/-!
# Reindexing Fischer block data by literal blocks

A complete block decomposition may initially use an arbitrary finite index
type. Its canonical equivalence with the literal primitive central
idempotents reindexes the decomposition without changing the selected block
of any simple module or irreducible Brauer character.
-/

noncomputable section

open scoped BigOperators MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24LiteralBlockReindex

open ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37ActualBlockFibres

universe u

variable {k X BlockIndex : Type u}
variable [Field k] [Group X] [Fintype X] [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}

/-- The literal set of blocks is finite because every literal primitive
central idempotent occurs in the supplied complete decomposition. -/
@[instance_reducible]
noncomputable def literalBlockFintype
    (blocks : BlockIdempotentDecomposition blockIdempotent) :
    Fintype (ActualBlock (k := k) (X := X)) :=
  Fintype.ofEquiv BlockIndex blocks.primitiveBlockEquiv

omit [Fintype X] in
/-- Reindex a complete block decomposition by its literal primitive central
idempotents. -/
theorem literalBlocks
    [Fintype (ActualBlock (k := k) (X := X))]
    (blocks : BlockIdempotentDecomposition blockIdempotent) :
    BlockIdempotentDecomposition
      (fun b : ActualBlock (k := k) (X := X) ↦ b.1) where
  complete := {
    idem := fun b ↦ b.2.idempotent
    ortho := by
      intro b c hbc
      let e := blocks.primitiveBlockEquiv
      have hindex : e.symm b ≠ e.symm c := by
        intro h
        exact hbc (e.symm.injective h)
      have hb : blockIdempotent (e.symm b) = b.1 := by
        simpa only [e,
          BlockIdempotentDecomposition.primitiveBlockEquiv_apply,
          BlockIdempotentDecomposition.primitiveBlockOfIndex_val] using
          congrArg Subtype.val (e.apply_symm_apply b)
      have hc : blockIdempotent (e.symm c) = c.1 := by
        simpa only [e,
          BlockIdempotentDecomposition.primitiveBlockEquiv_apply,
          BlockIdempotentDecomposition.primitiveBlockOfIndex_val] using
          congrArg Subtype.val (e.apply_symm_apply c)
      simpa only [hb, hc] using blocks.complete.ortho hindex
    complete := by
      classical
      calc
        (∑ b : ActualBlock (k := k) (X := X), b.1) =
            ∑ i : BlockIndex, blockIdempotent i := by
          simpa only [
            BlockIdempotentDecomposition.primitiveBlockEquiv_apply,
            BlockIdempotentDecomposition.primitiveBlockOfIndex_val] using
            (blocks.primitiveBlockEquiv.sum_comp
              (fun b : ActualBlock (k := k) (X := X) ↦ b.1)).symm
        _ = 1 := blocks.complete.complete
    central := fun b ↦ b.2.central }
  primitive := fun b ↦ b.2

omit [Fintype X] in
/-- The literal block indexed by itself is unchanged. -/
@[simp]
theorem primitiveBlockOfIndex_literalBlocks
    [Fintype (ActualBlock (k := k) (X := X))]
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (b : ActualBlock (k := k) (X := X)) :
    (literalBlocks blocks).primitiveBlockOfIndex b = b := by
  apply Subtype.ext
  rfl

omit [Fintype X] in
/-- Reindexing by literal blocks transports the supporting block of every
simple module through the canonical block equivalence. -/
theorem moduleBlock_literalBlocks
    [Fintype (ActualBlock (k := k) (X := X))]
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    {V : Type*} [AddCommGroup V] [Module k[X] V]
    [IsSimpleModule k[X] V] :
    (literalBlocks blocks).moduleBlock (V := V) =
      blocks.primitiveBlockOfIndex (blocks.moduleBlock (V := V)) := by
  symm
  apply (literalBlocks blocks).moduleBlock_eq_of_smul_eq_self
  intro v
  exact blocks.moduleBlock_smul v

variable {p : ℕ} {K : Type u}
variable [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable (iota : PrimeRegularRootEmbedding p k K X)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)

/-- The literal decomposition assigns a Brauer character to the same
primitive idempotent as the original indexed decomposition. -/
theorem irreducibleBrauerCharacterBlock_literalBlocks
    [Fintype (ActualBlock (k := k) (X := X))]
    (psi : IBr iota) :
    irreducibleBrauerCharacterBlock iota hinj (literalBlocks blocks) psi =
      brauerBlock iota hinj blocks psi := by
  let Y : SimpleModuleClass k[X] :=
    (simpleModuleClassEquivIBr iota hinj).symm psi
  letI : IsSimpleModule k[X]
      (Representation.asModule (simpleClassFDRep Y).ρ) :=
    simple_iff_isSimpleModule.mp (simpleClassFDRep_underlying_simple Y)
  change
    (literalBlocks blocks).moduleBlock
        (V := Representation.asModule (simpleClassFDRep Y).ρ) =
      actualBlockOfIndex blocks
        (blocks.moduleBlock
          (V := Representation.asModule (simpleClassFDRep Y).ρ))
  exact moduleBlock_literalBlocks blocks

variable {R : LiteralCarrierAdapter
  (p := p) (k := k) (K := K) (X := X)}

/-- Restrict a block-preserving global character-weight equivalence to each
literal block fibre. -/
noncomputable def restrictOmegaToLiteralBlock
    [Fintype (ActualBlock (k := k) (X := X))]
    (Omega : IBr iota ≃ WeightClass (p := p) (K := K) (X := X))
    (hblock : ∀ psi,
      R.1.weightBlock (Omega psi) = brauerBlock iota hinj blocks psi)
    (b : ActualBlock (k := k) (X := X)) :
    BrauerFibre iota hinj (literalBlocks blocks) b ≃
      WeightFibre R.1 b where
  toFun psi := ⟨Omega psi.1, by
    calc
      R.1.weightBlock (Omega psi.1) =
          brauerBlock iota hinj blocks psi.1 := hblock psi.1
      _ = irreducibleBrauerCharacterBlock iota hinj
          (literalBlocks blocks) psi.1 :=
        (irreducibleBrauerCharacterBlock_literalBlocks
          iota hinj blocks psi.1).symm
      _ = b := psi.2⟩
  invFun w := ⟨Omega.symm w.1, by
    calc
      irreducibleBrauerCharacterBlock iota hinj
          (literalBlocks blocks) (Omega.symm w.1) =
        brauerBlock iota hinj blocks (Omega.symm w.1) :=
          irreducibleBrauerCharacterBlock_literalBlocks
            iota hinj blocks (Omega.symm w.1)
      _ = R.1.weightBlock (Omega (Omega.symm w.1)) :=
        (hblock (Omega.symm w.1)).symm
      _ = R.1.weightBlock w.1 := by rw [Omega.apply_symm_apply]
      _ = b := w.2⟩
  left_inv psi := by
    apply Subtype.ext
    exact Omega.symm_apply_apply psi.1
  right_inv w := by
    apply Subtype.ext
    exact Omega.apply_symm_apply w.1

variable {E : Type u}
variable [Group E] [Finite E] [IsCyclic E]

/-- The canonical literal reindexing preserves transport of Brauer blocks
under automorphisms. -/
theorem literalBlocks_brauerBlock_transport
    [Fintype (ActualBlock (k := k) (X := X))]
    (alpha : (MulAut X)ᵐᵒᵖ) (psi : IBr iota) :
    irreducibleBrauerCharacterBlock iota hinj (literalBlocks blocks)
        (alpha • psi) =
      alpha • irreducibleBrauerCharacterBlock iota hinj
        (literalBlocks blocks) psi := by
  calc
    irreducibleBrauerCharacterBlock iota hinj (literalBlocks blocks)
        (alpha • psi) =
      brauerBlock iota hinj blocks (alpha • psi) :=
        irreducibleBrauerCharacterBlock_literalBlocks
          iota hinj blocks (alpha • psi)
    _ = alpha • brauerBlock iota hinj blocks psi :=
      brauerBlock_transport iota hinj blocks alpha psi
    _ = alpha • irreducibleBrauerCharacterBlock iota hinj
        (literalBlocks blocks) psi := by
      rw [irreducibleBrauerCharacterBlock_literalBlocks iota hinj blocks psi]

/-- The global action on Brauer characters induces a transport source on a
literal block fixed by the chosen outer action. -/
theorem literalFibreTransportSource
    [Fintype (ActualBlock (k := k) (X := X))]
    (outer : E →* MulAut X)
    (b : ActualBlock (k := k) (X := X))
    (hfixed : ∀ e : E, inverseOpHom outer e • b = b) :
    FibreTransportSource iota hinj (literalBlocks blocks) outer b where
  brauerBlock_transport := fun alpha psi ↦
    literalBlocks_brauerBlock_transport iota hinj blocks alpha psi
  outerBlock_fixed := hfixed

omit [Finite E] [IsCyclic E] in
/-- Restriction to a literal block fibre preserves equivariance under the
chosen cyclic outer action. -/
theorem restrictOmegaToLiteralBlock_outer_equivariant
    [Fintype (ActualBlock (k := k) (X := X))]
    (Omega : IBr iota ≃ WeightClass (p := p) (K := K) (X := X))
    (hOmega : ∀ alpha : (MulAut X)ᵐᵒᵖ, ∀ psi : IBr iota,
      Omega (alpha • psi) = alpha • Omega psi)
    (hblock : ∀ psi,
      R.1.weightBlock (Omega psi) = brauerBlock iota hinj blocks psi)
    (outer : E →* MulAut X)
    (b : ActualBlock (k := k) (X := X))
    (T : FibreTransportSource iota hinj (literalBlocks blocks) outer b) :
    let _ : MulAction E
        (BrauerFibre iota hinj (literalBlocks blocks) b) :=
      rightIBrBlockMulAction iota hinj (literalBlocks blocks)
        outer b T.outerBlock_fixed T.brauerBlock_transport
    let _ : MulAction E (WeightFibre R.1 b) :=
      rightWeightFibreMulAction outer R.1 b T.outerBlock_fixed
    ∀ (e : E)
      (psi : BrauerFibre iota hinj (literalBlocks blocks) b),
      restrictOmegaToLiteralBlock iota hinj blocks Omega hblock b (e • psi) =
        e • restrictOmegaToLiteralBlock iota hinj blocks Omega hblock b psi := by
  dsimp only
  letI : MulAction E
      (BrauerFibre iota hinj (literalBlocks blocks) b) :=
    rightIBrBlockMulAction iota hinj (literalBlocks blocks)
      outer b T.outerBlock_fixed T.brauerBlock_transport
  letI : MulAction E (WeightFibre R.1 b) :=
    rightWeightFibreMulAction outer R.1 b T.outerBlock_fixed
  intro e psi
  apply Subtype.ext
  change Omega (e • psi).1 =
    (e • restrictOmegaToLiteralBlock iota hinj blocks Omega hblock b psi).1
  rw [rightIBrBlock_smul_val, rightWeightFibre_smul_val]
  exact hOmega _ _

end ModularRep.PaperProofs.SporadicFi24LiteralBlockReindex


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
