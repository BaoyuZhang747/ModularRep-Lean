import ModularRep.IBrBlockEquivTransport
import ModularRep.IrreducibleBrauerCharacterEquiv
import ModularRep.PaperProofs.EvenFieldFLZSourceConditions

/-!
# Actual Brauer block fibres under a group equivalence

The ambient catalogue may store a different Fintype instance and a
different proof of the SAME complete primitive decomposition. Those are
identified in K before applying the existing IBr block transport theorem.
Only an actual primitive-idempotent equation is used. The actual Brauer
fibre equivalence is computed from equivAlongMulEquiv, not assumed.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.OddTwoGroupEquivBrauerBlocks

open ModularRep
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.CyclicOuterLemma37ActualBlockFibres

universe u

variable {p : ℕ} {k K G H Block : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Group H] [Fintype H] [Fintype Block]

/-- The finite indexing instance and decomposition proof add no freedom
once all actual primitive idempotents on the SAME labels agree. -/
theorem block_eq_of_ambient_idempotent
    (iota : PrimeRegularRootEmbedding p k K G)
    (injective : IrreducibleBrauerCharacterInjectivity iota)
    (A : AmbientBlockCatalogueData (k := k) (G := G) (Block := Block))
    {b : Block → k[G]} (blocks : BlockIdempotentDecomposition b)
    (idempotent_eq : ∀ x, A.blockIdempotent x = b x)
    (psi : IBr iota) :
    (letI := A.fintypeBlock
     irreducibleBrauerCharacterBlock iota injective A.blocks psi) =
      irreducibleBrauerCharacterBlock iota injective blocks psi := by
  rcases A with @⟨finiteA, bA, blocksA, catalogueA⟩
  have hf : finiteA = (inferInstance : Fintype Block) := Subsingleton.elim _ _
  cases hf
  have hb : bA = b := funext idempotent_eq
  cases hb
  rfl

/-- Transport to the EXACT supplied target catalogue, whose primitive
idempotents are the actual images of the source decomposition. -/
theorem block_alongMulEquiv
    (iota : PrimeRegularRootEmbedding p k K G)
    (injective : IrreducibleBrauerCharacterInjectivity iota)
    (e : G ≃* H)
    (injectiveH : IrreducibleBrauerCharacterInjectivity (iota.alongMulEquiv e))
    {b : Block → k[G]} (blocks : BlockIdempotentDecomposition b)
    (A : AmbientBlockCatalogueData (k := k) (G := H) (Block := Block))
    (idempotent_eq : ∀ x,
      A.blockIdempotent x = MonoidAlgebra.domCongr k k e (b x))
    (psi : IBr iota) :
    (letI := A.fintypeBlock
     irreducibleBrauerCharacterBlock (iota.alongMulEquiv e) injectiveH A.blocks
       (IrreducibleBrauerCharacter.equivAlongMulEquiv iota e psi)) =
      irreducibleBrauerCharacterBlock iota injective blocks psi := by
  rw [block_eq_of_ambient_idempotent (iota.alongMulEquiv e) injectiveH A
    (blocks.alongMulEquiv e) idempotent_eq]
  exact irreducibleBrauerCharacterBlock_alongMulEquiv iota injective e
    injectiveH blocks psi

/-- Restrict the COMPUTED actual Brauer equivalence to the SAME block
label. Both membership proofs follow from the primitive-block theorem. -/
def brauerFibreEquiv
    (iota : PrimeRegularRootEmbedding p k K G)
    (injective : IrreducibleBrauerCharacterInjectivity iota)
    (e : G ≃* H)
    (injectiveH : IrreducibleBrauerCharacterInjectivity (iota.alongMulEquiv e))
    {b : Block → k[G]} (blocks : BlockIdempotentDecomposition b)
    (A : AmbientBlockCatalogueData (k := k) (G := H) (Block := Block))
    (idempotent_eq : ∀ x,
      A.blockIdempotent x = MonoidAlgebra.domCongr k k e (b x))
    (block : Block) :
    BrauerFibre iota injective blocks block ≃
      (letI := A.fintypeBlock
       BrauerFibre (iota.alongMulEquiv e) injectiveH A.blocks block) where
  toFun psi := ⟨IrreducibleBrauerCharacter.equivAlongMulEquiv iota e psi.1,
    (block_alongMulEquiv iota injective e injectiveH blocks A idempotent_eq psi.1).trans
      psi.2⟩
  invFun psi := ⟨(IrreducibleBrauerCharacter.equivAlongMulEquiv iota e).symm psi.1, by
    rw [← block_alongMulEquiv iota injective e injectiveH blocks A idempotent_eq]
    simpa only [Equiv.apply_symm_apply] using psi.2⟩
  left_inv psi := by
    apply Subtype.ext
    exact (IrreducibleBrauerCharacter.equivAlongMulEquiv iota e).symm_apply_apply psi.1
  right_inv psi := by
    apply Subtype.ext
    exact (IrreducibleBrauerCharacter.equivAlongMulEquiv iota e).apply_symm_apply psi.1

@[simp] theorem brauerFibreEquiv_value
    (iota : PrimeRegularRootEmbedding p k K G)
    (injective : IrreducibleBrauerCharacterInjectivity iota)
    (e : G ≃* H)
    (injectiveH : IrreducibleBrauerCharacterInjectivity (iota.alongMulEquiv e))
    {b : Block → k[G]} (blocks : BlockIdempotentDecomposition b)
    (A : AmbientBlockCatalogueData (k := k) (G := H) (Block := Block))
    (idempotent_eq : ∀ x,
      A.blockIdempotent x = MonoidAlgebra.domCongr k k e (b x))
    (block : Block) (psi : BrauerFibre iota injective blocks block)
    (x : PrimeRegularElement (G := H) p) :
    (brauerFibreEquiv iota injective e injectiveH blocks A idempotent_eq block psi).1.1 x =
      psi.1.1 (PrimeRegularElement.map e.symm.toMonoidHom x) := rfl

end ModularRep.PaperProofs.OddTwoGroupEquivBrauerBlocks


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
