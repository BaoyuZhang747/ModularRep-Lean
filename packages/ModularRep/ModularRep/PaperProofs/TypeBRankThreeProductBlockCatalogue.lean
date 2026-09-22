import ModularRep.PaperProofs.TypeBRankThreeProductBlockSource
import ModularRep.BlockCentralCharacters

/-!
# The original block catalogue in product-tuple coordinates

A finite label equivalence pulls back the supplied complete decomposition
and its SAME central characters. The product specialization computes that
equivalence from literal primitive factorization and the original
decomposition's primitiveBlockEquiv. Its idempotents are the prescribed
coefficient products, proved equal to the original labelled idempotents.

No new source field, local selector, character-weight assignment or block
induction conclusion is introduced. Literal-primitive reindexing and group
equivalence transport remain the existing separate APIs.
-/

noncomputable section
set_option autoImplicit false

open scoped BigOperators MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBRankThreeProductBlockCatalogue

open ModularRep
open TypeBRankThreeProductBlockSource

universe u

section Reindex

variable {k G B J : Type u} [Field k] [Group G]
variable [Fintype B] [Fintype J]
variable {blockIdempotent : B → k[G]}
variable (D : BlockIdempotentDecomposition blockIdempotent) (e : J ≃ B)

include D in
/-- Pull back the same finite primitive decomposition along a label equivalence. -/
theorem reindexBlocks :
    BlockIdempotentDecomposition (fun j => blockIdempotent (e j)) where
  complete := {
    idem := fun j => (D.primitive (e j)).idempotent
    ortho := by
      intro j l hjl
      exact D.complete.ortho (fun h => hjl (e.injective h))
    complete := by
      classical
      exact (e.sum_comp blockIdempotent).trans D.complete.complete
    central := fun j => (D.primitive (e j)).central }
  primitive := fun j => D.primitive (e j)

/-- The reindexed central idempotent is literally the old one. -/
@[simp] theorem reindexBlocks_blockIdempotentInCenter (j : J) :
    (reindexBlocks D e).blockIdempotentInCenter j =
      D.blockIdempotentInCenter (e j) := rfl

variable [IsAlgClosed k] [Fintype G]
variable (C : BlockCentralCharacterCatalogue D)

/-- Pull back the existing central characters; delta and exhaustivity are preserved. -/
def reindexCatalogue : BlockCentralCharacterCatalogue (reindexBlocks D e) where
  centralCharacter j := C.centralCharacter (e j)
  delta_own j := by
    change C.centralCharacter (e j) (D.blockIdempotentInCenter (e j)) = 1
    exact C.delta_own (e j)
  delta_other j l hjl := by
    change C.centralCharacter (e j) (D.blockIdempotentInCenter (e l)) = 0
    exact C.delta_other (e j) (e l) (fun h => hjl (e.injective h))
  exhaustive := by
    intro lambda
    obtain ⟨b, hb⟩ := C.exhaustive lambda
    refine ⟨e.symm b, ?_⟩
    change C.centralCharacter (e (e.symm b)) = lambda
    rw [e.apply_symm_apply]
    exact hb

/-- Reindexing chooses no new central character family. -/
@[simp] theorem reindexCatalogue_centralCharacter (j : J) :
    (reindexCatalogue D e C).centralCharacter j =
      C.centralCharacter (e j) := rfl

end Reindex

section Product

variable {I k B : Type u} [Fintype I] [Field k] [IsAlgClosed k]

local instance indexDecidableEq : DecidableEq I := Classical.decEq I

variable (H : I → Type u) [∀ i, Group (H i)] [∀ i, Fintype (H i)]
variable [Fintype B] [∀ i, Fintype (LiteralPrimitiveBlock k (H i))]
variable (source : PrimitiveProductSource (k := k) H)
variable {blockIdempotent : B → k[∀ i, H i]}
variable (D : BlockIdempotentDecomposition blockIdempotent)

/-- Product tuples are related to the original labels by actual primitive blocks. -/
def productTupleLabelEquiv : (∀ i, LiteralPrimitiveBlock k (H i)) ≃ B :=
  (productBlockEquiv H source).trans D.primitiveBlockEquiv.symm

/-- The original catalogue idempotent has the prescribed product coefficients. -/
@[simp] theorem productTupleLabelEquiv_idempotent
    (b : ∀ i, LiteralPrimitiveBlock k (H i)) :
    blockIdempotent (productTupleLabelEquiv H source D b) =
      productIdempotent H b := by
  change blockIdempotent
      (D.primitiveBlockEquiv.symm (productBlock H source b)) =
    productIdempotent H b
  exact congrArg Subtype.val
    (D.primitiveBlockEquiv.apply_symm_apply (productBlock H source b))

include source D in
/-- This is the original complete family with its product-tuple labels. -/
theorem productTupleBlocks :
    BlockIdempotentDecomposition
      (fun b : ∀ i, LiteralPrimitiveBlock k (H i) => productIdempotent H b) := by
  simpa only [productTupleLabelEquiv_idempotent] using
    reindexBlocks D (productTupleLabelEquiv H source D)

private theorem productTupleBlockInCenter
    (b : ∀ i, LiteralPrimitiveBlock k (H i)) :
    (reindexBlocks D (productTupleLabelEquiv H source D)).blockIdempotentInCenter b =
      (productTupleBlocks H source D).blockIdempotentInCenter b := by
  apply Subtype.ext
  exact productTupleLabelEquiv_idempotent H source D b

variable (C : BlockCentralCharacterCatalogue D)

/-- The tuple catalogue retains the actual original catalogue's central characters. -/
def productTupleCatalogue :
    BlockCentralCharacterCatalogue (productTupleBlocks H source D) where
  centralCharacter b :=
    (reindexCatalogue D (productTupleLabelEquiv H source D) C).centralCharacter b
  delta_own b := by
    rw [← productTupleBlockInCenter H source D b]
    exact (reindexCatalogue D (productTupleLabelEquiv H source D) C).delta_own b
  delta_other b c hbc := by
    rw [← productTupleBlockInCenter H source D c]
    exact (reindexCatalogue D (productTupleLabelEquiv H source D) C).delta_other b c hbc
  exhaustive :=
    (reindexCatalogue D (productTupleLabelEquiv H source D) C).exhaustive

/-- The same original block central character is exposed at every product tuple. -/
@[simp] theorem productTupleCatalogue_centralCharacter
    (b : ∀ i, LiteralPrimitiveBlock k (H i)) :
    (productTupleCatalogue H source D C).centralCharacter b =
      C.centralCharacter (productTupleLabelEquiv H source D b) := rfl

end Product

end ModularRep.PaperProofs.TypeBRankThreeProductBlockCatalogue


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
