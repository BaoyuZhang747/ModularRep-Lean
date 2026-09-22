import ModularRep.PrimitiveBlockAutomorphism
import ModularRep.IBrBlock
import ModularRep.PaperProofs.TypeBFiniteProductNaturality
import Mathlib.Data.Finsupp.Defs

/-!
# Literal primitive blocks of a finite product

The product element is defined coefficientwise in the actual group algebra.
The finite product occurs in the commutative residue field, not in the ambient
possibly noncommutative group algebra.

The root-free source records the standard primitive-block factorization for
this element.  A separate source identifies the supporting block of the SAME
Brauer external-product dictionary and the supplied complete literal block
catalogues.  No character-weight assignment is a field of either source.

The routine algebraic source boundary is the finite-product centre argument
from Navarro, Characters and Blocks of Finite Groups (1998), (3.11),
pp. 55--57, and (3.12), pp. 57--58.  The Brauer external-product values are
Navarro (8.21), p. 177, with the definition on p. 176.  These are separate
locators: (8.21) alone does not assert primitive-block factorization.  The
source preparation note spells out the elementary centre argument and the
remaining specified dictionary authentication.
-/

noncomputable section

open scoped BigOperators MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBRankThreeProductBlockSource

open FDRepSimpleClassKZero

universe u v

variable {I k : Type u} (H : I → Type u) [Fintype I]
variable [∀ i, Group (H i)] [∀ i, Finite (H i)] [Field k]

/-- The literal product element, specified on every group basis coefficient. -/
def productIdempotent (blocks : ∀ i, LiteralPrimitiveBlock k (H i)) :
    k[∀ i, H i] :=
  MonoidAlgebra.ofCoeff
    (Finsupp.equivFunOnFinite.symm (fun g ↦ ∏ i, (blocks i).val.coeff (g i)))

@[simp]
theorem productIdempotent_apply
    (blocks : ∀ i, LiteralPrimitiveBlock k (H i)) (g : ∀ i, H i) :
    (productIdempotent H blocks).coeff g = ∏ i, (blocks i).val.coeff (g i) :=
  rfl

/-- Routine E1 primitive-block facts about the fixed coefficient formula.
The algebraic closure hypothesis is explicit even in this root-free scope. -/
structure PrimitiveProductSource [IsAlgClosed k] : Prop where
  primitive : ∀ blocks : ∀ i, LiteralPrimitiveBlock k (H i),
    IsPrimitiveCentralIdempotent (productIdempotent H blocks)
  factorization : ∀ b : LiteralPrimitiveBlock k (∀ i, H i),
    ∃! blocks : ∀ i, LiteralPrimitiveBlock k (H i),
      productIdempotent H blocks = b.val

variable [IsAlgClosed k]
variable (source : PrimitiveProductSource (k := k) H)

/-- The block map is constructed from the fixed element and its primitivity. -/
def productBlock (blocks : ∀ i, LiteralPrimitiveBlock k (H i)) :
    LiteralPrimitiveBlock k (∀ i, H i) :=
  ⟨productIdempotent H blocks, source.primitive blocks⟩

@[simp]
theorem productBlock_val (blocks : ∀ i, LiteralPrimitiveBlock k (H i)) :
    (productBlock H source blocks).val = productIdempotent H blocks :=
  rfl

/-- Unique specified factorization makes the constructed map injective. -/
theorem productBlock_injective : Function.Injective (productBlock H source) := by
  intro blocks other h
  obtain ⟨factors, hfactor, hunique⟩ :=
    source.factorization (productBlock H source blocks)
  have hblocks : productIdempotent H blocks =
      (productBlock H source blocks).val := rfl
  have hother : productIdempotent H other =
      (productBlock H source blocks).val :=
    congrArg (fun b : LiteralPrimitiveBlock k (∀ i, H i) ↦ b.val) h.symm
  exact (hunique blocks hblocks).trans (hunique other hother).symm

/-- Every actual primitive block is reached, not just a selected block list. -/
theorem productBlock_surjective : Function.Surjective (productBlock H source) := by
  intro b
  obtain ⟨blocks, hblocks, hunique⟩ := source.factorization b
  exact ⟨blocks, Subtype.ext hblocks⟩

/-- The equivalence is a deduction from literal product-element factorization. -/
def productBlockEquiv :
    (∀ i, LiteralPrimitiveBlock k (H i)) ≃ LiteralPrimitiveBlock k (∀ i, H i) :=
  Equiv.ofBijective (productBlock H source)
    ⟨productBlock_injective H source, productBlock_surjective H source⟩

@[simp]
theorem productBlockEquiv_apply (blocks : ∀ i, LiteralPrimitiveBlock k (H i)) :
    productBlockEquiv H source blocks = productBlock H source blocks :=
  rfl

/-- The recovered factor tuple has the original group's literal coefficients. -/
theorem productBlockEquiv_symm_value (b : LiteralPrimitiveBlock k (∀ i, H i)) :
    productIdempotent H ((productBlockEquiv H source).symm b) = b.val :=
  congrArg (fun c : LiteralPrimitiveBlock k (∀ i, H i) ↦ c.val)
    ((productBlockEquiv H source).apply_symm_apply b)

section BrauerSupport

variable {p : ℕ} {K : Type v}
variable [Field K] [CharZero K] [CharP k p]

/-- The existing actual supporting-block construction on a literal catalogue.
Character injectivity is supplied by the checked root-embedding theorem. -/
def brauerBlock {G : Type u} [Group G] [Finite G]
    [Fintype (LiteralPrimitiveBlock k G)]
    (root : PrimeRegularRootEmbedding p k K G)
    (D : BlockIdempotentDecomposition
      (fun b : LiteralPrimitiveBlock k G ↦ b.val))
    (phi : IBr root) : LiteralPrimitiveBlock k G :=
  irreducibleBrauerCharacterBlock root
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root) D phi

variable (iota : PrimeRegularRootEmbedding p k K (∀ i, H i))
variable (factorRoot : ∀ i, PrimeRegularRootEmbedding p k K (H i))
variable (characters : TypeBFiniteProductNaturality.ExternalProductData H iota factorRoot)
variable [Fintype (LiteralPrimitiveBlock k (∀ i, H i))]
variable [∀ i, Fintype (LiteralPrimitiveBlock k (H i))]
variable (productDecomposition : BlockIdempotentDecomposition
  (fun b : LiteralPrimitiveBlock k (∀ i, H i) ↦ b.val))
variable (factorDecomposition : ∀ i, BlockIdempotentDecomposition
  (fun b : LiteralPrimitiveBlock k (H i) ↦ b.val))

/-- The supporting-block dictionary for the SAME complete Brauer coordinates.
Its sole field is an equality in the actual product group algebra. -/
structure BrauerSupportSource : Prop where
  supporting_block : ∀ psi : IBr iota,
    (brauerBlock iota productDecomposition psi).val =
      productIdempotent H (fun i ↦
        brauerBlock (factorRoot i) (factorDecomposition i)
          (characters.characters psi i))

variable (support : BrauerSupportSource H iota factorRoot characters
  productDecomposition factorDecomposition)

include support in
/-- The element-level support equation gives equality of actual primitive blocks. -/
theorem brauerBlock_eq_productBlock (psi : IBr iota) :
    brauerBlock iota productDecomposition psi =
      productBlock H source (fun i ↦
        brauerBlock (factorRoot i) (factorDecomposition i)
          (characters.characters psi i)) := by
  apply Subtype.ext
  exact support.supporting_block psi

include support in
/-- Unique block coordinates agree with the blocks of the actual Brauer coordinates. -/
theorem productBlockEquiv_symm_brauerBlock (psi : IBr iota) :
    (productBlockEquiv H source).symm (brauerBlock iota productDecomposition psi) =
      (fun i ↦ brauerBlock (factorRoot i) (factorDecomposition i)
        (characters.characters psi i)) := by
  apply (productBlockEquiv H source).injective
  exact ((productBlockEquiv H source).apply_symm_apply
    (brauerBlock iota productDecomposition psi)).trans
      (brauerBlock_eq_productBlock H source iota factorRoot characters
        productDecomposition factorDecomposition support psi)

end BrauerSupport

end ModularRep.PaperProofs.TypeBRankThreeProductBlockSource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
