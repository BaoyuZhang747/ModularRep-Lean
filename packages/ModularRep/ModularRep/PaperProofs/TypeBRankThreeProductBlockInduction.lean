import ModularRep.BlockInduction
import ModularRep.PrimitiveBlockAutomorphism
import Mathlib.Data.Finsupp.Defs
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Block induction on literal finite products

The product group algebra elements are fixed by their coefficients.
The uniform elementary source records centrality, spanning by pure central
products, and the evaluations of the same complete block catalogues.
Coefficient restriction is computed in the original subgroup coordinates.
Factor block inductions then determine the product induced central function.
-/

noncomputable section

open scoped BigOperators MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBRankThreeProductBlockInduction

open ModularRep

universe u

variable {I k : Type u} [Fintype I] [Field k]
variable (H : I → Type u) [∀ i, Group (H i)] [∀ i, Fintype (H i)]

/-- The literal pure product of group algebra elements. -/
def coefficientProduct (z : ∀ i, k[H i]) : k[∀ i, H i] :=
  MonoidAlgebra.ofCoeff
    (Finsupp.equivFunOnFinite.symm (fun g => ∏ i, (z i).coeff (g i)))

@[simp] theorem coefficientProduct_coeff (z : ∀ i, k[H i]) (g : ∀ i, H i) :
    (coefficientProduct H z).coeff g = ∏ i, (z i).coeff (g i) := rfl

variable (S : ∀ i, Subgroup (H i))

local instance subgroupFintype {A : Type u} [Group A] [Finite A]
    (Q : Subgroup A) : Fintype Q := Fintype.ofFinite Q

/-- The original coordinate of an element of the literal subgroup product. -/
def subgroupCoordinate (x : Subgroup.pi Set.univ S) (i : I) : S i :=
  ⟨x.val i, (Subgroup.mem_pi Set.univ).mp x.property i (Set.mem_univ i)⟩

@[simp] theorem subgroupCoordinate_val (x : Subgroup.pi Set.univ S) (i : I) :
    (subgroupCoordinate H S x i).val = x.val i := rfl

/-- The local pure product lies in the actual subgroup algebra. -/
def subgroupCoefficientProduct (z : ∀ i, k[S i]) :
    k[Subgroup.pi Set.univ S] :=
  MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm
    (fun x => ∏ i, (z i).coeff (subgroupCoordinate H S x i)))

@[simp] theorem subgroupCoefficientProduct_coeff (z : ∀ i, k[S i])
    (x : Subgroup.pi Set.univ S) :
    (subgroupCoefficientProduct H S z).coeff x =
      ∏ i, (z i).coeff (subgroupCoordinate H S x i) := rfl

/-- Centrality concerns the fixed coefficient formula. -/
def AmbientProductCentrality : Prop :=
  ∀ z : ∀ i, GroupAlgebraCenter k (H i),
    coefficientProduct H (fun i => (z i : k[H i])) ∈
      GroupAlgebraCenter k (∀ i, H i)

/-- Centrality for the same local coefficient formula. -/
def LocalProductCentrality : Prop :=
  ∀ z : ∀ i, GroupAlgebraCenter k (S i),
    subgroupCoefficientProduct H S (fun i => (z i : k[S i])) ∈
      GroupAlgebraCenter k (Subgroup.pi Set.univ S)

/-- Bundle the prescribed ambient product as a central element. -/
def ambientCenterProduct (central : AmbientProductCentrality (k := k) H)
    (z : ∀ i, GroupAlgebraCenter k (H i)) :
    GroupAlgebraCenter k (∀ i, H i) :=
  ⟨coefficientProduct H (fun i => (z i : k[H i])), central z⟩

/-- Bundle the prescribed local product as a central element. -/
def localCenterProduct (central : LocalProductCentrality (k := k) H S)
    (z : ∀ i, GroupAlgebraCenter k (S i)) :
    GroupAlgebraCenter k (Subgroup.pi Set.univ S) :=
  ⟨subgroupCoefficientProduct H S (fun i => (z i : k[S i])), central z⟩

/-- Uniform E1 centre tensor facts, with the spanning set fixed in advance.
No assertion about block induction occurs in this source. -/
structure CenterProductSource : Prop where
  ambient_central : AmbientProductCentrality (k := k) H
  local_central : LocalProductCentrality (k := k) H S
  ambient_spanning :
    Submodule.span k (Set.range (ambientCenterProduct H ambient_central)) = ⊤

/-- Coefficient restriction commutes with the literal pure products. -/
theorem centerCoeffRestrict_product
    (center : CenterProductSource (k := k) H S)
    (z : ∀ i, GroupAlgebraCenter k (H i)) :
    centerCoeffRestrict (Subgroup.pi Set.univ S)
        (ambientCenterProduct H center.ambient_central z) =
      localCenterProduct H S center.local_central
        (fun i => centerCoeffRestrict (S i) (z i)) := by
  apply Subtype.ext
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro x
  change (coeffRestrict (Subgroup.pi Set.univ S)
      (coefficientProduct H (fun i => (z i : k[H i])))).coeff x =
    (subgroupCoefficientProduct H S
      (fun i => (centerCoeffRestrict (S i) (z i) : k[S i]))).coeff x
  rw [coeffRestrict_apply, coefficientProduct_coeff, subgroupCoefficientProduct_coeff]
  apply Finset.prod_congr rfl
  intro i _
  exact (coeffRestrict_apply (S i) (z i : k[H i])
    (subgroupCoordinate H S x i)).symm

section Catalogues

local instance indexDecidableEq : DecidableEq I := Classical.decEq I

variable [IsAlgClosed k]
variable [∀ i, Fintype (LiteralPrimitiveBlock k (H i))]
variable [∀ i, Fintype (LiteralPrimitiveBlock k (S i))]

variable (factorAmbientBlocks : ∀ i, BlockIdempotentDecomposition
  (fun b : LiteralPrimitiveBlock k (H i) => b.val))
variable (factorLocalBlocks : ∀ i, BlockIdempotentDecomposition
  (fun b : LiteralPrimitiveBlock k (S i) => b.val))
variable (ambientBlocks : BlockIdempotentDecomposition
  (fun b : ∀ i, LiteralPrimitiveBlock k (H i) =>
    coefficientProduct H (fun i => (b i).val)))
variable (localBlocks : BlockIdempotentDecomposition
  (fun b : ∀ i, LiteralPrimitiveBlock k (S i) =>
    subgroupCoefficientProduct H S (fun i => (b i).val)))

variable (factorAmbientCatalogue : ∀ i,
  BlockCentralCharacterCatalogue (factorAmbientBlocks i))
variable (factorLocalCatalogue : ∀ i,
  BlockCentralCharacterCatalogue (factorLocalBlocks i))
variable (ambientCatalogue : BlockCentralCharacterCatalogue ambientBlocks)
variable (localCatalogue : BlockCentralCharacterCatalogue localBlocks)
variable (center : CenterProductSource (k := k) H S)

/-- Uniform evaluations on pure central products in the exact catalogues.
The labels are tuples of actual factor primitives and the decompositions
use their prescribed coefficient products. -/
structure CatalogueProductSource : Prop where
  ambient_evaluation : ∀ (b : ∀ i, LiteralPrimitiveBlock k (H i))
      (z : ∀ i, GroupAlgebraCenter k (H i)),
    ambientCatalogue.centralCharacter b
        (ambientCenterProduct H center.ambient_central z) =
      ∏ i, (factorAmbientCatalogue i).centralCharacter (b i) (z i)
  local_evaluation : ∀ (b : ∀ i, LiteralPrimitiveBlock k (S i))
      (z : ∀ i, GroupAlgebraCenter k (S i)),
    localCatalogue.centralCharacter b
        (localCenterProduct H S center.local_central z) =
      ∏ i, (factorLocalCatalogue i).centralCharacter (b i) (z i)

variable (dictionary : CatalogueProductSource H S factorAmbientBlocks factorLocalBlocks
  ambientBlocks localBlocks factorAmbientCatalogue factorLocalCatalogue
  ambientCatalogue localCatalogue center)

include dictionary in
/-- Factor induction identifies the entire induced linear map, not only
its values on primitive block idempotents. -/
theorem inducedCentralFunction_product
    (b : ∀ i, LiteralPrimitiveBlock k (S i))
    (B : ∀ i, LiteralPrimitiveBlock k (H i))
    (factor : ∀ i, BlockInducesTo (S i)
      (factorLocalCatalogue i) (factorAmbientCatalogue i) (b i) (B i)) :
    inducedCentralFunction (Subgroup.pi Set.univ S)
        (localCatalogue.centralCharacter b) =
      (ambientCatalogue.centralCharacter B).toLinearMap := by
  apply LinearMap.ext_on_range center.ambient_spanning
  intro z
  change inducedCentralFunction (Subgroup.pi Set.univ S)
      (localCatalogue.centralCharacter b)
      (ambientCenterProduct H center.ambient_central z) =
    ambientCatalogue.centralCharacter B
      (ambientCenterProduct H center.ambient_central z)
  rw [inducedCentralFunction_apply, centerCoeffRestrict_product H S center,
    dictionary.local_evaluation, dictionary.ambient_evaluation]
  apply Finset.prod_congr rfl
  intro i _
  obtain ⟨defined, equation⟩ := factor i
  exact congrArg
    (fun f : GroupAlgebraCenter k (H i) →ₐ[k] k => f (z i)) equation

include dictionary in
/-- The actual product local block induces to the actual product ambient
block because the factor inductions agree on a spanning set of the centre. -/
theorem blockInducesTo_product
    (b : ∀ i, LiteralPrimitiveBlock k (S i))
    (B : ∀ i, LiteralPrimitiveBlock k (H i))
    (factor : ∀ i, BlockInducesTo (S i)
      (factorLocalCatalogue i) (factorAmbientCatalogue i) (b i) (B i)) :
    BlockInducesTo (Subgroup.pi Set.univ S)
      localCatalogue ambientCatalogue b B := by
  have equation := inducedCentralFunction_product H S factorAmbientBlocks factorLocalBlocks
    ambientBlocks localBlocks factorAmbientCatalogue factorLocalCatalogue
    ambientCatalogue localCatalogue center dictionary b B factor
  have defined : IsBlockInductionDefined (Subgroup.pi Set.univ S)
      (localCatalogue.centralCharacter b) := by
    intro x y
    rw [equation]
    exact (ambientCatalogue.centralCharacter B).map_mul x y
  refine ⟨defined, ?_⟩
  apply AlgHom.ext
  intro z
  exact LinearMap.congr_fun equation z

end Catalogues

end ModularRep.PaperProofs.TypeBRankThreeProductBlockInduction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
