import ModularRep.PaperProofs.OddTwoPrincipalProductAtlas

/-!
# The full normalizer of the actual independent product

An (3B) identifies the full normalizer quotient by block-monomial matrices.
The source input here fixes that map on actual normalizer elements, including
permutations of equal basic blocks. The quotient equivalence must commute
with that displayed map. Thus it cannot be replaced by an unrelated
abstract isomorphism or by the product of the basic normalizer quotients.

The existing wreath convention is the right-action convention: matrices
are P_pi D_f, with the coefficient in the column block. The source's usual
left-action convention is converted by this explicit matrix equation.
These group and coordinate assertions remain E1/E2. There is no character,
radicality, principal membership or final iBAW assertion in this packet.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoPrincipalProductNormalizer

open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
open ModularRep.PaperProofs.OddTwoPrincipalProductAtlas
open ModularRep.PaperProofs.OddTwoWreathReflection

universe u

variable {n : ℕ} {F : Type u} [Field F] [Fintype F]
variable (P : ProductShape n F)

abbrev SymmetricWreath (H : Type u) (d : ℕ) :=
  PermutationWreathProduct H (MonoidHom.id (Equiv.Perm (Fin d)))

abbrev BasicNormalizer (i : Fin P.count) :=
  Subgroup.normalizer ((P.basic i).subgroup : Set (Sp (P.rank i) F))

abbrev BasicQuotient (i : Fin P.count) := NormalizerQuotient (P.basic i).subgroup

abbrev NormalizerWreaths := (i : Fin P.count) →
  SymmetricWreath (BasicNormalizer P i) (P.copies i)

abbrev QuotientWreaths := (i : Fin P.count) →
  SymmetricWreath (BasicQuotient P i) (P.copies i)

/-- Explicit grouping of the independent block coordinates. -/
def groupedCoordinates :
    (Σ i : Fin P.count, Fin (P.copies i) ×
      (Fin (P.rank i) ⊕ Fin (P.rank i))) ≃ P.Coordinates where
  toFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  invFun x := ⟨x.1.1, x.1.2, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Actual block-monomial matrix, in the existing right-action convention.
The coefficient is the column block b and the output block is pi(b). -/
def basicMonomialMatrix (i : Fin P.count)
    (z : SymmetricWreath (BasicNormalizer P i) (P.copies i)) :
    Matrix (Fin (P.copies i) × (Fin (P.rank i) ⊕ Fin (P.rank i)))
      (Fin (P.copies i) × (Fin (P.rank i) ⊕ Fin (P.rank i))) F :=
  fun a b => if a.1 = z.right b.1 then
    ((z.left b.1).1 : Matrix (Fin (P.rank i) ⊕ Fin (P.rank i))
      (Fin (P.rank i) ⊕ Fin (P.rank i)) F) a.2 b.2 else 0

/-- Coordinatewise quotient of the ACTUAL basic normalizer elements. -/
def quotientWreathMap (z : NormalizerWreaths P) : QuotientWreaths P := fun i =>
  ⟨fun j => QuotientGroup.mk' ((P.basic i).subgroup.subgroupOf
      (Subgroup.normalizer ((P.basic i).subgroup : Set (Sp (P.rank i) F))))
        ((z i).left j),
    (z i).right⟩

/-- Equality of actual basic conjugacy types, with the literal same-rank
coordinate cast. Equal abstract group types alone do not satisfy this. -/
def BasicConjugate (i j : Fin P.count) : Prop :=
  ∃ (h : P.rank i = P.rank j) (g : Sp (P.rank j) F),
    (cast (congrArg (fun r => Subgroup (Sp r F)) h) (P.basic i).subgroup).comap
        (MulAut.conj g⁻¹).toMonoidHom = (P.basic j).subgroup

variable (A : P.Geometry)

/-- The actual An (3B) realization. The quotient square and full matrix
formula bind the source equivalence to the same product subgroup. The
centralizer containment is the displayed scalar-centralizer consequence
for these surviving models. It is not a statement about a free theta.
-/
structure AnProductNormalizerSource where
  separated : ∀ i j, BasicConjugate P i j → i = j
  normalizerLift : NormalizerWreaths P →*
    Subgroup.normalizer (A.subgroup : Set (Sp n F))
  normalizerLift_matrix : ∀ z,
    ((normalizerLift z).1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      Matrix.reindex ((groupedCoordinates P).trans A.basisIndex)
        ((groupedCoordinates P).trans A.basisIndex)
          (Matrix.blockDiagonal' (fun i => basicMonomialMatrix P i (z i)))
  quotientEquiv : QuotientWreaths P ≃* NormalizerQuotient A.subgroup
  quotient_square : ∀ z,
    quotientEquiv (quotientWreathMap P z) =
      QuotientGroup.mk' (A.subgroup.subgroupOf
        (Subgroup.normalizer (A.subgroup : Set (Sp n F)))) (normalizerLift z)
  centralizer_le : Subgroup.centralizer (A.subgroup : Set (Sp n F)) ≤ A.subgroup

namespace AnProductNormalizerSource

variable {P A} (S : AnProductNormalizerSource P A)

/-- The normalizer element used by character inflation has exactly the
block-monomial lift prescribed by the source. -/
theorem inverse_quotient_lift (z : NormalizerWreaths P) :
    S.quotientEquiv.symm
      (QuotientGroup.mk' (A.subgroup.subgroupOf
        (Subgroup.normalizer (A.subgroup : Set (Sp n F)))) (S.normalizerLift z)) =
      quotientWreathMap P z := by
  rw [← S.quotient_square, MulEquiv.symm_apply_apply]

end AnProductNormalizerSource

end ModularRep.PaperProofs.OddTwoPrincipalProductNormalizer


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
