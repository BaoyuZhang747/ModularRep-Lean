import ModularRep.PaperProofs.TypeBQ3B2CriterionAssembly

/-!
The complete fixed-block clauses use the actual group, root, primitive
block, weight source and unchanged matching. This output has the same
conjuncts as the matrix-group clauses. The normalization theorems retain
the existing partition, local character equivalences and extension data.
They do not transport a criterion across a group isomorphism.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBQ3AssemblyCriterionData

open ModularRep CharacterWeight
open TypeBCentralKernelBlockSource TypeBCentralKernelInertia
open TypeBQ3PrincipalWeightInflation TypeBQ3PrincipalRadicalDecoding
open TypeBQ3PrincipalCriterionData

variable {k K Y : Type} [Field k] [Field K] [CharP k 2]
  [IsAlgClosed k] [CharZero K] [Group Y] [Finite Y]

local instance groupFintype (Z : Type) [Group Z] [Finite Z] : Fintype Z :=
  Fintype.ofFinite Z

local instance twoPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable (root : PrimeRegularRootEmbedding 2 k K Y)
  (R : CoverWeightSource (k := k) (K := K) Y)
  (b : LiteralPrimitiveBlock k Y)

/-- Complete clauses on the displayed specified fibres and matching. -/
def CompleteClauses (omega : BrauerFibre root b ≃ CoverWeight R b) : Prop :=
  (∀ (alpha : (MulAut Y)ᵐᵒᵖ) (phi psi : BrauerFibre root b),
    psi.val = alpha • phi.val → (omega psi).val = alpha • (omega phi).val) ∧
  (∀ (alpha : (MulAut Y)ᵐᵒᵖ) (phi psi : BrauerFibre root b),
    psi.val = alpha • phi.val → part omega psi = alpha • part omega phi) ∧
  (∃ partition : BrauerFibre root b ≃
      Σ c : RadicalConjugacyClass (p := 2) (G := Y),
        {phi : BrauerFibre root b // part omega phi = c},
    (∀ phi, (partition phi).1 = part omega phi) ∧
    (∀ phi, (partition phi).2.val = phi)) ∧
  ∃ localEquiv : ∀ Q : RadicalSubgroup (p := 2) (G := Y),
      BrauerAtRadical omega Q ≃ RepresentativeDZ Nat.prime_two R Q b,
    (∀ Q phi, TypeBQ3PrincipalWeightInflation.classOf
      (characterWeightAt Nat.prime_two Q (localEquiv Q phi).val) =
      (omega phi.val).val) ∧
    (∀ (alpha : (MulAut Y)ᵐᵒᵖ)
        (Q : RadicalSubgroup (p := 2) (G := Y))
        (phi : BrauerAtRadical omega Q)
        (psi : BrauerAtRadical omega (Q.rightTwist alpha.unop)),
      psi.val.val = alpha • phi.val.val →
      (localEquiv (Q.rightTwist alpha.unop) psi).val =
          localCharacterTwist Q alpha (localEquiv Q phi).val ∧
        CharacterWeight.Isomorphic
          ((characterWeightAt Nat.prime_two Q (localEquiv Q phi).val).rightTwist alpha.unop)
          (characterWeightAt Nat.prime_two (Q.rightTwist alpha.unop)
            (localEquiv (Q.rightTwist alpha.unop) psi).val)) ∧
    (∀ Q phi, Nonempty (PrincipalClauseIII root phi.val.val
      (characterWeightAt Nat.prime_two Q (localEquiv Q phi).val)))

/-- The existing matrix-group output is definitionally the same output. -/
theorem of_b2
    (root : PrimeRegularRootEmbedding 2 k K TypeBQ3TripleCoverCarrier.G3)
    (R : TypeBRankThreePrincipalCountBinding.OmegaWeightSource
      (k := k) (K := K) (ZMod 3))
    (b : LiteralPrimitiveBlock k TypeBQ3TripleCoverCarrier.G3)
    (omega : BrauerFibre root b ≃ CoverWeight R b)
    (clauses : TypeBQ3B2CriterionAssembly.CompleteClauses root R b omega) :
    CompleteClauses root R b omega := clauses

/-- Principal action equations give the intrinsic supported-action graph
with the same partition, local equivalences and Clause III witnesses. -/
theorem of_principalClauses
    (literal : ∀ c, R.operations.ambientBlockData.blockIdempotent c = c.val)
    (hb : IsPrincipal b)
    (omega : BrauerFibre root b ≃ CoverWeight R b)
    (clauses : letI := R.operations.ambientBlockData.fintypeBlock
      (∀ (alpha : (MulAut Y)ᵐᵒᵖ) (phi : BrauerFibre root b),
        omega (TypeBQ3PrincipalBrauerInflation.principalStep root
          (coverDecomposition R literal) b hb alpha phi) =
        coverWeightStep R literal b hb alpha (omega phi)) ∧
      (∀ (alpha : (MulAut Y)ᵐᵒᵖ) (phi : BrauerFibre root b),
        part omega (TypeBQ3PrincipalBrauerInflation.principalStep root
          (coverDecomposition R literal) b hb alpha phi) = alpha • part omega phi) ∧
      (∃ partition : BrauerFibre root b ≃
          Σ c : RadicalConjugacyClass (p := 2) (G := Y),
            {phi : BrauerFibre root b // part omega phi = c},
        (∀ phi, (partition phi).1 = part omega phi) ∧
        (∀ phi, (partition phi).2.val = phi)) ∧
      ∃ localEquiv : ∀ Q : RadicalSubgroup (p := 2) (G := Y),
          BrauerAtRadical omega Q ≃ RepresentativeDZ Nat.prime_two R Q b,
        (∀ Q phi, TypeBQ3PrincipalWeightInflation.classOf
          (characterWeightAt Nat.prime_two Q (localEquiv Q phi).val) =
          (omega phi.val).val) ∧
        (∀ (alpha : (MulAut Y)ᵐᵒᵖ)
            (Q : RadicalSubgroup (p := 2) (G := Y))
            (phi : BrauerAtRadical omega Q)
            (psi : BrauerAtRadical omega (Q.rightTwist alpha.unop)),
          psi.val = TypeBQ3PrincipalBrauerInflation.principalStep root
            (coverDecomposition R literal) b hb alpha phi.val →
          (localEquiv (Q.rightTwist alpha.unop) psi).val =
              localCharacterTwist Q alpha (localEquiv Q phi).val ∧
            CharacterWeight.Isomorphic
              ((characterWeightAt Nat.prime_two Q
                (localEquiv Q phi).val).rightTwist alpha.unop)
              (characterWeightAt Nat.prime_two (Q.rightTwist alpha.unop)
                (localEquiv (Q.rightTwist alpha.unop) psi).val)) ∧
        (∀ Q phi, Nonempty (PrincipalClauseIII root phi.val.val
          (characterWeightAt Nat.prime_two Q (localEquiv Q phi).val)))) :
    CompleteClauses root R b omega := by
  letI := R.operations.ambientBlockData.fintypeBlock
  obtain ⟨equivariant, radical, partition, localEquiv, localClass,
    localCovariance, packets⟩ := clauses
  refine ⟨?_, ?_, partition, localEquiv, localClass, ?_, packets⟩
  · intro alpha phi psi values
    have same : psi = TypeBQ3PrincipalBrauerInflation.principalStep root
        (coverDecomposition R literal) b hb alpha phi := Subtype.ext values
    exact (congrArg (fun z : BrauerFibre root b => (omega z).val) same).trans
      (congrArg (fun w : CoverWeight R b => w.val) (equivariant alpha phi))
  · intro alpha phi psi values
    have same : psi = TypeBQ3PrincipalBrauerInflation.principalStep root
        (coverDecomposition R literal) b hb alpha phi := Subtype.ext values
    exact (congrArg (part omega) same).trans (radical alpha phi)
  · intro alpha Q phi psi values
    have same : psi.val = TypeBQ3PrincipalBrauerInflation.principalStep root
        (coverDecomposition R literal) b hb alpha phi.val := Subtype.ext values
    exact localCovariance alpha Q phi psi same

end ModularRep.PaperProofs.TypeBQ3AssemblyCriterionData


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
