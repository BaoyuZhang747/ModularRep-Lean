import ModularRep.PaperProofs.TypeBQ3FaithfulMatching
import ModularRep.PaperProofs.TypeBQ3FaithfulFibreBinding
import ModularRep.PaperProofs.TypeBQ3FaithfulRadicalCovariance
import ModularRep.PaperProofs.TypeBQ3FaithfulCriterionPointwise
import ModularRep.PaperProofs.TypeBQ3FaithfulCriterionLocalBlocks

/-! Complete fixed-block clauses for the same constructed faithful matching.
This internal construction consumes its matching and selected local reductions;
the source application constructs both from the narrower published and table
inputs. The actual criterion carrier is X, with identity extension ambient. -/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBQ3FaithfulCriterionAssembly

open ModularRep CharacterWeight
open TypeBCentralKernelBlockSource TypeBCentralKernelInertia
open TypeBQ3PrincipalWeightInflation TypeBQ3PrincipalRadicalDecoding
open TypeBQ3PrincipalCriterionData
open TypeBExceptionalQ3Proposition416Actual TypeBQ3FaithfulFibreBinding
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open Formalisation.ComputationArithmetic
open ModularRep.FDRepSimpleClassKZero

variable {k K X : Type} [Field k] [Field K] [CharZero K]
  [Group X] [Finite X] [CharP k 2] [IsAlgClosed k]

local instance groupFintype : Fintype X := Fintype.ofFinite X

local instance twoPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable (root : PrimeRegularRootEmbedding 2 k K X)
  (hinj : IrreducibleBrauerCharacterInjectivity root)
  {d : Q3Block → k[X]} (blocks : BlockIdempotentDecomposition d)
  (i : Q3Block)

/-- Transport through the identity-on-characters named-fibre equivalence. -/
def brauerStep (alpha : actualBlockStabilizer blocks i)
    (phi : BrauerFibre root (primitiveBlockOfLabel blocks i)) :
    BrauerFibre root (primitiveBlockOfLabel blocks i) :=
  brauerFibreEquiv root hinj blocks i
    (brauerFibreAction root hinj blocks
      (canonical_brauerBlock_transport blocks root hinj) i alpha
      ((brauerFibreEquiv root hinj blocks i).symm phi))

theorem brauerStep_val (alpha : actualBlockStabilizer blocks i)
    (phi : BrauerFibre root (primitiveBlockOfLabel blocks i)) :
    (brauerStep root hinj blocks i alpha phi).val = alpha.val • phi.val := rfl

variable (R : CoverWeightSource (k := k) (K := K) X)

/-- This proposition exposes every fixed-block clause; it is only an output. -/
def CompleteClauses
    (omega : BrauerFibre root (primitiveBlockOfLabel blocks i) ≃
      CoverWeight R (primitiveBlockOfLabel blocks i)) : Prop :=
  (∀ (alpha : actualBlockStabilizer blocks i) phi,
    (omega (brauerStep root hinj blocks i alpha phi)).val =
      alpha.val • (omega phi).val) ∧
  (∀ (alpha : actualBlockStabilizer blocks i) phi,
    part omega (brauerStep root hinj blocks i alpha phi) = alpha.val • part omega phi) ∧
  (∃ partition : BrauerFibre root (primitiveBlockOfLabel blocks i) ≃
      Σ c : RadicalConjugacyClass (p := 2) (G := X),
        {phi : BrauerFibre root (primitiveBlockOfLabel blocks i) // part omega phi = c},
    (∀ phi, (partition phi).1 = part omega phi) ∧
    (∀ phi, (partition phi).2.val = phi)) ∧
  ∃ localEquiv : ∀ Q : RadicalSubgroup (p := 2) (G := X),
      BrauerAtRadical omega Q ≃ RepresentativeDZ Nat.prime_two R Q
        (primitiveBlockOfLabel blocks i),
    (∀ Q phi, TypeBQ3PrincipalWeightInflation.classOf
      (characterWeightAt Nat.prime_two Q (localEquiv Q phi).val) =
      (omega phi.val).val) ∧
    (∀ (alpha : actualBlockStabilizer blocks i)
        (Q : RadicalSubgroup (p := 2) (G := X))
        (phi : BrauerAtRadical omega Q)
        (psi : BrauerAtRadical omega (Q.rightTwist alpha.val.unop)),
      psi.val = brauerStep root hinj blocks i alpha phi.val →
      (localEquiv (Q.rightTwist alpha.val.unop) psi).val =
          localCharacterTwist Q alpha.val (localEquiv Q phi).val ∧
        CharacterWeight.Isomorphic
          ((characterWeightAt Nat.prime_two Q (localEquiv Q phi).val).rightTwist alpha.val.unop)
          (characterWeightAt Nat.prime_two (Q.rightTwist alpha.val.unop)
            (localEquiv (Q.rightTwist alpha.val.unop) psi).val)) ∧
    (∀ Q phi, Nonempty (PrincipalClauseIII root phi.val.val
      (characterWeightAt Nat.prime_two Q (localEquiv Q phi).val)))

/-- The named equivalence and all its decoded local characters satisfy the
criterion using the original character and the same selected reduction. -/
theorem of_matching
    (matching : ActualBrauerFibre root hinj blocks i ≃
      R.Fibre (primitiveBlockOfLabel blocks i))
    (matchingEquivariant : ∀ (alpha : actualBlockStabilizer blocks i) phi,
      matching (brauerFibreAction root hinj blocks
        (canonical_brauerBlock_transport blocks root hinj) i alpha phi) =
          alpha • matching phi)
    (blockInner : actualBlockStabilizer blocks i ≤
      (RepresentationWeight.innerInverseOpHom (G := X)).range)
    (centrePrimeTo : Nat.Coprime 2 (Nat.card (Subgroup.center X)))
    (literalAt : R.operations.ambientBlockData.blockIdempotent
      (primitiveBlockOfLabel blocks i) = d i)
    (reductions : ∀ (W : CharacterWeight 2 K X),
      R.operations.rawWeightBlock W = primitiveBlockOfLabel blocks i →
        CanonicalRawReduction root W)
    (physical : ∀ (W : CharacterWeight 2 K X)
        (support : R.operations.rawWeightBlock W = primitiveBlockOfLabel blocks i),
      NavarroLocalReductionInflationBlockCompatibility.normalizerBrauerBlock
        R.operations W.subgroup (reductions W support).normalizerRoot
          (reductions W support).localBrauer =
        R.operations.inflateToNormalizer W.subgroup
          (R.operations.localCharacterBlock W.subgroup W.localCharacter W.defectZero))
    (fieldSource : SpathCoefficientField 2 k Nat.prime_two) :
    ∃ omega : BrauerFibre root (primitiveBlockOfLabel blocks i) ≃
        CoverWeight R (primitiveBlockOfLabel blocks i),
      (∀ phi, omega (brauerFibreEquiv root hinj blocks i phi) = matching phi) ∧
      CompleteClauses root hinj blocks i R omega := by
  let eB := brauerFibreEquiv root hinj blocks i
  let omega : BrauerFibre root (primitiveBlockOfLabel blocks i) ≃
      CoverWeight R (primitiveBlockOfLabel blocks i) := eB.symm.trans matching
  have graph : ∀ (alpha : actualBlockStabilizer blocks i) phi,
      (omega (brauerStep root hinj blocks i alpha phi)).val =
        alpha.val • (omega phi).val := by
    intro alpha phi
    change (matching (eB.symm (eB _))).val = alpha.val • (matching (eB.symm phi)).val
    rw [eB.symm_apply_apply]
    exact congrArg Subtype.val (matchingEquivariant alpha (eB.symm phi))
  refine ⟨omega, ?_, graph, ?_,
    ⟨partitionEquiv omega, partitionEquiv_part omega, partitionEquiv_character omega⟩,
    (fun Q => localMap omega Q), localMap_class omega, ?_, ?_⟩
  · intro phi
    exact congrArg matching (eB.symm_apply_apply phi)
  · intro alpha phi
    exact TypeBQ3FaithfulRadicalCovariance.part_of_class_transport omega
      alpha.val phi _ (graph alpha phi)
  · intro alpha Q phi psi same
    have transported : (omega psi.val).val = alpha.val • (omega phi.val).val := by
      rw [same]
      exact graph alpha phi.val
    exact ⟨TypeBQ3FaithfulRadicalCovariance.localMap_of_class_transport omega
        alpha.val Q phi psi transported,
      TypeBQ3FaithfulRadicalCovariance.localMap_raw_of_class_transport omega
        alpha.val Q phi psi transported⟩
  · intro Q phi
    let W := characterWeightAt Nat.prime_two Q (localMap omega Q phi).val
    have support : R.operations.rawWeightBlock W = primitiveBlockOfLabel blocks i :=
      (localMap omega Q phi).property
    let namedPhi : IBrBlock root hinj blocks i := eB.symm phi.val
    have inertia : MulAction.stabilizer (MulAut X)ᵐᵒᵖ phi.val.val ≤
        (RepresentationWeight.innerInverseOpHom (G := X)).range :=
      (inertia_le_namedBlockStabilizer root hinj blocks i namedPhi).trans blockInner
    let topData := TypeBQ3FaithfulCriterionLocalBlocks.intermediateAtTop
      R.operations root hinj blocks i (primitiveBlockOfLabel blocks i) literalAt
      namedPhi W support (reductions W support) (physical W support) fieldSource
    exact ⟨TypeBQ3FaithfulCriterionPointwise.of_top_data root phi.val.val W
      centrePrimeTo inertia (reductions W support) topData⟩

end ModularRep.PaperProofs.TypeBQ3FaithfulCriterionAssembly


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
