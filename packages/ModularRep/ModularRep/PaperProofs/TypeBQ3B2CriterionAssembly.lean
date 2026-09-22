import ModularRep.PaperProofs.TypeBQ3B2PairExtension
import ModularRep.PaperProofs.TypeBQ3FaithfulRadicalCovariance
import ModularRep.PaperProofs.TypeBQ3PrincipalCriterionPointwise

/-!
The fixed-block clauses on the actual matrix G3 are decoded from one
constructed matching. Its intrinsic character-action graph determines the
radical and local-character covariance. One raw representative is selected
for each matched class before the specified extension sources are supplied.
The two extensions are constructed once for that pair and retained when the
base coordinates are conjugated to every prescribed local representative.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBQ3B2CriterionAssembly

open ModularRep CharacterWeight
open TypeBQ3TripleCoverCarrier TypeBRankThreePrincipalCountBinding
open TypeBCentralKernelBlockSource TypeBCentralKernelInertia
open TypeBCentralKernelTripleCertificate (PhysicalBlocks)
open TypeBQ3PrincipalWeightInflation TypeBQ3PrincipalRadicalDecoding
open TypeBQ3PrincipalCriterionData TypeBQ3PrincipalExtensionApplication
open TypeBQ3PrincipalPairBlockChoice
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierActualNormalizerBase
open Representation.Extension NavarroBrauerRestrictionCovering

variable {k K : Type} [Field k] [Field K] [CharP k 2]
  [IsAlgClosed k] [CharZero K]

local instance groupFintype (Y : Type) [Group Y] [Finite Y] : Fintype Y :=
  Fintype.ofFinite Y

local instance twoPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable (root : PrimeRegularRootEmbedding 2 k K G3)
  (S : OmegaWeightSource (k := k) (K := K) (ZMod 3))
  (b : LiteralPrimitiveBlock k G3)

/-- Complete clauses for this specified block and this unchanged matching. -/
def CompleteClauses (omega : BrauerFibre root b ≃ CoverWeight S b) : Prop :=
  (∀ (alpha : (MulAut G3)ᵐᵒᵖ) (phi psi : BrauerFibre root b),
    psi.val = alpha • phi.val → (omega psi).val = alpha • (omega phi).val) ∧
  (∀ (alpha : (MulAut G3)ᵐᵒᵖ) (phi psi : BrauerFibre root b),
    psi.val = alpha • phi.val → part omega psi = alpha • part omega phi) ∧
  (∃ partition : BrauerFibre root b ≃
      Σ c : RadicalConjugacyClass (p := 2) (G := G3),
        {phi : BrauerFibre root b // part omega phi = c},
    (∀ phi, (partition phi).1 = part omega phi) ∧
    (∀ phi, (partition phi).2.val = phi)) ∧
  ∃ localEquiv : ∀ Q : RadicalSubgroup (p := 2) (G := G3),
      BrauerAtRadical omega Q ≃ RepresentativeDZ Nat.prime_two S Q b,
    (∀ Q phi, TypeBQ3PrincipalWeightInflation.classOf
      (characterWeightAt Nat.prime_two Q (localEquiv Q phi).val) =
      (omega phi.val).val) ∧
    (∀ (alpha : (MulAut G3)ᵐᵒᵖ)
        (Q : RadicalSubgroup (p := 2) (G := G3))
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

/-- The two quotient representatives retain the specified weight-block guard. -/
theorem exists_raw_representative (weight : CoverWeight S b) :
    ∃ W : {W : CharacterWeight 2 K G3 // S.operations.rawWeightBlock W = b},
      TypeBQ3PrincipalWeightInflation.classOf W.val = weight.val := by
  obtain ⟨iso, hiso⟩ := Quotient.exists_rep weight.val
  obtain ⟨W, hW⟩ := Quotient.exists_rep iso
  have same : TypeBQ3PrincipalWeightInflation.classOf W = weight.val := by
    exact (congrArg
      (fun t : CharacterWeight.IsoClass (p := 2) (K := K) (G := G3) =>
        (Quotient.mk'' t : CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := G3)))
      hW).trans hiso
  have support : S.operations.rawWeightBlock W = b := by
    change S.weightBlock (TypeBQ3PrincipalWeightInflation.classOf W) = b
    rw [same]
    exact weight.property
  exact ⟨⟨W, support⟩, same⟩

/-- Only the selected matched pairs require the specified extension sources. -/
theorem of_matching
    (matrixSource : MatrixExceptionalSource)
    (automorphisms : TypeBQ3TripleCoverAutomorphisms.MatrixAutomorphismSource)
    (indexTwo : (G (ZMod 3)).index = 2)
    (literalAt : S.operations.ambientBlockData.blockIdempotent b = b.val)
    (omega : BrauerFibre root b ≃ CoverWeight S b)
    (graph : ∀ (alpha : (MulAut G3)ᵐᵒᵖ) (phi psi : BrauerFibre root b),
      psi.val = alpha • phi.val → (omega psi).val = alpha • (omega phi).val) :
    ∃ selected : (phi : BrauerFibre root b) →
        {W : CharacterWeight 2 K G3 // S.operations.rawWeightBlock W = b},
      (∀ phi, TypeBQ3PrincipalWeightInflation.classOf (selected phi).val = (omega phi).val) ∧
      ∀ (reductions : ∀ phi : BrauerFibre root b,
            CanonicalRawReduction root (selected phi).val)
        (compatibility : ∀ phi : BrauerFibre root b,
          NavarroLocalReductionInflationBlockCompatibility.normalizerBrauerBlock
            S.operations (selected phi).val.subgroup (reductions phi).normalizerRoot
              (reductions phi).localBrauer =
          S.operations.inflateToNormalizer (selected phi).val.subgroup
            (S.operations.localCharacterBlock (selected phi).val.subgroup
              (selected phi).val.localCharacter (selected phi).val.defectZero))
        (ambientBlocks : ∀ phi : BrauerFibre root b,
          PhysicalBlocks k (ActualAutAmbient root phi.val))
        (localBlocks : ∀ phi : BrauerFibre root b, PhysicalBlocks k
          (embeddedNormalizer (innerEmbedding root phi.val) (selected phi).val.subgroup))
        (principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} 2 k)
        (ambientSeed : ∀ phi : BrauerFibre root b,
          PrimeRegularRootEmbedding 2 k K (ActualAutAmbient root phi.val))
        (fieldSource : SpathCoefficientField 2 k Nat.prime_two)
        (S9295 : Navarro9295BrauerRestrictionCoveringPrinciple 2 k K)
        (S96 : Navarro96PGroupCoveringUniquenessPrinciple 2 k)
        (S414 : ∀ phi : BrauerFibre root b,
          letI := (localBlocks phi).blockFintype
          Navarro414IntervalCentralCharacterSource
            (TypeBQ3PrincipalPairBaseInduction.embeddedRadicalInterval
              root phi.val (selected phi).val)
            (localBlocks phi).decomposition (localBlocks phi).catalogue),
        CompleteClauses root S b omega := by
  let selected : (phi : BrauerFibre root b) →
      {W : CharacterWeight 2 K G3 // S.operations.rawWeightBlock W = b} :=
    fun phi => Classical.choose (exists_raw_representative S b (omega phi))
  have selectedClass : ∀ phi : BrauerFibre root b,
      TypeBQ3PrincipalWeightInflation.classOf (selected phi).val = (omega phi).val :=
    fun phi => Classical.choose_spec (exists_raw_representative S b (omega phi))
  refine ⟨selected, selectedClass, ?_⟩
  intro reductions compatibility ambientBlocks localBlocks principle ambientSeed
    fieldSource S9295 S96 S414
  have fixedPair (phi : BrauerFibre root b) (alpha : MulAut G3)
      (fixed : MulOpposite.op alpha • phi.val = phi.val) :
      MulOpposite.op alpha • TypeBQ3PrincipalPairExtensions.rawClass (selected phi).val =
        TypeBQ3PrincipalPairExtensions.rawClass (selected phi).val := by
    change MulOpposite.op alpha • TypeBQ3PrincipalWeightInflation.classOf (selected phi).val =
      TypeBQ3PrincipalWeightInflation.classOf (selected phi).val
    rw [selectedClass phi]
    exact (graph (MulOpposite.op alpha) phi phi fixed.symm).symm
  let packets : ∀ phi : BrauerFibre root b,
      MatchedExtensionData root phi.val (selected phi).val (reductions phi)
        (TypeBQ3PrincipalInertiaQuotient.center_eq_bot matrixSource) :=
    fun phi => Classical.choice
      (TypeBQ3B2PairExtension.exists_pair_extensions_all_intermediate
        matrixSource automorphisms indexTwo S root b phi.val literalAt phi.property
        (selected phi).val (selected phi).property (fixedPair phi)
        (reductions phi) (compatibility phi) (ambientBlocks phi) (localBlocks phi)
        principle (ambientSeed phi) fieldSource S9295 S96 (S414 phi))
  refine ⟨graph, ?_,
    ⟨partitionEquiv omega, partitionEquiv_part omega, partitionEquiv_character omega⟩,
    (fun Q => localMap omega Q), localMap_class omega, ?_, ?_⟩
  · intro alpha phi psi same
    exact TypeBQ3FaithfulRadicalCovariance.part_of_class_transport omega
      alpha phi psi (graph alpha phi psi same)
  · intro alpha Q phi psi same
    have transported : (omega psi.val).val = alpha • (omega phi.val).val :=
      graph alpha phi.val psi.val same
    exact ⟨TypeBQ3FaithfulRadicalCovariance.localMap_of_class_transport omega
        alpha Q phi psi transported,
      TypeBQ3FaithfulRadicalCovariance.localMap_raw_of_class_transport omega
        alpha Q phi psi transported⟩
  · intro Q phi
    exact TypeBQ3PrincipalCriterionPointwise.exists_for_prescribed
      root phi.val.val (selected phi.val).val (reductions phi.val)
      (TypeBQ3PrincipalInertiaQuotient.center_eq_bot matrixSource) (packets phi.val)
      (characterWeightAt Nat.prime_two Q (localMap omega Q phi).val)
      ((selectedClass phi.val).trans (localMap_class omega Q phi).symm)

end ModularRep.PaperProofs.TypeBQ3B2CriterionAssembly


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
