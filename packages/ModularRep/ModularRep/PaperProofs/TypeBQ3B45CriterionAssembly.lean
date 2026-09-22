import ModularRep.PaperProofs.TypeBQ3B2CriterionAssembly
import ModularRep.PaperProofs.TypeBQ3B45QOneExtension
import ModularRep.PaperProofs.TypeBQ3B45DefectZeroMatching

/-!
The fixed-block criterion for a derived defect-zero matching on the actual
matrix G3. The existing radical partition and local defect-zero decoding
retain this same matching. Every prescribed decoded raw representative has
its block guard proved from its class; its trivial radical and local value
anchor then feed the actual Q=1 extension constructor.

The matching, graph, radical triviality and local anchors are intermediate
deductions of the caller, not published criterion inputs. In particular no
ClauseIII, pair-extension packet, intermediate block equation, B2-specific
count, dihedral datum or finished fixed-block criterion is assumed here.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBQ3B45CriterionAssembly

open ModularRep CharacterWeight
open TypeBQ3TripleCoverCarrier TypeBRankThreePrincipalCountBinding
open TypeBCentralKernelBlockSource TypeBCentralKernelInertia
open TypeBCentralKernelTripleCertificate (PhysicalBlocks)
open TypeBQ3PrincipalWeightInflation TypeBQ3PrincipalRadicalDecoding
open TypeBQ3PrincipalCriterionData TypeBQ3B2CriterionAssembly
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient

variable {k K : Type} [Field k] [Field K] [CharP k 2]
  [IsAlgClosed k] [CharZero K]

local instance groupFintype (Y : Type) [Group Y] [Finite Y] : Fintype Y :=
  Fintype.ofFinite Y

local instance twoPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable (root : PrimeRegularRootEmbedding 2 k K G3)
  (R : OmegaWeightSource (k := k) (K := K) (ZMod 3))
  (b : LiteralPrimitiveBlock k G3)

/-- The prescribed raw representative retains the block of its matched class. -/
theorem decoded_raw_block
    (omega : BrauerFibre root b ≃ CoverWeight R b)
    (Q : RadicalSubgroup (p := 2) (G := G3))
    (phi : BrauerAtRadical omega Q) :
    R.operations.rawWeightBlock
      (characterWeightAt Nat.prime_two Q (localMap omega Q phi).val) = b := by
  change R.weightBlock (TypeBQ3PrincipalWeightInflation.classOf
    (characterWeightAt Nat.prime_two Q (localMap omega Q phi).val)) = b
  exact (congrArg R.weightBlock (localMap_class omega Q phi)).trans
    (omega phi.val).property

/-- Decode the same derived matching and apply the actual Q=1 construction
to every prescribed local representative. The complete base catalogue is
the one already stored by R; no separate base-block source is introduced. -/
theorem of_derived_matching
    (matrixSource : MatrixExceptionalSource)
    (automorphisms : TypeBQ3TripleCoverAutomorphisms.MatrixAutomorphismSource)
    (indexTwo : (G (ZMod 3)).index = 2)
    (omega : BrauerFibre root b ≃ CoverWeight R b)
    (graph : ∀ (alpha : (MulAut G3)ᵐᵒᵖ) (phi psi : BrauerFibre root b),
      psi.val = alpha • phi.val → (omega psi).val = alpha • (omega phi).val)
    (radicalTrivial : ∀ U : CharacterWeight 2 K G3,
      R.operations.rawWeightBlock U = b → U.subgroup = ⊥)
    (localAnchor : ∀ (phi : BrauerFibre root b) (U : CharacterWeight 2 K G3),
      R.operations.rawWeightBlock U = b →
      ∀ n : PrimeRegularElement (G := Subgroup.normalizer (U.subgroup : Set G3)) 2,
        phi.val.val (PrimeRegularElement.map
          (Subgroup.normalizer (U.subgroup : Set G3)).subtype n) =
        U.localCharacter (QuotientGroup.mk n.val))
    (ambientBlocks : ∀ phi : BrauerFibre root b,
      PhysicalBlocks k (ActualAutAmbient root phi.val))
    (principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} 2 k)
    (ambientSeed : ∀ phi : BrauerFibre root b,
      PrimeRegularRootEmbedding 2 k K (ActualAutAmbient root phi.val))
    (fieldSource : SpathCoefficientField 2 k Nat.prime_two) :
    CompleteClauses root R b omega := by
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
    let U := characterWeightAt Nat.prime_two Q (localMap omega Q phi).val
    have supported : R.operations.rawWeightBlock U = b :=
      decoded_raw_block root R b omega Q phi
    exact TypeBQ3B45QOneExtension.exists_actual_qOne_clauseIII
      matrixSource automorphisms indexTwo root phi.val.val U
      (radicalTrivial U supported) (localAnchor phi.val U supported)
      R.operations.ambientBlockData (ambientBlocks phi.val)
      principle (ambientSeed phi.val) fieldSource

/-- The selected defect-zero source constructs the complete matching and
all raw value anchors before the Q=1 criterion is combined. No matching,
graph, radical map, local equivalence or extension packet is a source field. -/
theorem of_fixedBlockSource
    (matrixSource : MatrixExceptionalSource)
    (automorphisms : TypeBQ3TripleCoverAutomorphisms.MatrixAutomorphismSource)
    (indexTwo : (G (ZMod 3)).index = 2)
    (reference : IBr root)
    (source : TypeBQ3B45DefectZeroMatching.FixedBlockSource
      root R matrixSource b reference)
    (ambientBlocks : ∀ phi : BrauerFibre root b,
      PhysicalBlocks k (ActualAutAmbient root phi.val))
    (principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} 2 k)
    (ambientSeed : ∀ phi : BrauerFibre root b,
      PrimeRegularRootEmbedding 2 k K (ActualAutAmbient root phi.val))
    (fieldSource : SpathCoefficientField 2 k Nat.prime_two) :
    CompleteClauses root R b (TypeBQ3B45DefectZeroMatching.fixedBlockEquiv source) := by
  refine of_derived_matching root R b matrixSource automorphisms indexTwo
    (TypeBQ3B45DefectZeroMatching.fixedBlockEquiv source)
    (TypeBQ3B45DefectZeroMatching.fixedBlockEquiv_graph source)
    (fun U supported =>
      (TypeBQ3B45DefectZeroMatching.raw_local_anchor source U supported).1)
    ?_ ambientBlocks principle ambientSeed fieldSource
  intro phi U supported n
  have same : phi.val = reference := source.unique phi.val phi.property
  rw [same]
  exact (TypeBQ3B45DefectZeroMatching.raw_local_anchor source U supported).2 n

end ModularRep.PaperProofs.TypeBQ3B45CriterionAssembly


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
