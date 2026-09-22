import ModularRep.PaperProofs.TypeBQ3B2CriterionAssembly
import ModularRep.PaperProofs.TypeBQ3FaithfulLocalReduction

/-!
The same calibrated Navarro source constructs the selected local reductions.
The specified block guard identifies their normalizer blocks, so neither a
reduction family nor a second compatibility assertion remains in the output.
The specified extension sources are scoped to the representatives already
selected from the unchanged matching.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBQ3B2CriterionFinish

open ModularRep CharacterWeight
open TypeBQ3TripleCoverCarrier TypeBRankThreePrincipalCountBinding
open TypeBCentralKernelBlockSource TypeBCentralKernelInertia
open TypeBCentralKernelTripleCertificate (PhysicalBlocks)
open TypeBQ3PrincipalWeightInflation
open TypeBQ3PrincipalPairBlockChoice
open TypeBQ3B2CriterionAssembly
open TypeBFixedRootDefinitionFamily TypeBLocalReductionInstantiation
open TypeBQ3FaithfulLocalReduction
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
  (R : OmegaWeightSource (k := k) (K := K) (ZMod 3))
  (b : LiteralPrimitiveBlock k G3)

/-- The full criterion conclusion with only its scoped specified extension inputs. -/
def PhysicalExtensionConclusion
    (omega : BrauerFibre root b ≃ CoverWeight R b) : Prop :=
  ∃ selected : (phi : BrauerFibre root b) →
      {W : CharacterWeight 2 K G3 // R.operations.rawWeightBlock W = b},
    (∀ phi, TypeBQ3PrincipalWeightInflation.classOf (selected phi).val = (omega phi).val) ∧
    ∀ (ambientBlocks : ∀ phi : BrauerFibre root b,
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
      CompleteClauses root R b omega

/-- Construct the reductions and their specified block equalities before
applying the complete fixed-block construction to the same matching. -/
theorem of_matching
    (matrixSource : MatrixExceptionalSource)
    (automorphisms : TypeBQ3TripleCoverAutomorphisms.MatrixAutomorphismSource)
    (indexTwo : (G (ZMod 3)).index = 2)
    {O : Type} [CommRing O] [IsDomain O] [Algebra O K]
    (Msys : ModularSystem 2 K O k)
    (calibration : RootResidueCompatible Msys root)
    [ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card G3)]
    (navarro : ∀ W : CharacterWeight 2 K G3,
      letI := localOrdinaryRoots (K := K) W.subgroup
      ScopedDefectZeroReductionSource Msys (localQuotientRoot root W.subgroup)
        (localRoot_residueCanonical Msys root calibration W.subgroup))
    (physical : GuardedBlockCompatibility root R.operations)
    (literalAt : R.operations.ambientBlockData.blockIdempotent b = b.val)
    (omega : BrauerFibre root b ≃ CoverWeight R b)
    (graph : ∀ (alpha : (MulAut G3)ᵐᵒᵖ) (phi psi : BrauerFibre root b),
      psi.val = alpha • phi.val → (omega psi).val = alpha • (omega phi).val) :
    PhysicalExtensionConclusion root R b omega := by
  obtain ⟨selected, selectedClass, finish⟩ :=
    TypeBQ3B2CriterionAssembly.of_matching root R b matrixSource automorphisms
      indexTwo literalAt omega graph
  refine ⟨selected, selectedClass, ?_⟩
  intro ambientBlocks localBlocks principle ambientSeed fieldSource S9295 S96 S414
  let reductions : ∀ phi : BrauerFibre root b,
      CanonicalRawReduction root (selected phi).val :=
    fun phi => TypeBQ3FaithfulLocalReduction.of_scoped
      Msys root calibration (selected phi).val (navarro (selected phi).val)
  exact finish reductions
    (fun phi => normalizerBlock_of_guarded physical (selected phi).val (reductions phi))
    ambientBlocks localBlocks principle ambientSeed fieldSource S9295 S96 S414

end ModularRep.PaperProofs.TypeBQ3B2CriterionFinish


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
