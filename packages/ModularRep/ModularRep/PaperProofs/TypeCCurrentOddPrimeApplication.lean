import ModularRep.PaperProofs.TypeCCurrentOddPrimeLiSource
import ModularRep.PaperProofs.TypeCOddPrimeSymplecticCover
import ModularRep.PaperProofs.TypeCCurrentInertiaHall
import ModularRep.PaperProofs.TypeCCurrentConstituentFactorization
import ModularRep.PaperProofs.TypeCCurrentWeightStabilizerTransport
import ModularRep.PaperProofs.TypeCCurrentCriterionCorrespondence
import ModularRep.PaperProofs.TypeBFullCriterionSplittingSource

/-!
Current finite-splitting application: all original mathematical deductions
are retained. The basic-set and correspondence systems are the same actual
modular system; roots on both groups are its constructed roots. Ordinary
extensions use finite ambient roots and scoped cyclic sources.

# Actual odd-field, odd-prime Type C criterion application

All groups and actions below are the previously constructed matrix Sp range,
CSp, entrywise field action, and natural semidirect action. The input record
contains the exact source premises of the protected constituent, correspondence,
extension, Hall and raw-normalizer arguments. Their conclusions are computed;
none of the criterion's five resulting clauses is a new field.

The final endpoint applies the published universal certificate to its fixed
complete block-family output. Authentication of its literal source-to-output
interpretation, and transport to the independently selected Type C target,
remain separate obligations. This is not an unconditional Type C proposition.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeCCurrentOddPrimeApplication

open ModularRep FDRepSimpleClassKZero
open TypeBCriterionHypotheses TypeCConformalActionAdapter
open TypeCWeightTensorFieldAction
open TypeCOddPrimeConformalCriterionCarriers
open OddTwoConformalProjectiveRealisation (CSp PSp)
open EvenFieldFLZSourceConditions
open TypeBLocalOrdinaryExtensionSplitting TypeBLocalOrdinaryGeometry

variable (n : ℕ) (F : Type) [Field F] [Finite F]
variable [(SpSubgroup n F).Normal]
variable {ell : ℕ} {k K O CyclicTarget : Type}
variable [Field k] [Field K] [CommRing O] [IsDomain O] [Algebra O K]
variable [CharP k ell] [IsAlgClosed k] [CharZero K]
variable [Group CyclicTarget] [IsCyclic CyclicTarget]
variable [HasEnoughRootsOfUnity K (Nat.card (Ambient (fieldAction n F)))]


local instance ambientFintype : Fintype (CSp n F) := Fintype.ofFinite _
local instance baseFintype : Fintype (SpSubgroup n F) := Fintype.ofFinite _

variable [Fintype (LiteralPrimitiveBlock k (CSp n F))]
variable [Fintype (LiteralPrimitiveBlock k (SpSubgroup n F))]
variable [Finite (TensorCharacters (k := k) (SpSubgroup n F))]
variable [MulAction (ActingGroup (k := k) (SpSubgroup n F) (fieldAction n F) (field_spSubgroup_map n F))
  (LiteralPrimitiveBlock k (CSp n F))]
variable [MulAction (Ambient (fieldAction n F)) (LiteralPrimitiveBlock k (SpSubgroup n F))]
variable (iotaM : PrimeRegularRootEmbedding ell k K (CSp n F))
variable (iotaG : PrimeRegularRootEmbedding ell k K (SpSubgroup n F))
variable (hinjM : IrreducibleBrauerCharacterInjectivity iotaM)
variable (hinjG : IrreducibleBrauerCharacterInjectivity iotaG)
variable (blocks : BlockData (ell := ell) (k := k) (K := K) (SpSubgroup n F))
variable (D : OrdinaryReductionEquiv (k := k) (K := K) (SpSubgroup n F) (fieldAction n F) (field_spSubgroup_map n F))
variable (productFormula : BrauerLinearTensorProductFormula iotaM)
variable (radicalKernel : RadicalKernelLiftInput (p := ell) (SpSubgroup n F) (fieldAction n F) (field_spSubgroup_map n F) D)

/-- Source premises on fixed carriers. `standardRadicals` must receive Li's
actual product-basic family in its source interpretation; coverage is only
subgroup conjugacy and the standard formula concerns each weight's own pair.
The fixed nondefining odd-prime scope is retained even where a generic K
argument does not need all of it. -/
structure SourceInputs where
  prime : Nat.Prime ell
  odd : Odd ell
  nondefining : ¬ ell ∣ Nat.card F
  coefficient : SpathCoefficientField ell k prime
  structuralSource : StructuralSource n F
  coverSource : TypeCOddPrimeSymplecticCover.CoverSource n F ell
  dividesSimpleOrder : ell ∣ Nat.card (PSp n F)
  localReduction : LocalReductionData (SpSubgroup n F) iotaG blocks
  correspondenceSource : TypeCCurrentCriterionCorrespondence.SourceInputs
    (O := O) (SpSubgroup n F) (fieldAction n F) (field_spSubgroup_map n F) D iotaM hinjM blocks productFormula radicalKernel
  basicSet : TypeCCurrentConstituentFactorization.BasicSetSource
    (O := O) (SpSubgroup n F) (fieldAction n F) (naturalAction n F) iotaG hinjG blocks.downstairs
  blockInputs : ∀ b : LiteralPrimitiveBlock k (SpSubgroup n F),
    TypeCCurrentConstituentFactorization.BlockSourceInputs
      (SpSubgroup n F) (fieldAction n F) (naturalAction n F) iotaG hinjG blocks.downstairs basicSet
      (CyclicTarget := CyclicTarget) b
  restriction : TypeCCurrentConstituentFactorization.RestrictionExpansionSource
    (SpSubgroup n F) iotaM iotaG
  liftPrimeTo : ∀ lambda : TensorCharacters (k := k) (SpSubgroup n F),
    ell.Coprime (orderOf (OrdinaryReductionEquiv.lift
      (G0 := SpSubgroup n F) (field := fieldAction n F)
      (hinvariant := field_spSubgroup_map n F) D lambda))
  liftTrivial : ∀ lambda : TensorCharacters (k := k) (SpSubgroup n F),
    OrdinaryReductionEquiv.lift
      (G0 := SpSubgroup n F) (field := fieldAction n F)
      (hinvariant := field_spSubgroup_map n F) D lambda ∈
        linearCharactersTrivialOn (k := K) (SpSubgroup n F)
  brauerExtension : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} ell k
  ordinaryM : ∀ W : CharacterWeight ell K (SpSubgroup n F),
      letI := TypeBExtensionClausesSplitting.mRoots
        (SpSubgroup n F) (fieldAction n F) (naturalAction n F) W
      ScopedCyclicExtensionSource K
        (Inertia (SpSubgroup n F) (fieldAction n F) (naturalAction n F) W
          (embeddedM (fieldAction n F)) ⧸
        RadicalInInertia (SpSubgroup n F) (fieldAction n F) (naturalAction n F) W
          (embeddedM (fieldAction n F)))
  ordinaryGE : ∀ W : CharacterWeight ell K (SpSubgroup n F),
      letI := TypeBExtensionClausesSplitting.geRoots
        (SpSubgroup n F) (fieldAction n F) (naturalAction n F) W
      ScopedCyclicExtensionSource K
        (Inertia (SpSubgroup n F) (fieldAction n F) (naturalAction n F) W
          (baseFieldGroup (SpSubgroup n F) (fieldAction n F)) ⧸
        RadicalInInertia (SpSubgroup n F) (fieldAction n F) (naturalAction n F) W
          (baseFieldGroup (SpSubgroup n F) (fieldAction n F)))
  hall : HallData (SpSubgroup n F) ell
  index_dvd_two : ((SpSubgroup n F) ⊔ Subgroup.center (CSp n F)).index ∣ 2
  rootM : iotaM = TypeBModularGroupRootBinding.groupRoot
    correspondenceSource.modularSystem (CSp n F)
  rootG : iotaG = TypeBModularGroupRootBinding.groupRoot
    correspondenceSource.modularSystem (SpSubgroup n F)
  sameSystem : basicSet.modularSystem = correspondenceSource.modularSystem
  upstairsPhysical : TypeBFixedRootDefinitionFamily.GuardedBlockCompatibility
    iotaM blocks.weightUpstairs.operations
  li : TypeCCurrentOddPrimeLiSource.Li55SplittingCertificate

variable (inputs : SourceInputs n F (O := O)
  (CyclicTarget := CyclicTarget) iotaM iotaG hinjM hinjG blocks D
  productFormula radicalKernel)

/-- Join the already checked K arguments on the same actual Sp/CSp datum.
The extension principles are generic; no Type B structural fact is used. -/
def hypotheses : AllBlocksHypotheses (SpSubgroup n F) (fieldAction n F) (naturalAction n F) iotaM iotaG blocks
    hinjM (field_spSubgroup_map n F) D productFormula radicalKernel := by
  letI := inputs.structuralSource.field_cyclic
  exact {
    prime := inputs.prime
    coefficient := inputs.coefficient
    cover := TypeCOddPrimeSymplecticCover.ellPrimeCover n F
      inputs.prime inputs.odd inputs.coverSource
    divides_simple_order := inputs.dividesSimpleOrder
    structural := structural n F inputs.structuralSource
    rootAgreement := inputs.restriction.roots
    brauer_injective_downstairs := hinjG
    localReduction := inputs.localReduction
    liftCompatible := inputs.correspondenceSource.liftReductionCompatible
    lift_primeTo := inputs.liftPrimeTo
    lift_trivial := inputs.liftTrivial
    extensions := TypeCCurrentOddPrimeLiSource.extensionClauses n F iotaG
      inputs.structuralSource inputs.brauerExtension inputs.ordinaryM inputs.ordinaryGE
    correspondence := TypeCCurrentCriterionCorrespondence.globalCorrespondence
      (SpSubgroup n F) (fieldAction n F) (field_spSubgroup_map n F) D iotaM hinjM blocks productFormula radicalKernel
      inputs.correspondenceSource
    hall := inputs.hall
    JG := TypeCCurrentInertiaHall.allPairsJG n F iotaG inputs.odd
      inputs.index_dvd_two inputs.structuralSource.quotient_cyclic inputs.hall
    constituent := TypeCCurrentConstituentFactorization.constituentClause_of_lemma312
      (SpSubgroup n F) (fieldAction n F) (naturalAction n F) iotaM iotaG hinjG blocks.downstairs inputs.basicSet
      inputs.blockInputs inputs.restriction
    rawNormalizer := TypeCCurrentOddPrimeLiSource.rawNormalizerClause n F inputs.li
      inputs.structuralSource inputs.prime inputs.odd inputs.nondefining }

/-- Invoke the universal fixed-output source at this actual Type C input.
The target family uses the same downstairs blocks, roots and local reductions;
the cover is the same matrix projection to the pre-existing PSp quotient.
The external certificate's source interpretation is still an audit boundary. -/
theorem full_block_condition_source_instantiated
    (criterion : TypeBFullCriterionSplittingSource.Theorem45SplittingCertificate) :
    Nonempty (TypeBFullBlockCondition.FamilyWitness
      (TypeBFixedRootCriterionFamilySplitting.downstairsFamily (SpSubgroup n F) iotaG blocks inputs.prime hinjG inputs.localReduction)
      (TypeCOddPrimeSymplecticCover.ellPrimeCover n F
        inputs.prime inputs.odd inputs.coverSource)) := by
  letI : HasEnoughRootsOfUnity K (Nat.card (CSp n F)) :=
    HasEnoughRootsOfUnity.of_dvd K (by
      change Nat.card (CSp n F) ∣ Nat.card ((CSp n F) ⋊[fieldAction n F] (F ≃+* F))
      rw [SemidirectProduct.card]
      exact dvd_mul_right _ _)
  obtain ⟨witness⟩ := criterion.allBlocks inputs.correspondenceSource.modularSystem
    (SpSubgroup n F) (fieldAction n F) (naturalAction n F) iotaM iotaG
    inputs.rootM inputs.rootG blocks inputs.upstairsPhysical hinjM (field_spSubgroup_map n F)
    D productFormula radicalKernel
    (hypotheses n F iotaM iotaG hinjM hinjG blocks D productFormula radicalKernel inputs)
  exact ⟨TypeBFullCriterionSplittingSource.NormalizedFamilyWitness.full
    (familyAlgebra := (show Algebra O K from inferInstance)) witness⟩

end ModularRep.PaperProofs.TypeCCurrentOddPrimeApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
