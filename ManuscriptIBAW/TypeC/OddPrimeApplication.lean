import ManuscriptIBAW.TypeC.OddConformalCorrespondence
import ManuscriptIBAW.TypeC.OddLiteralBasicSet
import ManuscriptIBAW.TypeC.ConformalMultiplier
import ModularRep.PaperProofs.TypeCCurrentOddPrimeApplication

/-!
# Type C at odd primes with the derived stabiliser bound

The groups, roots, block operations and local characters are those of the
specified matrix Sp/CSp data. The assumptions give the multiplier geometry
and the module interpretation of tensoring. The two required indices follow
from that geometry.

The conformal correspondence is constructed from the general linear
character lemma, the basic set and the stated Li results. The rational ℓ′
series use the specified SO and GSpin dual groups. The proof constructs the
global bijection for the symplectic group and applies the Cabanes–Späth
argument directly.

The splitting field, local extension and common modular system hypotheses
remain explicit. The theorem is conditional on the displayed published
results.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ManuscriptIBAW.TypeC.OddPrimeApplication

open ModularRep ModularRep.PaperProofs FDRepSimpleClassKZero
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

structure SourceInputs where
  prime : Nat.Prime ell
  odd : Odd ell
  nondefining : ¬ ell ∣ Nat.card F
  coefficient : SpathCoefficientField ell k prime
  structuralSource : StructuralSource n F
  multiplier : ConformalMultiplierSource n F
  coverSource : TypeCOddPrimeSymplecticCover.CoverSource n F ell
  dividesSimpleOrder : ell ∣ Nat.card (PSp n F)
  localReduction : LocalReductionData (SpSubgroup n F) iotaG blocks
  ordinaryAndWeight : OddConformalCorrespondence.SourceInputs
    (O := O) (SpSubgroup n F) (fieldAction n F) (field_spSubgroup_map n F) D iotaM hinjM blocks productFormula radicalKernel
  upstairsSeries : OddRationalSeries.Conformal n F K
  upstairsSeries_eq : ordinaryAndWeight.series = upstairsSeries.ellPrime ell
  downstairsSeries : OddRationalSeries.Symplectic n F K
  basicSetData : OddLiteralBasicSet.SourceInputs n F
    (O := O) iotaG hinjG blocks.downstairs upstairsSeries downstairsSeries structuralSource
  blockInputs : ∀ b : LiteralPrimitiveBlock k (SpSubgroup n F),
    OddGlobalFactorization.BlockSourceInputs
      (SpSubgroup n F) (fieldAction n F) (naturalAction n F) iotaG hinjG blocks.downstairs
      (OddLiteralBasicSet.SourceInputs.toBasicSetSource n F iotaG hinjG blocks.downstairs
        upstairsSeries downstairsSeries structuralSource basicSetData)
      (CyclicTarget := CyclicTarget) b
  ordinarySeparation : OddGlobalFactorization.CabanesSpath31Certificate
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
  rootM : iotaM = TypeBModularGroupRootBinding.groupRoot
    ordinaryAndWeight.modularSystem (CSp n F)
  rootG : iotaG = TypeBModularGroupRootBinding.groupRoot
    ordinaryAndWeight.modularSystem (SpSubgroup n F)
  sameSystem : basicSetData.modularSystem = ordinaryAndWeight.modularSystem
  upstairsPhysical : TypeBFixedRootDefinitionFamily.GuardedBlockCompatibility
    iotaM blocks.weightUpstairs.operations
  li : TypeCCurrentOddPrimeLiSource.Li55SplittingCertificate

variable (inputs : SourceInputs n F (O := O)
  (CyclicTarget := CyclicTarget) iotaM iotaG hinjM hinjG blocks D
  productFormula radicalKernel)

/-- Construct the Conlon data for the symplectic group using the proved
stability of the rational union. -/
def SourceInputs.basicSet : OddGlobalFactorization.BasicSetSource
    (O := O) (SpSubgroup n F) (fieldAction n F) (naturalAction n F) iotaG hinjG blocks.downstairs :=
  OddLiteralBasicSet.SourceInputs.toBasicSetSource n F iotaG hinjG blocks.downstairs
    inputs.upstairsSeries inputs.downstairsSeries inputs.structuralSource inputs.basicSetData

omit [IsCyclic CyclicTarget] [Finite (TensorCharacters (k := k) (SpSubgroup n F))] in
/-- The ordinary predicate is the specified rational union by definition. -/
theorem SourceInputs.downstairsSeries_eq :
    inputs.basicSet.ordinary.predicate = inputs.downstairsSeries.ellPrime ell := rfl

/-- Construct the conformal source data from the specified tensor action and the
multiplier index calculation. -/
def correspondenceSource : TypeCCurrentCriterionCorrespondence.SourceInputs
    (O := O) (SpSubgroup n F) (fieldAction n F) (field_spSubgroup_map n F)
    D iotaM hinjM blocks productFormula radicalKernel :=
  OddConformalCorrespondence.retainedSource
    (SpSubgroup n F) (fieldAction n F) (field_spSubgroup_map n F)
    D iotaM hinjM blocks productFormula radicalKernel
    inputs.prime inputs.multiplier.index_le_two inputs.ordinaryAndWeight

omit [IsCyclic CyclicTarget] [Finite (TensorCharacters (k := k) (SpSubgroup n F))] in
include inputs in
/-- The same geometry shows that the index divides two. -/
theorem index_dvd_two :
    (SpSubgroup n F ⊔ Subgroup.center (CSp n F)).index ∣ 2 :=
  inputs.multiplier.index_dvd_two

/-- Construct the global bijection between ordinary and Brauer characters of the
symplectic group before applying ordinary character separation. -/
def downstairsBijection : OddGlobalFactorization.GlobalBijection
    (SpSubgroup n F) (fieldAction n F) (naturalAction n F) iotaG hinjG
    blocks.downstairs inputs.basicSet :=
  OddGlobalFactorization.globalBijection
    (SpSubgroup n F) (fieldAction n F) (naturalAction n F) iotaG hinjG
    blocks.downstairs inputs.basicSet inputs.blockInputs

omit [Finite (TensorCharacters (k := k) (SpSubgroup n F))] in
/-- The constructed beta is equivariant under all actual automorphisms
of Sp, including the specified field and diagonal automorphisms. -/
theorem downstairsBijection_automorphism_equivariant
    (alpha : MulAut (SpSubgroup n F)) (phi : IBr iotaG) :
    ((downstairsBijection n F iotaM iotaG hinjM hinjG blocks D
      productFormula radicalKernel inputs).beta
        (IrreducibleBrauerCharacter.twist iotaG phi alpha)).1 =
      OrdinaryIrreducibleCharacter.twist K (SpSubgroup n F)
        ((downstairsBijection n F iotaM iotaG hinjM hinjG blocks D
          productFormula radicalKernel inputs).beta phi).1 alpha :=
  OddGlobalFactorization.GlobalBijection.automorphism_equivariant
    (SpSubgroup n F) (fieldAction n F) (naturalAction n F) iotaG hinjG
    blocks.downstairs inputs.basicSet
    (downstairsBijection n F iotaM iotaG hinjM hinjG blocks D
      productFormula radicalKernel inputs)
    inputs.structuralSource.surjective alpha phi

/-- The target is the rational ℓ′ union on the specified special orthogonal dual
group, with the stated coefficient comparison. -/
def literalDownstairsBijection : IBr iotaG ≃
    {chi : OrdinaryIrreducibleCharacter.Irr K (SpSubgroup n F) //
      inputs.downstairsSeries.ellPrime ell chi} :=
  (downstairsBijection n F iotaM iotaG hinjM hinjG blocks D
    productFormula radicalKernel inputs).beta.trans
      (Equiv.subtypeEquivRight (fun chi => by rw [inputs.downstairsSeries_eq]))

omit [Finite (TensorCharacters (k := k) (SpSubgroup n F))] in
/-- Equivariance under all automorphisms of Sp on the specified rational series. -/
theorem literalDownstairsBijection_automorphism_equivariant
    (alpha : MulAut (SpSubgroup n F)) (phi : IBr iotaG) :
    (literalDownstairsBijection n F iotaM iotaG hinjM hinjG blocks D
      productFormula radicalKernel inputs
        (IrreducibleBrauerCharacter.twist iotaG phi alpha)).1 =
      OrdinaryIrreducibleCharacter.twist K (SpSubgroup n F)
        (literalDownstairsBijection n F iotaM iotaG hinjM hinjG blocks D
          productFormula radicalKernel inputs phi).1 alpha :=
  downstairsBijection_automorphism_equivariant n F iotaM iotaG hinjM hinjG
    blocks D productFormula radicalKernel inputs alpha phi

omit [Finite (TensorCharacters (k := k) (SpSubgroup n F))] in
/-- Block preservation holds for the same beta used in the criterion. -/
theorem downstairsBijection_block_preserving (phi : IBr iotaG) :
    inputs.basicSet.ordinary.blockOf
      ((downstairsBijection n F iotaM iotaG hinjM hinjG blocks D
        productFormula radicalKernel inputs).beta phi) =
      irreducibleBrauerCharacterBlock iotaG hinjG blocks.downstairs phi :=
  (downstairsBijection n F iotaM iotaG hinjM hinjG blocks D
    productFormula radicalKernel inputs).block_preserving phi

/-- Construct all criterion hypotheses, including the computed conformal
correspondence, on the same actual Sp/CSp datum. -/
def hypotheses : AllBlocksHypotheses
    (SpSubgroup n F) (fieldAction n F) (naturalAction n F) iotaM iotaG blocks
    hinjM (field_spSubgroup_map n F) D productFormula radicalKernel := by
  letI := inputs.structuralSource.field_cyclic
  let beta := downstairsBijection n F iotaM iotaG hinjM hinjG blocks D
    productFormula radicalKernel inputs
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
    liftCompatible := inputs.ordinaryAndWeight.liftReductionCompatible
    lift_primeTo := inputs.liftPrimeTo
    lift_trivial := inputs.liftTrivial
    extensions := TypeCCurrentOddPrimeLiSource.extensionClauses n F iotaG
      inputs.structuralSource inputs.brauerExtension inputs.ordinaryM inputs.ordinaryGE
    correspondence := OddConformalCorrespondence.globalCorrespondence
      (SpSubgroup n F) (fieldAction n F) (field_spSubgroup_map n F)
      D iotaM hinjM blocks productFormula radicalKernel inputs.prime
      inputs.multiplier.index_le_two inputs.ordinaryAndWeight
    hall := inputs.hall
    JG := TypeCCurrentInertiaHall.allPairsJG n F iotaG inputs.odd
      inputs.multiplier.index_dvd_two inputs.structuralSource.quotient_cyclic inputs.hall
    constituent := by
      intro Phi
      obtain ⟨phi, hphi⟩ := TypeCCurrentConstituentFactorization.exists_constituent
        (SpSubgroup n F) iotaM iotaG inputs.restriction Phi
      exact ⟨phi, hphi, OddGlobalFactorization.GlobalBijection.allBrauerFactorization
        (SpSubgroup n F) (fieldAction n F) (naturalAction n F) iotaG hinjG
        blocks.downstairs inputs.basicSet beta
        (OddGlobalFactorization.ordinarySeparation n F inputs.ordinarySeparation
          inputs.structuralSource inputs.downstairsSeries) phi⟩
    rawNormalizer := TypeCCurrentOddPrimeLiSource.rawNormalizerClause n F inputs.li
      inputs.structuralSource inputs.prime inputs.odd inputs.nondefining }

/-- Apply the published criterion on the specified target after deriving both index
facts. The target family retains exactly the original roots and blocks. -/
theorem full_block_condition_source_instantiated
    (criterion : TypeBFullCriterionSplittingSource.Theorem45SplittingCertificate) :
    Nonempty (TypeBFullBlockCondition.FamilyWitness
      (TypeBFixedRootCriterionFamilySplitting.downstairsFamily
        (SpSubgroup n F) iotaG blocks inputs.prime hinjG inputs.localReduction)
      (TypeCOddPrimeSymplecticCover.ellPrimeCover n F
        inputs.prime inputs.odd inputs.coverSource)) := by
  let : HasEnoughRootsOfUnity K (Nat.card (CSp n F)) :=
    HasEnoughRootsOfUnity.of_dvd K (show Nat.card (CSp n F) ∣
        Nat.card (Ambient (fieldAction n F)) from by
      rw [SemidirectProduct.card]
      exact dvd_mul_right _ _)
  obtain ⟨witness⟩ := criterion.allBlocks inputs.ordinaryAndWeight.modularSystem
    (SpSubgroup n F) (fieldAction n F) (naturalAction n F) iotaM iotaG
    inputs.rootM inputs.rootG blocks inputs.upstairsPhysical hinjM (field_spSubgroup_map n F)
    D productFormula radicalKernel
    (hypotheses n F iotaM iotaG hinjM hinjG blocks D productFormula radicalKernel inputs)
  exact ⟨TypeBFullCriterionSplittingSource.NormalizedFamilyWitness.full
    (familyAlgebra := (show Algebra O K from inferInstance)) witness⟩

end ManuscriptIBAW.TypeC.OddPrimeApplication

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
`docs/manuals/formalisation-companion.tex` and `audit/current/source-crosswalk.json`.
-/
