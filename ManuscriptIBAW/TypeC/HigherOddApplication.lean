import ManuscriptIBAW.TypeC.OddPrimeApplication
import ModularRep.PaperProofs.TypeCActualCaseSourceData

/-!
# The complete Type C application in higher rank at odd primes

The conformal correspondence and stabiliser arguments apply to the specified
family on the prime-to-ell cover of PSp. The assumptions concern the cited
ordinary character and weight results, the block operations and
Brough–Späth's criterion. The complete family is a conclusion.

The ordinary coefficient field splits the specified finite groups and is the
fraction field of the chosen modular system. It is not required to be
algebraically closed.
-/

noncomputable section
open scoped MonoidAlgebra
namespace ManuscriptIBAW.TypeC
open ModularRep ModularRep.PaperProofs FDRepSimpleClassKZero CharacterWeight
open TypeCActualCaseSourceData
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family
open TypeBFixedRootDefinitionFamily TypeBFullBlockCondition
open OddTwoConformalProjectiveRealisation (Sp PSp CSp spProjection)
open TypeCActualSimpleQuotientCoordinates
local instance higherOddFiniteFintype (G : Type) [Finite G] : Fintype G := Fintype.ofFinite G

section HigherOdd

open TypeBCriterionHypotheses TypeCConformalActionAdapter TypeCWeightTensorFieldAction
open TypeCOddPrimeConformalCriterionCarriers

variable (n ell : ℕ) (F : Type) [Field F] [Finite F]

/-- The data used in the proof at odd primes. The conformal block stabiliser
bound and the required subgroup index are derived from the multiplier and
linear character arguments. All coefficient fields, roots, blocks and
character actions are fixed before applying the criterion. -/
structure HigherOddInputs where
  [normal : (SpSubgroup n F).Normal]
  k : Type
  K : Type
  O : Type
  CyclicTarget : Type
  [fieldk : Field k]
  [fieldK : Field K]
  [ringO : CommRing O]
  [domainO : IsDomain O]
  [algebraOK : Algebra O K]
  [charPk : CharP k ell]
  [closedk : IsAlgClosed k]
  [charZeroK : CharZero K]
  [ordinaryRootsAmbient : HasEnoughRootsOfUnity K
    (Nat.card (Ambient (fieldAction n F)))]
  [groupCyclic : Group CyclicTarget]
  [cyclic : IsCyclic CyclicTarget]
  [finiteBlocksM : Fintype (LiteralPrimitiveBlock k (CSp n F))]
  [finiteBlocksG : Fintype (LiteralPrimitiveBlock k (SpSubgroup n F))]
  [finiteTensor : Finite (TensorCharacters (k := k) (SpSubgroup n F))]
  [actionM : MulAction
    (ActingGroup (k := k) (SpSubgroup n F) (fieldAction n F) (field_spSubgroup_map n F))
    (LiteralPrimitiveBlock k (CSp n F))]
  [actionG : MulAction (Ambient (fieldAction n F))
    (LiteralPrimitiveBlock k (SpSubgroup n F))]
  iotaM : PrimeRegularRootEmbedding ell k K (CSp n F)
  iotaG : PrimeRegularRootEmbedding ell k K (SpSubgroup n F)
  injectiveM : IrreducibleBrauerCharacterInjectivity iotaM
  injectiveG : IrreducibleBrauerCharacterInjectivity iotaG
  blocks : BlockData (ell := ell) (k := k) (K := K) (SpSubgroup n F)
  reduction : OrdinaryReductionEquiv (k := k) (K := K)
    (SpSubgroup n F) (fieldAction n F) (field_spSubgroup_map n F)
  productFormula : BrauerLinearTensorProductFormula iotaM
  radicalKernel : RadicalKernelLiftInput (p := ell)
    (SpSubgroup n F) (fieldAction n F) (field_spSubgroup_map n F) reduction
  other : OddPrimeApplication.SourceInputs n F
    (O := O) (CyclicTarget := CyclicTarget)
    iotaM iotaG injectiveM injectiveG blocks reduction productFormula radicalKernel
  criterion : TypeBFullCriterionSplittingSource.Theorem45SplittingCertificate

attribute [instance] HigherOddInputs.fieldk HigherOddInputs.fieldK HigherOddInputs.ringO
  HigherOddInputs.domainO HigherOddInputs.algebraOK HigherOddInputs.charPk
  HigherOddInputs.closedk HigherOddInputs.charZeroK HigherOddInputs.ordinaryRootsAmbient
  HigherOddInputs.groupCyclic HigherOddInputs.cyclic HigherOddInputs.finiteBlocksM
  HigherOddInputs.finiteBlocksG HigherOddInputs.finiteTensor

def HigherOddInputs.target (D : HigherOddInputs n ell F) : ActualTarget n ell F := by
  letI := D.normal
  letI := D.actionM
  letI := D.actionG
  exact
    { family := TypeBFixedRootCriterionFamilySplitting.downstairsFamily (SpSubgroup n F) D.iotaG D.blocks
        D.other.prime D.injectiveG D.other.localReduction
      cover := TypeCOddPrimeSymplecticCover.ellPrimeCover n F
        D.other.prime D.other.odd D.other.coverSource
      simpleEquiv := MulEquiv.refl _ }

theorem HigherOddInputs.complete (D : HigherOddInputs n ell F) :
    Nonempty (FamilyWitness D.target.family D.target.cover) := by
  let := D.normal
  let := D.actionM
  let := D.actionG
  exact OddPrimeApplication.full_block_condition_source_instantiated
    n F D.iotaM D.iotaG D.injectiveM D.injectiveG D.blocks D.reduction
    D.productFormula D.radicalKernel D.other D.criterion

@[simp] theorem HigherOddInputs.projection (D : HigherOddInputs n ell F) :
    D.target.projection = TypeCOddPrimeSymplecticCover.projection n F := rfl


end HigherOdd

end ManuscriptIBAW.TypeC

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
this package's formalisation report and source records.
-/
