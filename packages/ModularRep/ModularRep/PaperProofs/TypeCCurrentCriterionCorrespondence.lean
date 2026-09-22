import ModularRep.PaperProofs.TypeCCurrentOrdinaryActions
import ModularRep.PaperProofs.TypeCCurrentProposition313
import ModularRep.PaperProofs.TypeBCriterionHypotheses

/-!
Current coefficient adapter: the original Conlon, block-fibre and orbit
proofs are retained with characteristic-zero simple labels and their checked
tensor/field action, without ordinary algebraic closure.

# The computed Type C correspondence in the literal criterion domain

The published inputs below are precisely the existing Propositions 3.11 and 3.14
inputs, on the same normal subgroup, roots, primitive block catalogue and
ordinary-label carrier. The output is the actual `GlobalCorrespondence`
used by the universal Brough--Spath criterion. The correspondence is obtained
by invoking the protected source-instantiated Proposition 3.14 theorem.

No Brauer-to-label or Brauer-to-weight equivalence, combined equivariance,
criterion-hypothesis packet or final block condition is an input. The only
set correspondence in `SourceInputs` is Li's ordinary-label-to-weight map.
The exact E1/E2 interpretation of its predicates, basic set and separate
tensor/field formulas is retained by the source contract. The other three
criterion clauses and the literal Sp/CSp specialization remain separate.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeCCurrentCriterionCorrespondence

open ModularRep
open BlockFibreRestriction DecompositionBasicSetBridge ExactGrothendieckGroup
open FDRepSimpleClassKZero OrdinaryIrreducibleCharacter
open ConlonBasicSet TypeCConformalActionAdapter
open TypeCExactStabilizerLemma310Relative TypeCWeightTensorFieldAction
open TypeBCriterionHypotheses

variable {ell : ℕ} {K O k M E : Type}
variable [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
variable [CharZero K] [CharP k ell] [IsAlgClosed k]
variable [Group M] [Finite M] [Group E] [Finite E]

local instance : Fintype M := Fintype.ofFinite _

variable (G : Subgroup M) [G.Normal] (field : E →* MulAut M)
variable (hinvariant : FieldInvariantSubgroup.IsInvariant G field)
variable (D : OrdinaryReductionEquiv (k := k) (K := K) G field hinvariant)
variable [Fintype (LiteralPrimitiveBlock k M)]
variable [Fintype (LiteralPrimitiveBlock k G)]
variable [MulAction (ActingGroup (k := k) G field hinvariant)
  (LiteralPrimitiveBlock k M)]
variable (iotaM : PrimeRegularRootEmbedding ell k K M)
variable (hinjM : IrreducibleBrauerCharacterInjectivity iotaM)
variable (blocks : BlockData (ell := ell) (k := k) (K := K) G)
variable (productFormula : BrauerLinearTensorProductFormula iotaM)
variable (radicalKernel : RadicalKernelLiftInput (p := ell) G field hinvariant D)

/-- Existing published source inputs on the exact specified upstairs blocks.
The source contains no map from Brauer characters to ordinary labels or
weights, and no assumption about a downstairs matching. -/
structure SourceInputs where
  modularSystem : ModularSystem ell K O k
  reductionCompatible : StableReductionBrauerCharacterCompatibility
    modularSystem iotaM
  series : Irr K M → Prop
  [finiteSeries : Finite
    (TypeCCurrentProposition311.OrdinarySeriesCarrier series)]
  seriesTensorStable : OrdinarySeriesTensorStable G field hinvariant D series
  seriesFieldStable : OrdinarySeriesFieldStable (K := K) field series
  linearEquiv :
    MonoidAlgebra ℤ
        (TypeCCurrentProposition311.OrdinarySeriesCarrier series) ≃ₗ[ℤ]
      MonoidAlgebra ℤ (IBr iotaM)
  decomposition : ∀ v : MonoidAlgebra ℤ
      (TypeCCurrentProposition311.OrdinarySeriesCarrier series),
    labelledSimpleClassKZero (simpleModuleClassEquivIBr iotaM hinjM).symm
        (linearEquiv v) =
      decompositionMapOfStableReduction modularSystem iotaM reductionCompatible
        (labelledSimpleClassKZero
          (TypeBOrdinaryLabelSplitting.ordinarySeriesLabel
            (K := K) series) v)
  ordinaryBlock : Irr K M → LiteralPrimitiveBlock k M
  ordinaryBlockEquivariant : OrdinaryBlockEquivariant
    G field hinvariant D ordinaryBlock
  brauerBlockEquivariant : BrauerBlockEquivariant
    G field hinvariant iotaM productFormula
      (irreducibleBrauerCharacterBlock iotaM hinjM blocks.upstairs)
  blockDiagonal : BlockDiagonalLinearEquiv
    (TypeBSpecialCliffordActionAdapter.ordinarySeriesBlockMap series ordinaryBlock)
    (irreducibleBrauerCharacterBlock iotaM hinjM blocks.upstairs) linearEquiv
  liftReductionCompatible : TypeBSpecialCliffordActionAdapter.OrdinaryLiftReductionCompatible
    G field hinvariant D iotaM
  kernelCard : ∀ block : LiteralPrimitiveBlock k M, Nat.card
    (fieldProjection
      (LinearCharactersTrivialOn.fieldAction (k := k) field
        (FieldInvariantSubgroup.isFieldStable G field hinvariant))
      (MulAction.stabilizer
        (ActingGroup (k := k) G field hinvariant) block)).ker ≤ 2
  conlon : ∀ block : LiteralPrimitiveBlock k M,
    PadicConlonMarkDetection.{0, 0} (p := 2)
      (A := MulAction.stabilizer
        (ActingGroup (k := k) G field hinvariant) block)
  burnside : ∀ block : LiteralPrimitiveBlock k M,
    PublishedBurnsideMarkInjectivity.{0, 0}
      (A := MulAction.stabilizer
        (ActingGroup (k := k) G field hinvariant) block)
  labelToWeight : TypeCCurrentProposition311.OrdinarySeriesCarrier series ≃
    CharacterWeight.ConjugacyClass (p := ell) (K := K) (G := M)
  label_tensor : ∀ (lambda : TensorCharacters (k := k) G)
      (x : TypeCCurrentProposition311.OrdinarySeriesCarrier series),
    labelToWeight
        (TypeCCurrentProposition313.ordinaryTensorStep
          G field hinvariant D series seriesTensorStable lambda x) =
      TypeCWeightTensorFieldAction.CharacterWeight.linearTwistConjugacyClass
        (TypeCWeightTensorFieldAction.radicalLift
          G field hinvariant D radicalKernel lambda)⁻¹ (labelToWeight x)
  label_field : ∀ (e : E)
      (x : TypeCCurrentProposition311.OrdinarySeriesCarrier series),
    labelToWeight
        (TypeCCurrentProposition313.ordinaryFieldStep
          (K := K) field series seriesFieldStable e x) =
      CharacterWeight.rightTwistConjugacyClass (field e⁻¹) (labelToWeight x)
  label_block : ∀
      x : TypeCCurrentProposition311.OrdinarySeriesCarrier series,
    blocks.weightUpstairs.weightBlock (labelToWeight x) =
      TypeBSpecialCliffordActionAdapter.ordinarySeriesBlockMap series ordinaryBlock x

attribute [instance] SourceInputs.finiteSeries

variable [IsCyclic E] [Finite (TensorCharacters (k := k) G)]

/-- Construct the criterion's exact upstairs correspondence from the
existing source-instantiated theorem on those same primitive blocks. -/
def globalCorrespondence
    (S : SourceInputs (O := O) G field hinvariant D iotaM hinjM blocks
      productFormula radicalKernel) :
    GlobalCorrespondence G field iotaM blocks hinjM hinvariant D
      productFormula radicalKernel := by
  have hexists :=
    TypeCCurrentProposition313.proposition_3_13_condition_ii_source_instantiated
      G field hinvariant D S.modularSystem iotaM S.reductionCompatible hinjM
      productFormula S.series S.seriesTensorStable S.seriesFieldStable
      S.linearEquiv S.decomposition S.ordinaryBlock S.ordinaryBlockEquivariant
      blocks.upstairs S.brauerBlockEquivariant S.blockDiagonal
      S.liftReductionCompatible radicalKernel S.kernelCard S.conlon S.burnside
      blocks.weightUpstairs S.labelToWeight S.label_tensor S.label_field S.label_block
  exact ⟨Classical.choose hexists, (Classical.choose_spec hexists).1,
    (Classical.choose_spec hexists).2.1⟩

end ModularRep.PaperProofs.TypeCCurrentCriterionCorrespondence


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
