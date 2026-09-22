import ManuscriptIBAW.Library.TensorStabilizer
import ModularRep.PaperProofs.TypeCCurrentCriterionCorrespondence

/-!
# The conformal correspondence at odd primes

The specified data consist of ordinary labels, the decomposition map, block
operations, ordinary lifts and the separate Li actions. The block stabiliser
bound follows from the general central character lemma and the geometric
quotient index. It is not assumed.

Tensoring uses the reciprocal of the specified modular linear character, in
agreement with the inverse tensor convention of the action. No matching from
Brauer characters to ordinary labels or weights is assumed.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ManuscriptIBAW.TypeC.OddConformalCorrespondence

open ModularRep ModularRep.PaperProofs
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

/-- The actual modular inclusion of the quotient characters with the reciprocal
required by the specified tensor action convention. -/
def reciprocalLinear : TensorCharacters (k := k) G →* (M →* kˣ) where
  toFun c := c.1⁻¹
  map_one' := by
    apply MonoidHom.ext
    intro g
    change (1 : kˣ)⁻¹ = 1
    exact inv_one
  map_mul' := by
    intro c d
    apply MonoidHom.ext
    intro g
    change (c.1 g * d.1 g)⁻¹ = (c.1 g)⁻¹ * (d.1 g)⁻¹
    rw [mul_inv_rev, mul_comm]

theorem reciprocalLinear_injective :
    Function.Injective (reciprocalLinear (k := k) G) := by
  intro c d h
  apply Subtype.ext
  exact inv_injective h

theorem reciprocalLinear_trivial (c : TensorCharacters (k := k) G) :
    G ≤ (reciprocalLinear (k := k) G c).ker := by
  intro g hg
  change (c.1 g)⁻¹ = 1
  rw [c.2 hg, inv_one]

/-- The published and coefficient assumptions on the specified groups and
character sets. An application must identify the series predicate with the
rational ℓ′ union. -/
structure SourceInputs where
  tensor :
    let _ := tensorBlockAction (B := LiteralPrimitiveBlock k M)
      (LinearCharactersTrivialOn.fieldAction (k := k) field
        (FieldInvariantSubgroup.isFieldStable G field hinvariant))
    LinearBlockStabilizer.SimpleBlockTensorSource (reciprocalLinear (k := k) G)
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

variable [Finite (TensorCharacters (k := k) G)]

/-- Lemma 3.10: the general tensor stabiliser deduction on the same primitive
block and exact field/tensor action. -/
theorem kernelCard
    (prime : ell.Prime)
    (index : Nat.card (M ⧸ (G ⊔ Subgroup.center M)) ≤ 2)
    (S : SourceInputs (O := O) G field hinvariant D iotaM hinjM blocks
      productFormula radicalKernel)
    (block : LiteralPrimitiveBlock k M) :
    Nat.card
      (fieldProjection
        (LinearCharactersTrivialOn.fieldAction (k := k) field
          (FieldInvariantSubgroup.isFieldStable G field hinvariant))
        (MulAction.stabilizer (ActingGroup (k := k) G field hinvariant) block)).ker ≤ 2 := by
  exact (tensor_field_kernel_bound
    (LinearCharactersTrivialOn.fieldAction (k := k) field
      (FieldInvariantSubgroup.isFieldStable G field hinvariant))
    prime G (reciprocalLinear (k := k) G) (reciprocalLinear_injective G)
    (reciprocalLinear_trivial G) S.tensor block).trans index

/-- Construct the source data required by the correspondence theorem, using the
stabiliser bound proved above. -/
def retainedSource
    (prime : ell.Prime)
    (index : Nat.card (M ⧸ (G ⊔ Subgroup.center M)) ≤ 2)
    (S : SourceInputs (O := O) G field hinvariant D iotaM hinjM blocks
      productFormula radicalKernel) :
    TypeCCurrentCriterionCorrespondence.SourceInputs (O := O)
      G field hinvariant D iotaM hinjM blocks productFormula radicalKernel where
  modularSystem := S.modularSystem
  reductionCompatible := S.reductionCompatible
  series := S.series
  finiteSeries := S.finiteSeries
  seriesTensorStable := S.seriesTensorStable
  seriesFieldStable := S.seriesFieldStable
  linearEquiv := S.linearEquiv
  decomposition := S.decomposition
  ordinaryBlock := S.ordinaryBlock
  ordinaryBlockEquivariant := S.ordinaryBlockEquivariant
  brauerBlockEquivariant := S.brauerBlockEquivariant
  blockDiagonal := S.blockDiagonal
  liftReductionCompatible := S.liftReductionCompatible
  conlon := S.conlon
  burnside := S.burnside
  labelToWeight := S.labelToWeight
  label_tensor := S.label_tensor
  label_field := S.label_field
  label_block := S.label_block
  kernelCard := kernelCard G field hinvariant D iotaM hinjM blocks
    productFormula radicalKernel prime index S

variable [IsCyclic E]

/-- The correspondence follows using the derived linear character stabiliser
bound on every block. -/
def globalCorrespondence
    (prime : ell.Prime)
    (index : Nat.card (M ⧸ (G ⊔ Subgroup.center M)) ≤ 2)
    (S : SourceInputs (O := O) G field hinvariant D iotaM hinjM blocks
      productFormula radicalKernel) :
    GlobalCorrespondence G field iotaM blocks hinjM hinvariant D
      productFormula radicalKernel :=
  TypeCCurrentCriterionCorrespondence.globalCorrespondence
    G field hinvariant D iotaM hinjM blocks productFormula radicalKernel
    (retainedSource G field hinvariant D iotaM hinjM blocks
      productFormula radicalKernel prime index S)

end ManuscriptIBAW.TypeC.OddConformalCorrespondence

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
`docs/manuals/formalisation-companion.tex` and `audit/current/source-crosswalk.json`.
-/
