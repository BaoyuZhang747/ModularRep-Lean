import ModularRep.CharacterWeightBlockAssignment
import ModularRep.PaperProofs.TypeBOddPrimesProposition44Relative
import ModularRep.PaperProofs.TypeBSpecialCliffordActionAdapter
import ModularRep.PaperProofs.TypeCWeightTensorFieldAction

/-!
# Proposition 4.3 on the literal set of weights defined by characters

This file instantiates the orbit-construction deduction in Proposition 4.3 on
function-valued ordinary and Brauer characters and on conjugacy classes of
literal character weights.  The acting group is the semidirect product of
the modular linear characters of the special Clifford quotient with the
field group.  Its action on weights is constructed by descent to each local
normaliser quotient and by right automorphism transport.  The weight block
is the composite constructed by `CharacterWeight.LocalBlockInductionSource`.

The published Feng--Li--Zhang ordinary-label-to-weight equivalence remains
an exact E2 input, together with its separate tensor and field formulas and
its block compatibility.  Lean derives combined equivariance, invokes the
source-shaped Lemma 4.2 on one representative of each block orbit, transports
the resulting maps, and proves equivariance and block preservation of the
combined Brauer-to-weight equivalence.

No Brauer-to-weight equivalence, Brough--Sp\"ath criterion, inductive BAW
condition, or iBAW conclusion is an input.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBOddPrimesProposition44Actual

open ModularRep.BlockFibreRestriction
open ModularRep.DecompositionBasicSetBridge
open ModularRep.ExactGrothendieckGroup
open ModularRep.FDRepSimpleClassKZero
open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs.ConlonBasicSet
open ModularRep.PaperProofs.OddConlonOrbitAssembly
open ModularRep.PaperProofs.OddConformalProposition311Relative
open ModularRep.PaperProofs.TypeBConlonBlockRelative
open ModularRep.PaperProofs.TypeBOddPrimesProposition44Relative
open ModularRep.PaperProofs.TypeBSpecialCliffordActionAdapter
open ModularRep.PaperProofs.TypeCWeightTensorFieldAction

universe u

variable {p : Nat}
variable {K O k M E Block CyclicTarget ScalarField Semisimple : Type u}
variable [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
variable [CharZero K] [IsAlgClosed K] [CharP k p] [IsAlgClosed k]
variable [Group M] [Fintype M] [Group E]
variable [Group CyclicTarget] [IsCyclic CyclicTarget]
variable [Field ScalarField]

abbrev OrdinarySeriesCarrier (series : Irr K M → Prop) :=
  TypeBSpecialCliffordActionAdapter.OrdinarySeriesCarrier series

abbrev WeightClass :=
  CharacterWeight.ConjugacyClass (p := p) (K := K) (G := M)

/-- Tensor an ordinary label by the inverse lift of one quotient character.
This is the tensor part of the manuscript's right action. -/
def ordinaryTensorStep
    (G0 : Subgroup M) [G0.Normal]
    (field : E →* MulAut M)
    (hinvariant : TypeCConformalActionAdapter.FieldInvariantSubgroup.IsInvariant
      G0 field)
    (D : OrdinaryReductionEquiv (k := k) (K := K)
      G0 field hinvariant)
    (series : Irr K M → Prop)
    (seriesTensorStable : TypeCConformalActionAdapter.OrdinarySeriesTensorStable
      G0 field hinvariant D series)
    (lambda : TensorCharacters (k := k) G0)
    (x : OrdinarySeriesCarrier series) :
    OrdinarySeriesCarrier series :=
  ⟨OrdinaryIrreducibleCharacter.linearTwist x.1
      (TypeCConformalActionAdapter.OrdinaryReductionEquiv.lift
        (G0 := G0) (field := field) (hinvariant := hinvariant) D lambda)⁻¹,
    seriesTensorStable lambda x.1 x.2⟩

/-- Apply the inverse field automorphism to one ordinary label. -/
def ordinaryFieldStep
    (field : E →* MulAut M)
    (series : Irr K M → Prop)
    (seriesFieldStable : TypeCConformalActionAdapter.OrdinarySeriesFieldStable
      (K := K) field series)
    (e : E) (x : OrdinarySeriesCarrier series) :
    OrdinarySeriesCarrier series :=
  ⟨OrdinaryIrreducibleCharacter.twist K M x.1 (field e⁻¹),
    seriesFieldStable e x.1 x.2⟩

/-- The weight action used in Proposition 4.3 is the literal local tensor
action followed by right transport through the inverse field automorphism. -/
@[instance_reducible]
def weightAction
    (G0 : Subgroup M) [G0.Normal]
    (field : E →* MulAut M)
    (hinvariant : TypeCConformalActionAdapter.FieldInvariantSubgroup.IsInvariant
      G0 field)
    (D : OrdinaryReductionEquiv (k := k) (K := K)
      G0 field hinvariant)
    (radicalKernel : RadicalKernelLiftInput
      (p := p) G0 field hinvariant D) :
    MulAction (ActingGroup (k := k) G0 field hinvariant)
      (WeightClass (p := p) (K := K) (M := M)) :=
  TypeCWeightTensorFieldAction.tensorFieldSemidirectAction
    G0 field hinvariant D radicalKernel

/-- Separate tensor and field formulas for the published ordinary-label map
imply equivariance for the constructed semidirect actions. -/
theorem labelToWeight_combined_equivariant
    (G0 : Subgroup M) [G0.Normal]
    (field : E →* MulAut M)
    (hinvariant : TypeCConformalActionAdapter.FieldInvariantSubgroup.IsInvariant
      G0 field)
    (D : OrdinaryReductionEquiv (k := k) (K := K)
      G0 field hinvariant)
    (series : Irr K M → Prop)
    (seriesTensorStable : TypeCConformalActionAdapter.OrdinarySeriesTensorStable
      G0 field hinvariant D series)
    (seriesFieldStable : TypeCConformalActionAdapter.OrdinarySeriesFieldStable
      (K := K) field series)
    (radicalKernel : RadicalKernelLiftInput
      (p := p) G0 field hinvariant D)
    (rho : OrdinarySeriesCarrier series ≃
      WeightClass (p := p) (K := K) (M := M))
    (rho_tensor : ∀ (lambda : TensorCharacters (k := k) G0)
        (x : OrdinarySeriesCarrier series),
      rho (ordinaryTensorStep G0 field hinvariant D series
        seriesTensorStable lambda x) =
        CharacterWeight.linearTwistConjugacyClass
          (radicalLift G0 field hinvariant D radicalKernel lambda)⁻¹ (rho x))
    (rho_field : ∀ (e : E) (x : OrdinarySeriesCarrier series),
      rho (ordinaryFieldStep (K := K) field series seriesFieldStable e x) =
        CharacterWeight.rightTwistConjugacyClass (field e⁻¹) (rho x)) :
    let A := ActingGroup (k := k) G0 field hinvariant
    let hseries := TypeCConformalActionAdapter.ordinarySeriesStable_of_tensor_and_field
      G0 field hinvariant D series seriesTensorStable seriesFieldStable
    let _ : MulAction A (OrdinarySeriesCarrier series) :=
      ordinarySeriesCarrierAction G0 field hinvariant D series hseries
    let _ : MulAction A (WeightClass (p := p) (K := K) (M := M)) :=
      weightAction G0 field hinvariant D radicalKernel
    ∀ (a : A) (x : OrdinarySeriesCarrier series),
      rho (a • x) = a • rho x := by
  dsimp only
  let hseries := TypeCConformalActionAdapter.ordinarySeriesStable_of_tensor_and_field
    G0 field hinvariant D series seriesTensorStable seriesFieldStable
  letI ordinaryAction : MulAction
      (ActingGroup (k := k) G0 field hinvariant)
      (OrdinarySeriesCarrier series) :=
    ordinarySeriesCarrierAction G0 field hinvariant D series hseries
  letI actualWeightAction : MulAction
      (ActingGroup (k := k) G0 field hinvariant)
      (WeightClass (p := p) (K := K) (M := M)) :=
    weightAction G0 field hinvariant D radicalKernel
  intro a x
  let fieldX := ordinaryFieldStep (K := K)
    field series seriesFieldStable a.right x
  let tensorFieldX := ordinaryTensorStep G0 field hinvariant D series
    seriesTensorStable a.left fieldX
  have hsource : a • x = tensorFieldX := by
    apply Subtype.ext
    rfl
  calc
    rho (a • x) = rho tensorFieldX := congrArg rho hsource
    _ = CharacterWeight.linearTwistConjugacyClass
          (radicalLift G0 field hinvariant D radicalKernel a.left)⁻¹
          (rho fieldX) := rho_tensor a.left fieldX
    _ = CharacterWeight.linearTwistConjugacyClass
          (radicalLift G0 field hinvariant D radicalKernel a.left)⁻¹
          (CharacterWeight.rightTwistConjugacyClass
            (field a.right⁻¹) (rho x)) := by rw [rho_field a.right x]
    _ = a • rho x :=
      (TypeCWeightTensorFieldAction.tensorFieldSemidirectAction_apply
        G0 field hinvariant D radicalKernel a (rho x)).symm

/-- The global-bijection part of Proposition 4.3 on the literal weight
carrier.  The output is constructed from Lemma 4.2 and the published
ordinary-label correspondence; it is not present among the hypotheses. -/
theorem proposition_4_4_global_weight_equiv_actual
    (G0 : Subgroup M) [G0.Normal]
    (field : E →* MulAut M)
    (hinvariant : TypeCConformalActionAdapter.FieldInvariantSubgroup.IsInvariant
      G0 field)
    (D : OrdinaryReductionEquiv (k := k) (K := K)
      G0 field hinvariant)
    [Finite E] [IsCyclic E]
    [Finite (TensorCharacters (k := k) G0)]
    [Finite (ActingGroup (k := k) G0 field hinvariant)]
    [MulAction (ActingGroup (k := k) G0 field hinvariant) Block]
    [MulAction (MulAut M)ᵐᵒᵖ Block]
    (Msys : ModularSystem p K O k)
    (iota : PrimeRegularRootEmbedding p k K M)
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (productFormula : BrauerLinearTensorProductFormula iota)
    (series : Irr K M → Prop)
    [Finite (OrdinarySeriesCarrier series)]
    (seriesTensorStable : TypeCConformalActionAdapter.OrdinarySeriesTensorStable
      G0 field hinvariant D series)
    (seriesFieldStable : TypeCConformalActionAdapter.OrdinarySeriesFieldStable
      (K := K) field series)
    (linearEquiv :
      MonoidAlgebra ℤ (OrdinarySeriesCarrier series) ≃ₗ[ℤ]
        MonoidAlgebra ℤ (IBr iota))
    (hdecomposition : ∀ v : MonoidAlgebra ℤ
        (OrdinarySeriesCarrier series),
      labelledSimpleClassKZero (simpleModuleClassEquivIBr iota hinj).symm
          (linearEquiv v) =
        decompositionMapOfStableReduction Msys iota hcompat
          (labelledSimpleClassKZero
            (ordinarySeriesLabel (K := K) series) v))
    (ordinaryBlock : Irr K M → Block)
    (ordinaryBlockEquivariant : TypeCConformalActionAdapter.OrdinaryBlockEquivariant
      G0 field hinvariant D ordinaryBlock)
    [Fintype Block]
    {blockIdempotent : Block → k[M]}
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (brauerBlockEquivariant : TypeCConformalActionAdapter.BrauerBlockEquivariant
      G0 field hinvariant iota productFormula
        (irreducibleBrauerCharacterBlock iota hinj blocks))
    (hblockDiagonal : BlockDiagonalLinearEquiv
      (ordinarySeriesBlockMap series ordinaryBlock)
      (irreducibleBrauerCharacterBlock iota hinj blocks)
      linearEquiv)
    (liftReductionCompatible : OrdinaryLiftReductionCompatible
      G0 field hinvariant D iota)
    (radicalKernel : RadicalKernelLiftInput
      (p := p) G0 field hinvariant D)
    (fieldProjection : ∀ omega : BlockOrbit
        (ActingGroup (k := k) G0 field hinvariant) Block,
      MulAction.stabilizer
        (ActingGroup (k := k) G0 field hinvariant)
        (orbitRepresentative omega) →* CyclicTarget)
    (scalar : ∀ omega : BlockOrbit
        (ActingGroup (k := k) G0 field hinvariant) Block,
      (fieldProjection omega).ker → ScalarFieldˣ)
    (scalarInjective : ∀ omega : BlockOrbit
        (ActingGroup (k := k) G0 field hinvariant) Block,
      Function.Injective (scalar omega))
    (parameter : BlockOrbit
      (ActingGroup (k := k) G0 field hinvariant) Block → Semisimple)
    (translate : ScalarFieldˣ → Semisimple → Semisimple)
    (multiplier : Semisimple → ScalarFieldˣ)
    (IsConjugate : Semisimple → Semisimple → Prop)
    (multiplierEqOfConjugate : ∀ {s t : Semisimple},
      IsConjugate s t → multiplier s = multiplier t)
    (translatedConjugate : ∀
      (omega : BlockOrbit
        (ActingGroup (k := k) G0 field hinvariant) Block)
      (d : (fieldProjection omega).ker),
      IsConjugate (parameter omega)
        (translate (scalar omega d) (parameter omega)))
    (multiplierTranslate : ∀ (z : ScalarFieldˣ) (s : Semisimple),
      multiplier (translate z s) = z ^ 2 * multiplier s)
    (conlon : ∀ omega : BlockOrbit
        (ActingGroup (k := k) G0 field hinvariant) Block,
      PadicConlonMarkDetection.{u, u}
        (p := 2)
        (A := MulAction.stabilizer
          (ActingGroup (k := k) G0 field hinvariant)
          (orbitRepresentative omega)))
    (burnside : ∀ omega : BlockOrbit
        (ActingGroup (k := k) G0 field hinvariant) Block,
      PublishedBurnsideMarkInjectivity.{u, u}
        (A := MulAction.stabilizer
          (ActingGroup (k := k) G0 field hinvariant)
          (orbitRepresentative omega)))
    (blockSource : CharacterWeight.LocalBlockInductionSource
      (p := p) (k := k) (K := K) (G := M) (Block := Block))
    (rho : OrdinarySeriesCarrier series ≃
      WeightClass (p := p) (K := K) (M := M))
    (rho_tensor : ∀ (lambda : TensorCharacters (k := k) G0)
        (x : OrdinarySeriesCarrier series),
      rho (ordinaryTensorStep G0 field hinvariant D series
        seriesTensorStable lambda x) =
        CharacterWeight.linearTwistConjugacyClass
          (radicalLift G0 field hinvariant D radicalKernel lambda)⁻¹ (rho x))
    (rho_field : ∀ (e : E) (x : OrdinarySeriesCarrier series),
      rho (ordinaryFieldStep (K := K) field series seriesFieldStable e x) =
        CharacterWeight.rightTwistConjugacyClass (field e⁻¹) (rho x))
    (rho_block_preserving : ∀ x : OrdinarySeriesCarrier series,
      blockSource.weightBlock (rho x) =
        ordinarySeriesBlockMap series ordinaryBlock x) :
    let A := ActingGroup (k := k) G0 field hinvariant
    let Basic := OrdinarySeriesCarrier series
    let hseries := TypeCConformalActionAdapter.ordinarySeriesStable_of_tensor_and_field
      G0 field hinvariant D series seriesTensorStable seriesFieldStable
    let _ : MulAction A Basic :=
      ordinarySeriesCarrierAction G0 field hinvariant D series hseries
    let _ : MulAction A (IBr iota) :=
      brauerCharacterAction G0 field hinvariant iota productFormula
    let _ : MulAction A (WeightClass (p := p) (K := K) (M := M)) :=
      weightAction G0 field hinvariant D radicalKernel
    let brauerBlock := irreducibleBrauerCharacterBlock iota hinj blocks
    ∃ omega : IBr iota ≃ WeightClass (p := p) (K := K) (M := M),
      (∀ (a : A) (phi : IBr iota), omega (a • phi) = a • omega phi) ∧
      (∀ phi : IBr iota,
        blockSource.weightBlock (omega phi) = brauerBlock phi) ∧
      (∀ (a : A) (W : WeightClass (p := p) (K := K) (M := M)),
        blockSource.weightBlock (a • W) =
          a • blockSource.weightBlock W) := by
  dsimp only
  let A := ActingGroup (k := k) G0 field hinvariant
  let Basic := OrdinarySeriesCarrier series
  let ordinaryBlockOnSeries := ordinarySeriesBlockMap series ordinaryBlock
  let brauerBlock := irreducibleBrauerCharacterBlock iota hinj blocks
  have hseries : TypeCConformalActionAdapter.OrdinarySeriesStable
      G0 field hinvariant D series :=
    TypeCConformalActionAdapter.ordinarySeriesStable_of_tensor_and_field
      G0 field hinvariant D series seriesTensorStable seriesFieldStable
  letI ordinaryAction : MulAction A Basic :=
    ordinarySeriesCarrierAction G0 field hinvariant D series hseries
  letI brauerAction : MulAction A (IBr iota) :=
    brauerCharacterAction G0 field hinvariant iota productFormula
  letI actualWeightAction : MulAction A
      (WeightClass (p := p) (K := K) (M := M)) :=
    weightAction G0 field hinvariant D radicalKernel
  let basicSet := ordinarySeriesBasicSet Msys iota hcompat hinj series
    linearEquiv hdecomposition
  let ambientActions := labelledKZeroActionData
    G0 field hinvariant D Msys iota hcompat hinj productFormula
      series hseries linearEquiv hdecomposition
  have ambientNatural : DecompositionNatural
      (A := A) (decompositionMapOfStableReduction Msys iota hcompat)
      ambientActions.ordinaryAction ambientActions.modularAction :=
    decompositionNatural G0 field hinvariant D Msys iota hcompat
      productFormula liftReductionCompatible
  have hordinaryBlock : ∀ (a : A) (x : Basic),
      ordinaryBlockOnSeries (a • x) = a • ordinaryBlockOnSeries x := by
    intro a x
    exact ordinarySeriesBlockMap_equivariant
      G0 field hinvariant D series ordinaryBlock hseries
        ordinaryBlockEquivariant a x
  have hbrauerBlock : ∀ (a : A) (phi : IBr iota),
      brauerBlock (a • phi) = a • brauerBlock phi := by
    intro a phi
    exact brauerBlockEquivariant a phi
  have rhoEquivariant : ∀ (a : A) (x : Basic),
      rho (a • x) = a • rho x :=
    labelToWeight_combined_equivariant
      G0 field hinvariant D series seriesTensorStable seriesFieldStable
        radicalKernel rho rho_tensor rho_field
  have hweightBlock : ∀ (a : A)
      (W : WeightClass (p := p) (K := K) (M := M)),
      blockSource.weightBlock (a • W) =
        a • blockSource.weightBlock W := by
    intro a W
    obtain ⟨x, rfl⟩ := rho.surjective W
    calc
      blockSource.weightBlock (a • rho x) =
          blockSource.weightBlock (rho (a • x)) :=
        congrArg blockSource.weightBlock (rhoEquivariant a x).symm
      _ = ordinaryBlockOnSeries (a • x) := rho_block_preserving (a • x)
      _ = a • ordinaryBlockOnSeries x := hordinaryBlock a x
      _ = a • blockSource.weightBlock (rho x) :=
        congrArg (fun b : Block => a • b) (rho_block_preserving x).symm
  obtain ⟨omega, homegaEquivariant, homegaBlock⟩ :=
    exists_global_weight_equiv_of_lemma_4_3
      (p := p) (G := M) (k := k) (K := K)
      (Basic := Basic) (A := A) (BlockIndex := Block)
      (CyclicTarget := CyclicTarget) (ScalarField := ScalarField)
      (Semisimple := Semisimple)
      iota hinj blocks basicSet ordinaryBlockOnSeries hblockDiagonal
        ambientActions ambientNatural hordinaryBlock hbrauerBlock
        fieldProjection scalar scalarInjective parameter translate multiplier
        IsConjugate multiplierEqOfConjugate translatedConjugate
        multiplierTranslate conlon burnside blockSource.weightBlock rho
        rhoEquivariant rho_block_preserving
  exact ⟨omega, homegaEquivariant, homegaBlock, hweightBlock⟩

end ModularRep.PaperProofs.TypeBOddPrimesProposition44Actual


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
