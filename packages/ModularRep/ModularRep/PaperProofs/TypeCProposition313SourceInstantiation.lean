import ModularRep.PaperProofs.OddConlonOrbitAssembly
import ModularRep.PaperProofs.TypeCProposition311SourceInstantiation
import ModularRep.PaperProofs.TypeCWeightTensorFieldAction
import ModularRep.CharacterWeightBlockAssignment

/-!
# Source-shaped condition (ii) for Proposition 3.14

This file applies the orbit-construction theorem for Proposition 3.14 to the
literal tensor-and-field actions constructed for Proposition 3.11.  The
Brauer carrier is the function-valued `IBr` set, the ordinary carrier is the
selected `ell'`-series subtype of function-valued irreducible ordinary
characters, and the set of weights is the actual conjugacy class quotient of
radical subgroups with defect-zero local ordinary characters.  The acting
group is the semidirect product of quotient linear Brauer characters with the
field group.  Its action on weights is constructed by descent of each lifted
linear character to the local normaliser quotient and by right automorphism
transport.

For one representative of every block orbit, Proposition 3.11 constructs a
stabiliser-equivariant Brauer-to-ordinary-label equivalence.  Lean transports
those equivalences over all block orbits and composes them with the separately
cited ordinary-label-to-weight correspondence.  Only that correspondence,
its separate tensor and field formulas, its block compatibility, and the
remaining clauses of the Brough--Späth criterion are explicit E2/U inputs.
The weight-to-block map is constructed from the exact local-character block,
inflation, and block-induction source rather than supplied as a free function.
No Brauer-to-weight equivalence, arbitrary weight action, BAW-goodness, or
iBAW conclusion is assumed.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeCProposition313SourceInstantiation

open ModularRep.BlockFibreRestriction
open ModularRep.DecompositionBasicSetBridge
open ModularRep.ExactGrothendieckGroup
open ModularRep.FDRepSimpleClassKZero
open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs.ConlonBasicSet
open ModularRep.PaperProofs.OddConlonOrbitAssembly
open ModularRep.PaperProofs.TypeCConformalActionAdapter
open ModularRep.PaperProofs.TypeCExactStabilizerLemma310Relative
open ModularRep.PaperProofs.TypeCWeightTensorFieldAction

universe u

variable {p : Nat}
variable {K O k M E Block : Type u}
variable [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
variable [CharZero K] [IsAlgClosed K] [CharP k p] [IsAlgClosed k]
variable [Group M] [Fintype M] [Group E]

/-- Tensor one actual ordinary label by the inverse lifted quotient character.
This is the tensor part of the manuscript's right action. -/
def ordinaryTensorStep
    (G0 : Subgroup M) [G0.Normal]
    (field : E →* MulAut M)
    (hinvariant : FieldInvariantSubgroup.IsInvariant G0 field)
    (D : OrdinaryReductionEquiv (k := k) (K := K)
      G0 field hinvariant)
    (series : Irr K M → Prop)
    (seriesTensorStable : OrdinarySeriesTensorStable
      G0 field hinvariant D series)
    (lambda : TensorCharacters (k := k) G0)
    (x : TypeCProposition311SourceInstantiation.OrdinarySeriesCarrier series) :
    TypeCProposition311SourceInstantiation.OrdinarySeriesCarrier series :=
  ⟨OrdinaryIrreducibleCharacter.linearTwist x.1
      (OrdinaryReductionEquiv.lift
        (G0 := G0) (field := field) (hinvariant := hinvariant) D lambda)⁻¹,
    seriesTensorStable lambda x.1 x.2⟩

/-- Apply the inverse field automorphism to one actual ordinary label. -/
def ordinaryFieldStep
    (field : E →* MulAut M)
    (series : Irr K M → Prop)
    (seriesFieldStable : OrdinarySeriesFieldStable (K := K) field series)
    (e : E)
    (x : TypeCProposition311SourceInstantiation.OrdinarySeriesCarrier series) :
    TypeCProposition311SourceInstantiation.OrdinarySeriesCarrier series :=
  ⟨OrdinaryIrreducibleCharacter.twist K M x.1 (field e⁻¹),
    seriesFieldStable e x.1 x.2⟩

/-- The separately cited tensor and field formulas for Li's ordinary labels
imply equivariance for the actual semidirect product action. -/
theorem labelToWeight_combined_equivariant
    (G0 : Subgroup M) [G0.Normal]
    (field : E →* MulAut M)
    (hinvariant : FieldInvariantSubgroup.IsInvariant G0 field)
    (D : OrdinaryReductionEquiv (k := k) (K := K)
      G0 field hinvariant)
    (series : Irr K M → Prop)
    (seriesTensorStable : OrdinarySeriesTensorStable
      G0 field hinvariant D series)
    (seriesFieldStable : OrdinarySeriesFieldStable (K := K) field series)
    (radicalKernel : RadicalKernelLiftInput
      (p := p) G0 field hinvariant D)
    (rho : TypeCProposition311SourceInstantiation.OrdinarySeriesCarrier series ≃
      CharacterWeight.ConjugacyClass (p := p) (K := K) (G := M))
    (rho_tensor : ∀ (lambda : TensorCharacters (k := k) G0)
        (x : TypeCProposition311SourceInstantiation.OrdinarySeriesCarrier series),
      rho (ordinaryTensorStep G0 field hinvariant D series
        seriesTensorStable lambda x) =
        TypeCWeightTensorFieldAction.CharacterWeight.linearTwistConjugacyClass
          (TypeCWeightTensorFieldAction.radicalLift
            G0 field hinvariant D radicalKernel lambda)⁻¹ (rho x))
    (rho_field : ∀ (e : E)
        (x : TypeCProposition311SourceInstantiation.OrdinarySeriesCarrier series),
      rho (ordinaryFieldStep (K := K) field series seriesFieldStable e x) =
        CharacterWeight.rightTwistConjugacyClass (field e⁻¹) (rho x)) :
    let A := ActingGroup (k := k) G0 field hinvariant
    let Basic :=
      TypeCProposition311SourceInstantiation.OrdinarySeriesCarrier series
    let hseries := ordinarySeriesStable_of_tensor_and_field
      G0 field hinvariant D series seriesTensorStable seriesFieldStable
    let _ : MulAction A Basic :=
      TypeBSpecialCliffordActionAdapter.ordinarySeriesCarrierAction
        G0 field hinvariant D series hseries
    let _ : MulAction A
        (CharacterWeight.ConjugacyClass (p := p) (K := K) (G := M)) :=
      TypeCWeightTensorFieldAction.tensorFieldSemidirectAction
        G0 field hinvariant D radicalKernel
    ∀ (a : A) (x : Basic), rho (a • x) = a • rho x := by
  dsimp only
  let hseries := ordinarySeriesStable_of_tensor_and_field
    G0 field hinvariant D series seriesTensorStable seriesFieldStable
  letI ordinaryAction : MulAction
      (ActingGroup (k := k) G0 field hinvariant)
      (TypeCProposition311SourceInstantiation.OrdinarySeriesCarrier series) :=
    TypeBSpecialCliffordActionAdapter.ordinarySeriesCarrierAction
      G0 field hinvariant D series hseries
  letI weightAction : MulAction
      (ActingGroup (k := k) G0 field hinvariant)
      (CharacterWeight.ConjugacyClass (p := p) (K := K) (G := M)) :=
    TypeCWeightTensorFieldAction.tensorFieldSemidirectAction
      G0 field hinvariant D radicalKernel
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
    _ = TypeCWeightTensorFieldAction.CharacterWeight.linearTwistConjugacyClass
          (TypeCWeightTensorFieldAction.radicalLift
            G0 field hinvariant D radicalKernel a.left)⁻¹ (rho fieldX) :=
      rho_tensor a.left fieldX
    _ = TypeCWeightTensorFieldAction.CharacterWeight.linearTwistConjugacyClass
          (TypeCWeightTensorFieldAction.radicalLift
            G0 field hinvariant D radicalKernel a.left)⁻¹
          (CharacterWeight.rightTwistConjugacyClass
            (field a.right⁻¹) (rho x)) := by
      rw [rho_field a.right x]
    _ = a • rho x :=
      (TypeCWeightTensorFieldAction.tensorFieldSemidirectAction_apply
        G0 field hinvariant D radicalKernel a (rho x)).symm

/-- The condition-(ii) endpoint with the actual combined tensor and field
actions on ordinary characters, Brauer characters, and character weights.

The three families `hcard`, `conlon`, and `burnside` are indexed by blocks
because Proposition 3.11 is applied only to one representative of each block
orbit.  Stating them for every block is harmless and avoids making a second
choice of representatives in the interface.  The proof itself still selects
and transports only one local equivalence per orbit.
-/
theorem proposition_3_13_condition_ii_source_instantiated
    (G0 : Subgroup M) [G0.Normal]
    (field : E →* MulAut M)
    (hinvariant : FieldInvariantSubgroup.IsInvariant G0 field)
    (D : OrdinaryReductionEquiv (k := k) (K := K)
      G0 field hinvariant)
    [Finite E] [IsCyclic E]
    [Finite (TensorCharacters (k := k) G0)]
    [MulAction (ActingGroup (k := k) G0 field hinvariant) Block]
    [MulAction (MulAut M)ᵐᵒᵖ Block]
    (Msys : ModularSystem p K O k)
    (iota : PrimeRegularRootEmbedding p k K M)
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (productFormula : BrauerLinearTensorProductFormula iota)
    (series : Irr K M → Prop)
    [Finite
      (TypeCProposition311SourceInstantiation.OrdinarySeriesCarrier series)]
    (seriesTensorStable : OrdinarySeriesTensorStable
      G0 field hinvariant D series)
    (seriesFieldStable : OrdinarySeriesFieldStable (K := K) field series)
    (linearEquiv :
      MonoidAlgebra ℤ
          (TypeCProposition311SourceInstantiation.OrdinarySeriesCarrier series) ≃ₗ[ℤ]
        MonoidAlgebra ℤ (IBr iota))
    (hdecomposition : ∀ v : MonoidAlgebra ℤ
        (TypeCProposition311SourceInstantiation.OrdinarySeriesCarrier series),
      labelledSimpleClassKZero (simpleModuleClassEquivIBr iota hinj).symm
          (linearEquiv v) =
        decompositionMapOfStableReduction Msys iota hcompat
          (labelledSimpleClassKZero
            (TypeBSpecialCliffordActionAdapter.ordinarySeriesLabel
              (K := K) series) v))
    (ordinaryBlock : Irr K M → Block)
    (ordinaryBlockEquivariant : OrdinaryBlockEquivariant
      G0 field hinvariant D ordinaryBlock)
    [Fintype Block]
    {blockIdempotent : Block → k[M]}
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (brauerBlockEquivariant : BrauerBlockEquivariant
      G0 field hinvariant iota productFormula
        (irreducibleBrauerCharacterBlock iota hinj blocks))
    (hblockDiagonal : BlockDiagonalLinearEquiv
      (TypeBSpecialCliffordActionAdapter.ordinarySeriesBlockMap
        series ordinaryBlock)
      (irreducibleBrauerCharacterBlock iota hinj blocks)
      linearEquiv)
    (liftReductionCompatible :
      TypeBSpecialCliffordActionAdapter.OrdinaryLiftReductionCompatible
        G0 field hinvariant D iota)
    (radicalKernel : RadicalKernelLiftInput
      (p := p) G0 field hinvariant D)
    (hcard : ∀ block : Block, Nat.card
      (fieldProjection
        (LinearCharactersTrivialOn.fieldAction (k := k) field
          (FieldInvariantSubgroup.isFieldStable G0 field hinvariant))
        (MulAction.stabilizer
          (ActingGroup (k := k) G0 field hinvariant) block)).ker ≤ 2)
    (conlon : ∀ block : Block, PadicConlonMarkDetection.{u, u}
      (p := 2)
      (A := MulAction.stabilizer
        (ActingGroup (k := k) G0 field hinvariant) block))
    (burnside : ∀ block : Block, PublishedBurnsideMarkInjectivity.{u, u}
      (A := MulAction.stabilizer
        (ActingGroup (k := k) G0 field hinvariant) block))
    (blockSource : CharacterWeight.LocalBlockInductionSource
      (p := p) (k := k) (K := K) (G := M) (Block := Block))
    (rho : TypeCProposition311SourceInstantiation.OrdinarySeriesCarrier series ≃
      CharacterWeight.ConjugacyClass (p := p) (K := K) (G := M))
    (rho_tensor : ∀ (lambda : TensorCharacters (k := k) G0)
        (x : TypeCProposition311SourceInstantiation.OrdinarySeriesCarrier series),
      rho (ordinaryTensorStep G0 field hinvariant D series
        seriesTensorStable lambda x) =
        TypeCWeightTensorFieldAction.CharacterWeight.linearTwistConjugacyClass
          (TypeCWeightTensorFieldAction.radicalLift
            G0 field hinvariant D radicalKernel lambda)⁻¹ (rho x))
    (rho_field : ∀ (e : E)
        (x : TypeCProposition311SourceInstantiation.OrdinarySeriesCarrier series),
      rho (ordinaryFieldStep (K := K) field series seriesFieldStable e x) =
        CharacterWeight.rightTwistConjugacyClass (field e⁻¹) (rho x))
    (rho_block_preserving : ∀
      x : TypeCProposition311SourceInstantiation.OrdinarySeriesCarrier series,
      blockSource.weightBlock (rho x) =
        TypeBSpecialCliffordActionAdapter.ordinarySeriesBlockMap
          series ordinaryBlock x) :
    let A := ActingGroup (k := k) G0 field hinvariant
    let Basic :=
      TypeCProposition311SourceInstantiation.OrdinarySeriesCarrier series
    let hseries := ordinarySeriesStable_of_tensor_and_field
      G0 field hinvariant D series seriesTensorStable seriesFieldStable
    let _ : MulAction A Basic :=
      TypeBSpecialCliffordActionAdapter.ordinarySeriesCarrierAction
        G0 field hinvariant D series hseries
    let _ : MulAction A (IBr iota) :=
      TypeBSpecialCliffordActionAdapter.brauerCharacterAction
        G0 field hinvariant iota productFormula
    let _ : MulAction A
        (CharacterWeight.ConjugacyClass (p := p) (K := K) (G := M)) :=
      TypeCWeightTensorFieldAction.tensorFieldSemidirectAction
        G0 field hinvariant D radicalKernel
    let brauerBlock := irreducibleBrauerCharacterBlock iota hinj blocks
    ∃ omega : IBr iota ≃
        CharacterWeight.ConjugacyClass (p := p) (K := K) (G := M),
      (∀ (a : A) (phi : IBr iota), omega (a • phi) = a • omega phi) ∧
      (∀ phi : IBr iota,
        blockSource.weightBlock (omega phi) = brauerBlock phi) ∧
      (∀ (a : A)
        (W : CharacterWeight.ConjugacyClass
          (p := p) (K := K) (G := M)),
        blockSource.weightBlock (a • W) =
          a • blockSource.weightBlock W) := by
  dsimp only
  let A := ActingGroup (k := k) G0 field hinvariant
  let Basic :=
    TypeCProposition311SourceInstantiation.OrdinarySeriesCarrier series
  let ordinaryBlockOnSeries :=
    TypeBSpecialCliffordActionAdapter.ordinarySeriesBlockMap
      series ordinaryBlock
  let brauerBlock := irreducibleBrauerCharacterBlock iota hinj blocks
  have hseries : OrdinarySeriesStable G0 field hinvariant D series :=
    ordinarySeriesStable_of_tensor_and_field
      G0 field hinvariant D series seriesTensorStable seriesFieldStable
  letI ordinaryAction : MulAction A Basic :=
    TypeBSpecialCliffordActionAdapter.ordinarySeriesCarrierAction
      G0 field hinvariant D series hseries
  letI brauerAction : MulAction A (IBr iota) :=
    TypeBSpecialCliffordActionAdapter.brauerCharacterAction
      G0 field hinvariant iota productFormula
  letI weightAction : MulAction A
      (CharacterWeight.ConjugacyClass (p := p) (K := K) (G := M)) :=
    TypeCWeightTensorFieldAction.tensorFieldSemidirectAction
      G0 field hinvariant D radicalKernel
  have rho_equivariant : ∀ (a : A) (x : Basic),
      rho (a • x) = a • rho x :=
    labelToWeight_combined_equivariant
      G0 field hinvariant D series seriesTensorStable seriesFieldStable
        radicalKernel rho rho_tensor rho_field
  have hordinaryBlock : ∀ (a : A) (x : Basic),
      ordinaryBlockOnSeries (a • x) = a • ordinaryBlockOnSeries x := by
    intro a x
    exact TypeBSpecialCliffordActionAdapter.ordinarySeriesBlockMap_equivariant
      G0 field hinvariant D series ordinaryBlock hseries
        ordinaryBlockEquivariant a x
  have hbrauerBlock : ∀ (a : A) (phi : IBr iota),
      brauerBlock (a • phi) = a • brauerBlock phi := by
    intro a phi
    exact brauerBlockEquivariant a phi
  have hweightBlock : ∀ (a : A)
      (W : CharacterWeight.ConjugacyClass
        (p := p) (K := K) (G := M)),
      blockSource.weightBlock (a • W) =
        a • blockSource.weightBlock W := by
    intro a W
    obtain ⟨x, rfl⟩ := rho.surjective W
    calc
      blockSource.weightBlock (a • rho x) =
          blockSource.weightBlock (rho (a • x)) :=
        congrArg blockSource.weightBlock (rho_equivariant a x).symm
      _ = ordinaryBlockOnSeries (a • x) := rho_block_preserving (a • x)
      _ = a • ordinaryBlockOnSeries x := hordinaryBlock a x
      _ = a • blockSource.weightBlock (rho x) :=
        congrArg (fun b : Block ↦ a • b) (rho_block_preserving x).symm
  have alphaExists : RepresentativeEquivExists
      brauerBlock ordinaryBlockOnSeries hbrauerBlock := by
    intro orbit
    let block : Block := orbitRepresentative orbit
    obtain ⟨e, he⟩ :=
      TypeCProposition311SourceInstantiation.proposition_3_11_source_instantiated
        G0 field hinvariant D Msys iota hcompat hinj productFormula
          series seriesTensorStable seriesFieldStable linearEquiv
          hdecomposition ordinaryBlock ordinaryBlockEquivariant blocks
          brauerBlockEquivariant hblockDiagonal liftReductionCompatible
          block (hcard block) (conlon block) (burnside block)
    refine ⟨e, ?_⟩
    intro a ha phi
    let j : MulAction.stabilizer A block := ⟨a, ha⟩
    have hj := he j phi
    exact congrArg Subtype.val hj
  obtain ⟨omega, homegaEquivariant, homegaBlock⟩ :=
    exists_condition_ii_bijection_of_orbitwise_composition
      brauerBlock ordinaryBlockOnSeries blockSource.weightBlock
        hbrauerBlock hordinaryBlock alphaExists rho rho_equivariant
        rho_block_preserving
  exact ⟨omega, homegaEquivariant, homegaBlock, hweightBlock⟩

end ModularRep.PaperProofs.TypeCProposition313SourceInstantiation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
