import ModularRep.PaperProofs.TypeCCurrentOrdinaryActions
import ModularRep.PaperProofs.TypeBSpecialCliffordActionAdapter
import ModularRep.PaperProofs.TypeCExactStabilizerLemma310Relative

/-!
Current coefficient adapter: the original Conlon, block-fibre and orbit
proofs are retained with characteristic-zero simple labels and their checked
tensor/field action, without ordinary algebraic closure.

# Source-shaped instantiation of Proposition 3.11

This file connects the abstract Conlon--Burnside endpoint for manuscript
Proposition 3.11 to the literal tensor and field actions on function-valued
ordinary and Brauer characters.  The ambient group remains an arbitrary
finite group with a normal subgroup because the identification with the
finite conformal symplectic group is a routine source input, not a
manuscript-specific deduction.

The ordinary carrier is the subtype of `Irr` cut out by the selected
`ell'`-series predicate.  The modular carrier is the literal function-valued
set `IBr`.  The exact Grothendieck-group actions and decomposition naturality
are constructed from quotient linear characters, their ordinary lifts, and
field pullback.  They are then restricted to the literal stabiliser of the
selected block.

The global integral basic-set equivalence, its block support, the concrete
series and block stability assertions, and Li's order bound on the tensor
kernel remain explicit source inputs.  No equivariant set bijection, Conlon
conclusion, BAW condition, or iBAW condition is assumed.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeCCurrentProposition311

open ModularRep.BlockFibreRestriction
open ModularRep.DecompositionBasicSetBridge
open ModularRep.ExactGrothendieckGroup
open ModularRep.FDRepSimpleClassKZero
open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs.ConlonBasicSet
open ModularRep.PaperProofs.OddConformalProposition311Relative
open ModularRep.PaperProofs.TypeCConformalActionAdapter
open ModularRep.PaperProofs.TypeCExactStabilizerLemma310Relative

universe u

variable {p : Nat}
variable {K O k M E Block : Type u}
variable [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
variable [CharZero K] [CharP k p] [IsAlgClosed k]
variable [Group M] [Finite M] [Group E]

abbrev TensorCharacters (G0 : Subgroup M) :=
  TypeCConformalActionAdapter.TensorCharacters (k := k) G0

abbrev ActingGroup
    (G0 : Subgroup M) [G0.Normal]
    (field : E →* MulAut M)
    (hinvariant : FieldInvariantSubgroup.IsInvariant G0 field) :=
  TypeCConformalActionAdapter.ActingGroup
    (k := k) G0 field hinvariant

abbrev OrdinarySeriesCarrier (series : Irr K M → Prop) :=
  TypeBOrdinaryLabelSplitting.OrdinarySeriesCarrier series

section Restriction

variable {Basic A : Type u} [Group A]
variable [MulAction A Basic]

omit [Finite M] [Group E] in
/-- Restrict the exact `K₀` action data to a subgroup of the acting group.
The label actions are required to be the literal restrictions of the ambient
actions. -/
def restrictLabelledKZeroActionData
    {decomposition : FDRepKZero K M →+ FDRepKZero k M}
    {iota : PrimeRegularRootEmbedding p k K M}
    {hinj : IrreducibleBrauerCharacterInjectivity iota}
    [MulAction A (IBr iota)]
    (basicSet : RestrictedIntegralBasicSetOnIBr
      iota hinj Basic decomposition)
    (ambient : LabelledKZeroActionData (A := A)
      basicSet.toRestrictedIntegralBasicSet)
    (J : Subgroup A)
    [MulAction J Basic] [MulAction J (IBr iota)]
    (hBasic : ∀ (j : J) (x : Basic), j • x = (j : A) • x)
    (hBrauer : ∀ (j : J) (phi : IBr iota), j • phi = (j : A) • phi) :
    LabelledKZeroActionData (A := J)
      basicSet.toRestrictedIntegralBasicSet where
  ordinaryAction := ambient.ordinaryAction.pullback J.subtype
  modularAction := ambient.modularAction.pullback J.subtype
  ordinary_single j x := by
    rw [hBasic]
    exact ambient.ordinary_single (j : A) x
  modular_single j phi := by
    rw [hBrauer]
    exact ambient.modular_single (j : A) phi

/-- Exact decomposition naturality restricts to the same literal subgroup. -/
theorem decompositionNatural_restrict
    {decomposition : FDRepKZero K M →+ FDRepKZero k M}
    {iota : PrimeRegularRootEmbedding p k K M}
    {hinj : IrreducibleBrauerCharacterInjectivity iota}
    [MulAction A (IBr iota)]
    (basicSet : RestrictedIntegralBasicSetOnIBr
      iota hinj Basic decomposition)
    (ambient : LabelledKZeroActionData (A := A)
      basicSet.toRestrictedIntegralBasicSet)
    (ambientNatural : DecompositionNatural (A := A) decomposition
      ambient.ordinaryAction ambient.modularAction)
    (J : Subgroup A)
    [MulAction J Basic] [MulAction J (IBr iota)]
    (hBasic : ∀ (j : J) (x : Basic), j • x = (j : A) • x)
    (hBrauer : ∀ (j : J) (phi : IBr iota), j • phi = (j : A) • phi) :
    let restricted := restrictLabelledKZeroActionData
      basicSet ambient J hBasic hBrauer
    DecompositionNatural (A := J) decomposition
      restricted.ordinaryAction restricted.modularAction := by
  dsimp only [restrictLabelledKZeroActionData]
  intro j x
  exact ambientNatural (j : A) x

end Restriction

section SourceInstantiation

variable (G0 : Subgroup M) [G0.Normal]
variable (field : E →* MulAut M)
variable (hinvariant : FieldInvariantSubgroup.IsInvariant G0 field)
variable (D : OrdinaryReductionEquiv (k := k) (K := K)
  G0 field hinvariant)
variable [MulAction (ActingGroup (k := k) G0 field hinvariant) Block]

/-- The strongest current source-shaped endpoint for Proposition 3.11.

The output is an equivariant equivalence between the literal Brauer block
fibre and the literal ordinary `ell'`-series block fibre.  The latter is
written as a nested subtype: its elements are ordinary irreducible characters
which satisfy `series` and whose ordinary block is `block`.

The arguments `linearEquiv`, `hdecomposition`, and `hblockDiagonal` are the
precise integral-basic-set and block-support content supplied by
Feng--Li--Zhang and Li.  They do not assert the desired equivariant set
equivalence.  The finite conformal/symplectic pair and Frobenius action are
routine E1 source instances and receive no K credit.  The ordinary reduction
identification, series stability, concrete block maps, block support, and
Li's kernel-cardinality bound remain explicit E2/U inputs. -/
theorem proposition_3_11_source_instantiated
    [Finite E] [IsCyclic E]
    [Finite (TensorCharacters (k := k) G0)]
    (Msys : ModularSystem p K O k)
    (iota : PrimeRegularRootEmbedding p k K M)
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (productFormula : BrauerLinearTensorProductFormula iota)
    (series : Irr K M → Prop)
    [Finite (OrdinarySeriesCarrier series)]
    (seriesTensorStable : OrdinarySeriesTensorStable
      G0 field hinvariant D series)
    (seriesFieldStable : OrdinarySeriesFieldStable (K := K) field series)
    (linearEquiv :
      MonoidAlgebra ℤ (OrdinarySeriesCarrier series) ≃ₗ[ℤ]
        MonoidAlgebra ℤ (IBr iota))
    (hdecomposition : ∀ v : MonoidAlgebra ℤ (OrdinarySeriesCarrier series),
      labelledSimpleClassKZero (simpleModuleClassEquivIBr iota hinj).symm
          (linearEquiv v) =
        decompositionMapOfStableReduction Msys iota hcompat
          (labelledSimpleClassKZero
            (TypeBOrdinaryLabelSplitting.ordinarySeriesLabel
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
    (block : Block)
    (hcard : Nat.card
      (fieldProjection
        (LinearCharactersTrivialOn.fieldAction (k := k) field
          (FieldInvariantSubgroup.isFieldStable G0 field hinvariant))
        (MulAction.stabilizer
          (ActingGroup (k := k) G0 field hinvariant) block)).ker ≤ 2)
    (conlon : PadicConlonMarkDetection.{u, u}
      (p := 2)
      (A := MulAction.stabilizer
        (ActingGroup (k := k) G0 field hinvariant) block))
    (burnside : PublishedBurnsideMarkInjectivity.{u, u}
      (A := MulAction.stabilizer
        (ActingGroup (k := k) G0 field hinvariant) block)) :
    let A := ActingGroup (k := k) G0 field hinvariant
    let J := MulAction.stabilizer A block
    let Basic := OrdinarySeriesCarrier series
    let ordinaryBlockOnSeries : Basic → Block :=
      TypeBSpecialCliffordActionAdapter.ordinarySeriesBlockMap
        series ordinaryBlock
    let brauerBlock := irreducibleBrauerCharacterBlock iota hinj blocks
    let hseries := ordinarySeriesStable_of_tensor_and_field
      G0 field hinvariant D series seriesTensorStable seriesFieldStable
    let _ : MulAction A Basic :=
      TypeBSpecialCliffordActionAdapter.ordinarySeriesCarrierAction
        G0 field hinvariant D series hseries
    let _ : MulAction A (IBr iota) :=
      TypeBSpecialCliffordActionAdapter.brauerCharacterAction
        G0 field hinvariant iota productFormula
    let _ : MulAction J Basic := MulAction.compHom Basic J.subtype
    let _ : MulAction J (IBr iota) := MulAction.compHom (IBr iota) J.subtype
    let ordinaryStable : ∀ (j : J) (x : Basic),
        ordinaryBlockOnSeries x = block →
          ordinaryBlockOnSeries (j • x) = block := fun j x hx ↦ by
      rw [show j • x = (j : A) • x by rfl]
      change TypeBSpecialCliffordActionAdapter.ordinarySeriesBlockMap
        series ordinaryBlock ((j : A) • x) = block
      rw [TypeBSpecialCliffordActionSplitting.ordinarySeriesBlockMap_equivariant
        G0 field hinvariant D series ordinaryBlock hseries
          ordinaryBlockEquivariant (j : A) x]
      have hx' : TypeBSpecialCliffordActionAdapter.ordinarySeriesBlockMap
          series ordinaryBlock x = block := hx
      rw [hx']
      exact j.property
    let brauerStable : ∀ (j : J) (phi : IBr iota),
        brauerBlock phi = block → brauerBlock (j • phi) = block :=
      fun j phi hphi ↦ by
        rw [show j • phi = (j : A) • phi by rfl]
        change irreducibleBrauerCharacterBlock iota hinj blocks
          ((j : A) • phi) = block
        rw [brauerBlockEquivariant]
        have hphi' : irreducibleBrauerCharacterBlock iota hinj blocks phi =
            block := hphi
        rw [hphi']
        exact j.property
    let _ : MulAction J (BlockFibre ordinaryBlockOnSeries block) :=
      stableBlockFibreMulAction ordinaryBlockOnSeries block ordinaryStable
    let _ : MulAction J (BlockFibre brauerBlock block) :=
      stableBlockFibreMulAction brauerBlock block brauerStable
    ∃ e : BlockFibre brauerBlock block ≃
        BlockFibre ordinaryBlockOnSeries block,
      ∀ (j : J) (phi : BlockFibre brauerBlock block),
        e (j • phi) = j • e phi := by
  dsimp only
  let A := ActingGroup (k := k) G0 field hinvariant
  let J := MulAction.stabilizer A block
  let Basic := OrdinarySeriesCarrier series
  let ordinaryBlockOnSeries : Basic → Block :=
    TypeBSpecialCliffordActionAdapter.ordinarySeriesBlockMap
      series ordinaryBlock
  let brauerBlock := irreducibleBrauerCharacterBlock iota hinj blocks
  have hseries : OrdinarySeriesStable G0 field hinvariant D series :=
    ordinarySeriesStable_of_tensor_and_field
      G0 field hinvariant D series seriesTensorStable seriesFieldStable
  letI ambientBasicAction : MulAction A Basic :=
    TypeBSpecialCliffordActionAdapter.ordinarySeriesCarrierAction
      G0 field hinvariant D series hseries
  letI ambientBrauerAction : MulAction A (IBr iota) :=
    TypeBSpecialCliffordActionAdapter.brauerCharacterAction
      G0 field hinvariant iota productFormula
  letI localBasicAction : MulAction J Basic :=
    MulAction.compHom Basic J.subtype
  letI localBrauerAction : MulAction J (IBr iota) :=
    MulAction.compHom (IBr iota) J.subtype
  have hBasic : ∀ (j : J) (x : Basic), j • x = (j : A) • x := by
    intro j x
    rfl
  have hBrauer : ∀ (j : J) (phi : IBr iota),
      j • phi = (j : A) • phi := by
    intro j phi
    rfl
  let basicSet := TypeCCurrentOrdinaryActions.ordinarySeriesBasicSet
    Msys iota hcompat hinj series linearEquiv hdecomposition
  let ambientActions := TypeCCurrentOrdinaryActions.labelledKZeroActionData
    G0 field hinvariant D Msys iota hcompat hinj productFormula
      series hseries linearEquiv hdecomposition
  have ambientNatural : DecompositionNatural (A := A)
      (decompositionMapOfStableReduction Msys iota hcompat)
      ambientActions.ordinaryAction ambientActions.modularAction :=
    TypeBSpecialCliffordActionSplitting.decompositionNatural
      G0 field hinvariant D Msys iota hcompat productFormula
        liftReductionCompatible
  let restrictedActions := restrictLabelledKZeroActionData
    basicSet ambientActions J hBasic hBrauer
  have restrictedNatural : DecompositionNatural (A := J)
      (decompositionMapOfStableReduction Msys iota hcompat)
      restrictedActions.ordinaryAction restrictedActions.modularAction :=
    decompositionNatural_restrict
      basicSet ambientActions ambientNatural J hBasic hBrauer
  have ordinaryStable : ∀ (j : J) (x : Basic),
      ordinaryBlockOnSeries x = block →
        ordinaryBlockOnSeries (j • x) = block := by
    intro j x hx
    rw [hBasic]
    change TypeBSpecialCliffordActionAdapter.ordinarySeriesBlockMap
      series ordinaryBlock ((j : A) • x) = block
    rw [TypeBSpecialCliffordActionSplitting.ordinarySeriesBlockMap_equivariant
      G0 field hinvariant D series ordinaryBlock hseries
        ordinaryBlockEquivariant (j : A) x]
    have hx' : TypeBSpecialCliffordActionAdapter.ordinarySeriesBlockMap
        series ordinaryBlock x = block := hx
    rw [hx']
    exact j.property
  have brauerStable : ∀ (j : J) (phi : IBr iota),
      brauerBlock phi = block → brauerBlock (j • phi) = block := by
    intro j phi hphi
    rw [hBrauer]
    change irreducibleBrauerCharacterBlock iota hinj blocks
      ((j : A) • phi) = block
    rw [brauerBlockEquivariant]
    have hphi' : irreducibleBrauerCharacterBlock iota hinj blocks phi =
        block := hphi
    rw [hphi']
    exact j.property
  exact proposition_3_11_of_exactStabilizer
    (LinearCharactersTrivialOn.fieldAction (k := k) field
      (FieldInvariantSubgroup.isFieldStable G0 field hinvariant))
    J iota hinj blocks block basicSet ordinaryBlockOnSeries hblockDiagonal
      restrictedActions restrictedNatural ordinaryStable brauerStable
      hcard conlon burnside

end SourceInstantiation

end ModularRep.PaperProofs.TypeCCurrentProposition311


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
