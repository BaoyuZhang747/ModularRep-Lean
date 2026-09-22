import ModularRep.PaperProofs.TypeBConlonBlockRelative
import ModularRep.PaperProofs.OddConlonOrbitAssembly
import ModularRep.StabilizerFactorizationTransport

/-!
# The manuscript deductions in Proposition 4.3

This file checks the new orbit-construction step in the odd-prime type-B proof.
It does not assume a blockwise Brauer-to-label bijection.  For each selected
block-orbit representative, it restricts the exact `K₀` action and
naturality to the literal block stabiliser and invokes the source-shaped
relative form of Lemma 4.2.  The resulting stabiliser-equivariant local
bijections are then transported along block orbits and composed with the
published ordinary-label-to-weight correspondence.

The final correspondence is only the equivariant, block-preserving bijection
required in one clause of the external Brough--Späth criterion.  No instance
of that criterion, inductive BAW, or iBAW is assumed or concluded here.  The
ordinary-label-to-weight correspondence and the exact representation-
theoretic inputs to Lemma 4.2 remain explicit parameters.

The stabiliser-factorisation transfer used later in the manuscript is already
checked, independently of this theorem, in
`StabilizerFactorizationTransport`.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBOddPrimesProposition44Relative

open ModularRep.BlockFibreRestriction
open ModularRep.DecompositionBasicSetBridge
open ModularRep.ExactGrothendieckGroup
open ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.ConlonBasicSet
open ModularRep.PaperProofs.OddConlonOrbitAssembly
open ModularRep.PaperProofs.OddConformalProposition311Relative
open ModularRep.PaperProofs.TypeBConlonBlockRelative

universe u

variable {p : Nat}
variable {G k K Basic A BlockIndex CyclicTarget ScalarField
  Semisimple Weight : Type u}
variable [Group G] [Finite G]
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group A] [Finite A]
variable [Group CyclicTarget] [IsCyclic CyclicTarget]
variable [Field ScalarField]
variable [Finite Basic] [MulAction A Basic]
variable [MulAction A BlockIndex] [MulAction A Weight]

/-- Restriction of a `K₀` action to a subgroup of the acting group.  The
label actions are the literal restrictions of the ambient actions; no
equivariance conclusion is inserted here. -/
noncomputable def restrictLabelledKZeroActionDataToSubgroup
    {decomposition : FDRepKZero K G →+ FDRepKZero k G}
    {iota : PrimeRegularRootEmbedding p k K G}
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

omit [Finite A] [Finite Basic] in
/-- Exact decomposition naturality restricts to every subgroup of the acting
group. -/
theorem decompositionNatural_restrict_subgroup
    {decomposition : FDRepKZero K G →+ FDRepKZero k G}
    {iota : PrimeRegularRootEmbedding p k K G}
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
    let restricted := restrictLabelledKZeroActionDataToSubgroup
      basicSet ambient J hBasic hBrauer
    DecompositionNatural (A := J) decomposition
      restricted.ordinaryAction restricted.modularAction := by
  dsimp only [restrictLabelledKZeroActionDataToSubgroup]
  intro j x
  exact ambientNatural (j : A) x

/-- The protected core of Proposition 4.3's global-bijection argument.

The hypotheses before `rho` are the non-conclusion inputs used by Lemma 4.2
on each literal block stabiliser.  In particular, neither a local blockwise
bijection nor a global Brauer-to-weight bijection is assumed.  `rho` is the
published equivariant correspondence from ordinary labels to weights.  Lean
constructs the local Conlon--Burnside bijections, transports them along block
orbits, composes them with `rho`, and proves block preservation and
equivariance of the result. -/
theorem exists_global_weight_equiv_of_lemma_4_3
    (iota : PrimeRegularRootEmbedding p k K G)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    [MulAction A (IBr iota)]
    [Fintype BlockIndex]
    {blockIdempotent : BlockIndex → k[G]}
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    {decomposition : FDRepKZero K G →+ FDRepKZero k G}
    (basicSet : RestrictedIntegralBasicSetOnIBr
      iota hinj Basic decomposition)
    (ordinaryBlock : Basic → BlockIndex)
    (hblockDiagonal : BlockDiagonalLinearEquiv ordinaryBlock
      (irreducibleBrauerCharacterBlock iota hinj blocks)
      basicSet.linearEquiv)
    (ambientActions : LabelledKZeroActionData (A := A)
      basicSet.toRestrictedIntegralBasicSet)
    (ambientNatural : DecompositionNatural (A := A) decomposition
      ambientActions.ordinaryAction ambientActions.modularAction)
    (ordinaryBlockEquivariant : ∀ (a : A) (x : Basic),
      ordinaryBlock (a • x) = a • ordinaryBlock x)
    (brauerBlockEquivariant : ∀ (a : A) (phi : IBr iota),
      irreducibleBrauerCharacterBlock iota hinj blocks (a • phi) =
        a • irreducibleBrauerCharacterBlock iota hinj blocks phi)
    (fieldProjection : ∀ omega : BlockOrbit A BlockIndex,
      MulAction.stabilizer A (orbitRepresentative omega) →* CyclicTarget)
    (scalar : ∀ omega : BlockOrbit A BlockIndex,
      (fieldProjection omega).ker → ScalarFieldˣ)
    (scalarInjective : ∀ omega : BlockOrbit A BlockIndex,
      Function.Injective (scalar omega))
    (parameter : BlockOrbit A BlockIndex → Semisimple)
    (translate : ScalarFieldˣ → Semisimple → Semisimple)
    (multiplier : Semisimple → ScalarFieldˣ)
    (IsConjugate : Semisimple → Semisimple → Prop)
    (multiplierEqOfConjugate : ∀ {s t : Semisimple},
      IsConjugate s t → multiplier s = multiplier t)
    (translatedConjugate : ∀ (omega : BlockOrbit A BlockIndex)
      (d : (fieldProjection omega).ker),
      IsConjugate (parameter omega)
        (translate (scalar omega d) (parameter omega)))
    (multiplierTranslate : ∀ (z : ScalarFieldˣ) (s : Semisimple),
      multiplier (translate z s) = z ^ 2 * multiplier s)
    (conlon : ∀ omega : BlockOrbit A BlockIndex,
      PadicConlonMarkDetection.{u, u}
        (p := 2) (A := MulAction.stabilizer A (orbitRepresentative omega)))
    (burnside : ∀ omega : BlockOrbit A BlockIndex,
      PublishedBurnsideMarkInjectivity.{u, u}
        (A := MulAction.stabilizer A (orbitRepresentative omega)))
    (weightBlock : Weight → BlockIndex)
    (rho : Basic ≃ Weight)
    (rhoEquivariant : ∀ (a : A) (x : Basic), rho (a • x) = a • rho x)
    (rhoBlockPreserving : ∀ x : Basic,
      weightBlock (rho x) = ordinaryBlock x) :
    ∃ omega : IBr iota ≃ Weight,
      (∀ (a : A) (phi : IBr iota), omega (a • phi) = a • omega phi) ∧
      (∀ phi : IBr iota,
        weightBlock (omega phi) =
          irreducibleBrauerCharacterBlock iota hinj blocks phi) := by
  let brauerBlock := irreducibleBrauerCharacterBlock iota hinj blocks
  have alphaExists : RepresentativeEquivExists
      brauerBlock ordinaryBlock brauerBlockEquivariant := by
    intro orbit
    let block := orbitRepresentative orbit
    let J := MulAction.stabilizer A block
    let _ : MulAction J Basic := MulAction.compHom Basic J.subtype
    let _ : MulAction J (IBr iota) := MulAction.compHom (IBr iota) J.subtype
    have hBasic : ∀ (j : J) (x : Basic), j • x = (j : A) • x := by
      intro j x
      rfl
    have hBrauer : ∀ (j : J) (phi : IBr iota),
        j • phi = (j : A) • phi := by
      intro j phi
      rfl
    let restrictedActions := restrictLabelledKZeroActionDataToSubgroup
      basicSet ambientActions J hBasic hBrauer
    have restrictedNatural : DecompositionNatural (A := J) decomposition
        restrictedActions.ordinaryAction restrictedActions.modularAction :=
      decompositionNatural_restrict_subgroup basicSet ambientActions
        ambientNatural J hBasic hBrauer
    have ordinaryStable : ∀ (j : J) (x : Basic),
        ordinaryBlock x = block → ordinaryBlock (j • x) = block := by
      intro j x hx
      rw [hBasic, ordinaryBlockEquivariant, hx]
      exact j.property
    have brauerStable : ∀ (j : J) (phi : IBr iota),
        brauerBlock phi = block → brauerBlock (j • phi) = block := by
      intro j phi hphi
      change irreducibleBrauerCharacterBlock iota hinj blocks (j • phi) = block
      change irreducibleBrauerCharacterBlock iota hinj blocks phi = block at hphi
      rw [hBrauer, brauerBlockEquivariant, hphi]
      exact j.property
    have hlocal := lemma_4_3_relative
      (J := J) iota hinj blocks block basicSet ordinaryBlock
      hblockDiagonal restrictedActions restrictedNatural ordinaryStable
      brauerStable (fieldProjection orbit) (scalar orbit)
      (scalarInjective orbit) (parameter orbit) translate multiplier
      IsConjugate multiplierEqOfConjugate (translatedConjugate orbit)
      multiplierTranslate (conlon orbit) (burnside orbit)
    rcases hlocal with ⟨_, e, he⟩
    refine ⟨e, ?_⟩
    intro a hfix phi
    let j : J := ⟨a, hfix⟩
    have hj := he j phi
    exact congrArg Subtype.val hj
  exact exists_condition_ii_bijection_of_orbitwise_composition
    (A := A)
    (brauerBlock := brauerBlock)
    (labelBlock := ordinaryBlock)
    (weightBlock := weightBlock)
    brauerBlockEquivariant ordinaryBlockEquivariant alphaExists
    rho rhoEquivariant rhoBlockPreserving

end ModularRep.PaperProofs.TypeBOddPrimesProposition44Relative


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
