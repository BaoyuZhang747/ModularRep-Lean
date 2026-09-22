import ManuscriptIBAW.Sporadic.Fi24ThreeLocal
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3Definition41Assembly
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierLiteralV3Rows
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedModels

/-!
# The Fischer argument at three

The source specifies ordinary rows, their class values and outer fusion. The
entry for the elementary abelian subgroup of order nine in An–Dietrich
(2012), Table 8, identifies four local quotient characters, two of which
are fixed by the outer involution. The table's central
character identity determines their induced block. The published total of
four weights proves that these weights exhaust the block. The rank and local
fixed point arguments give signature (4,2). Normalisation for defect zero
characters and cancellation in the published equivariant correspondence for
the whole group then construct a block preserving map.

Radical support and the block bijection follow from these arguments. Neither
is assumed. The full condition additionally assumes compatible model,
extension and intermediate block witnesses for the same matching.
Interpretations of the literature, tables and characters remain explicit
published, computational and structural assumptions.
-/

noncomputable section
set_option maxHeartbeats 4000000
open scoped MonoidAlgebra
namespace ManuscriptIBAW.Sporadic.Fi24Three
open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs
open ModularRep.NavarroCoveringBrauerExtension ModularRep.NavarroBrauerRestrictionCovering
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorCarriers
open SporadicFi24P3Definition44NamedCarrierSmallCenterFamilyComparison
open SporadicFi24P3Definition44NamedCarrierQOneBlockCatalogues
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicCompleteCollapseLemma52Actual
  (DefectZeroReductionSource TrivialWeightSource GlobalDefectZeroCharacter)
open SporadicFi24QOneNormalisationActual
  (DefectZeroOrdinaryBlockSource DefectZeroWeightSubgroupSource)
open SporadicFi24P3AnDietrichSourceCertificate
open SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
open SporadicFi24P3Definition44NamedCarrierActualSectorOrdinarySpan
open SporadicFi24P3Definition44NamedCarrierActualSectorCoordinateEvaluation
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierAllPairs
open SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryFamily
open SporadicFi24P3Definition44NamedCarrierCenterlessDefinition41Data
open SporadicFi24P3Definition44NamedCarrierCenterlessEmbeddedBlockRows
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierLiteralV3Rows
open SporadicFi24P3V3RawRankCertificate SporadicFi24P3PlusRankReplayContract
open SporadicFi24P3Definition44NamedCarrierAcceleratedNamedModels
open SporadicFi24P3Definition44NamedCarrierAcceleratedDefinition41Certificate
open EvenFieldFLZSourceConditions
open TypeBCentralKernelNormalizerInertia (localAut)

universe u
variable {SourceAction SourceBrauer SourceWeight : Type u}
  [Group SourceAction] [MulAction SourceAction SourceBrauer]
  [MulAction SourceAction SourceWeight]
  {k K G : Type u}
  [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
  [Group G] [Fintype G]
  (iota : PrimeRegularRootEmbedding 3 k K G)
  (R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := G))

local instance centerFintype : Fintype (Subgroup.center G) := Fintype.ofFinite _

/-- The source assumptions for the argument. The An–Dietrich map is the
published correspondence for the whole character set. Membership in the
selected block and exhaustion of its weights are derived from the specified
table identities and numerical counts. -/
structure SourceInputs where
  roles : Fin 3 ≃ ActualBlock (k := k) (X := G)
  AD : AnDietrichFi24P3SourceCertificate
    (SourceAction := SourceAction) (SourceBrauer := SourceBrauer) (SourceWeight := SourceWeight)
  Bridge : AnDietrichFi24P3LiteralCarrierBridge
    (SourceAction := SourceAction) (SourceBrauer := SourceBrauer) (SourceWeight := SourceWeight) iota
  hOuter : Nat.card (LiteralOuterQuotient G) = 2
  tau : MulAut G
  htau : QuotientGroup.mk' (RepresentationWeight.innerInverseOpHom (G := G)).range
    (MulOpposite.op tau) ≠ 1
  fixedNonprincipal : MulOpposite.op tau • roles 1 = roles 1
  fixedDefectZero : MulOpposite.op tau • roles 2 = roles 2
  Dordinary : let _ := R.1.operations.ambientBlockData.fintypeBlock
    ActualOrdinaryDecomposition iota
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
      R.1.operations.ambientBlockData.blocks
  selected : Fin 6 → OrdinaryIrreducibleCharacter.Irr K G
  ordinaryComplete : let _ := R.1.operations.ambientBlockData.fintypeBlock
    ∀ chi, Dordinary.ordinaryBlock chi = roles 1 ↔ ∃ r, selected r = chi
  representatives : PrimeRegularRepresentativeCover 3 G (Fin 30)
  encoding : PrimitiveTwentyNineEncoding K
  ordinaryValues : ∀ r c,
    (selected r).1 (representatives.representative c).1 = literalV3Rows encoding r c
  fusion : ∀ c : Fin 30, ∃ x : G, tau (representatives.representative c).1 =
    x * (representatives.representative (regularOuterPermutation c)).1 * x⁻¹
  Q : RadicalSubgroup (p := 3) (G := G)
  /-- The radical subgroup in the `3^2` row of An–Dietrich (2012), Table 8. -/
  radicalOrder : Nat.card Q.1 = 9
  radicalExponent : ∀ x : Q.1, x ^ 3 = 1
  rows : Fin 4 → LocalDefectZeroCharacter (K := K) Q
  /-- Identification of all four local defect-zero characters in that row. -/
  rowBijective : Function.Bijective rows
  table : Fi24ThreeLocal.NamedTableSource R Q (roles 1) rows
  weightCount : Nat.card {w : WeightClass (p := 3) (K := K) (X := G) //
    R.1.weightBlock w = roles 1} = 4
  g : G
  stable : Q.1.comap (tau * MulAut.conj g).toMonoidHom = Q.1
  /-- The fixed count in the entry `2/2` of An–Dietrich (2012), Table 8,
  interpreted on the stated radical subgroup and normaliser action. -/
  localFixed : Nat.card {theta : LocalDefectZeroCharacter (K := K) Q //
    OrdinaryIrreducibleCharacter.twist K _ theta.1
      (localAut Q.1 (tau * MulAut.conj g) stable) = theta.1} = 2
  availability : LocalCanonicalAvailability iota
  compatibility : CanonicalLocalBlockCompatibility iota R.1.operations
  Dzero : DefectZeroReductionSource iota
  Tzero : TrivialWeightSource (p := 3) (X := G)
  Bzero : let _ := R.1.operations.ambientBlockData.fintypeBlock
    DefectZeroOrdinaryBlockSource iota
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
      R.1.operations.ambientBlockData.blocks Dzero
  Zzero : let _ := R.1.operations.ambientBlockData.fintypeBlock
    DefectZeroWeightSubgroupSource iota
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
      R.1.operations.ambientBlockData.blocks (R := R) Dzero
  dz : GlobalDefectZeroCharacter (p := 3) (K := K) (X := G)
  hdz : operationsBlock iota (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
    R (Dzero.reduce (iota := iota) dz) = roles 2
  hcenter : Subgroup.center G = ⊥
  principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} 3 k
  S9295 : Navarro9295BrauerRestrictionCoveringPrinciple 3 k K
  S9495 : Navarro9495BrauerCoveringPrinciple 3 k K
  S820 : Navarro820CyclicBrauerTwistPrinciple 3 k K
  fieldSource : SpathCoefficientField 3 k iota.prime
  ambientCatalogues :
    letI := R.1.operations.ambientBlockData.fintypeBlock
    letI : Invertible (Fintype.card (Subgroup.center G) : k) := centerlessCardInvertible hcenter
    ∀ phi : FaithfulIBr iota (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
      R.1.operations.ambientBlockData.blocks R ⟨⟩,
      letI : Fintype (ActualAutAmbient iota phi.val) := Fintype.ofFinite _
      actualBase iota phi.val ≠ ⊤ → UnselectedCatalogue (k := k) (A := ActualAutAmbient iota phi.val)
  ambientRoots :
    letI := R.1.operations.ambientBlockData.fintypeBlock
    letI : Invertible (Fintype.card (Subgroup.center G) : k) := centerlessCardInvertible hcenter
    ∀ phi : FaithfulIBr iota (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
      R.1.operations.ambientBlockData.blocks R ⟨⟩,
      Nonempty (PrimeRegularRootEmbedding 3 k K (ActualAutAmbient iota phi.val))
  positiveLocalInputs :
    letI := R.1.operations.ambientBlockData.fintypeBlock
    letI : Invertible (Fintype.card (Subgroup.center G) : k) := centerlessCardInvertible hcenter
    CenterlessPositiveLocalInputs iota (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
      R R.1.operations.ambientBlockData.blocks ⟨⟩

/-- Prove the local hypotheses and use them in the construction of the full
inductive condition for the centreless group. -/
theorem SourceInputs.rowsData
    (I : SourceInputs (SourceAction := SourceAction) (SourceBrauer := SourceBrauer)
      (SourceWeight := SourceWeight) iota R)
    : ∃ (Omega : IBr iota ≃ WeightClass (p := 3) (K := K) (X := G))
      (hOmega : ∀ (a : (MulAut G)ᵐᵒᵖ) (phi : IBr iota), Omega (a • phi) = a • Omega phi),
      (∀ phi, R.1.weightBlock (Omega phi) = operationsBlock iota
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) R phi) ∧
      CenterlessDefinition41Data iota
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
        R I.hcenter Omega hOmega I.Dzero I.Tzero := by
  have hsupport := Fi24ThreeLocal.radical_support iota R I.Q (I.roles 1) I.rows
    I.table I.rowBijective.1 I.weightCount
  have h := SporadicFi24P3Definition44NamedCarrierP3Definition41Assembly.p3_definition41_from_local_and_v3_sources
    (iota := iota) (R := R) (roles := I.roles) (AD := I.AD) (Bridge := I.Bridge)
    (hOuter := I.hOuter) (tau := I.tau) (htau := I.htau)
    (fixedNonprincipal := I.fixedNonprincipal) (fixedDefectZero := I.fixedDefectZero)
    (Dordinary := I.Dordinary) (selected := I.selected) (ordinaryComplete := I.ordinaryComplete)
    (representatives := I.representatives) (encoding := I.encoding)
    (V3 := literalV3Binding I.encoding) (ordinaryValues := I.ordinaryValues) (fusion := I.fusion)
    (Q := I.Q) (support := hsupport) (rows := I.rows) (rowBijective := I.rowBijective)
    (S414 := Fi24ThreeLocal.intervalSource R I.Q)
    (evaluation := Fi24ThreeLocal.intervalEvaluation_one R I.Q (I.roles 1) I.rows I.table)
    (g := I.g) (stable := I.stable) (localFixed := I.localFixed)
    (availability := I.availability) (compatibility := I.compatibility)
    (Dzero := I.Dzero) (Tzero := I.Tzero) (Bzero := I.Bzero) (Zzero := I.Zzero)
    (dz := I.dz) (hdz := I.hdz) I.hcenter I.principle I.S9295 I.S9495 I.S820 I.fieldSource
    I.ambientCatalogues I.ambientRoots I.positiveLocalInputs
  rcases h with ⟨Omega, hOmega, hblock, _, e, hFamily, _, _, _, _, _, _, _, _, _, hdata⟩
  exact ⟨Omega, hOmega, hblock, hdata⟩

/-- Compatible root choices for the same matching produced by the block
calculation. This is an explicit additional source requirement. It does
not require agreement of arbitrarily chosen root correspondences. -/
def SourceInputs.RootCompatibility
    (I : SourceInputs (SourceAction := SourceAction) (SourceBrauer := SourceBrauer)
      (SourceWeight := SourceWeight) iota R) : Prop :=
  let h := I.rowsData iota R
  let Omega := Classical.choose h
  let hOmega := Classical.choose (Classical.choose_spec h)
  ModularRep.PaperProofs.CoherentCenterlessRows.CoherentOriginalRowsOutput iota
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) R I.hcenter Omega hOmega

/-- The raw block calculation gives the full certificate when compatible
root choices for that matching have also been supplied. -/
theorem SourceInputs.complete
    (I : SourceInputs (SourceAction := SourceAction) (SourceBrauer := SourceBrauer)
      (SourceWeight := SourceWeight) iota R)
    (Cover : EllPrimeCoverSource 3 G) (roots : I.RootCompatibility iota R) :
    Definition41Certificate iota R Cover := by
  let h := I.rowsData iota R
  let Omega := Classical.choose h
  let hOmega := Classical.choose (Classical.choose_spec h)
  have hdata := Classical.choose_spec (Classical.choose_spec h)
  exact of_centerless_rows iota R Cover I.Dzero I.Tzero I.hcenter Omega hOmega
    hdata.1 hdata.2 roots

/-- A fixed named case and its stated assumptions, before any proof of the
complete block condition is constructed. -/
structure Inputs (base : NamedBase.{u}) where
  model : CaseModel base 3
  SourceAction : Type u
  SourceBrauer : Type u
  SourceWeight : Type u
  [sourceGroup : Group SourceAction]
  [sourceBrauerAction : MulAction SourceAction SourceBrauer]
  [sourceWeightAction : MulAction SourceAction SourceWeight]
  source : SourceInputs (SourceAction := SourceAction) (SourceBrauer := SourceBrauer)
    (SourceWeight := SourceWeight) model.iota model.R
  rootCompatibility : source.RootCompatibility model.iota model.R

attribute [instance] Inputs.sourceGroup Inputs.sourceBrauerAction Inputs.sourceWeightAction

theorem Inputs.complete {base : NamedBase.{u}} (I : Inputs base) : CaseConclusion I.model :=
  I.source.complete I.model.iota I.model.R I.model.Cover I.rootCompatibility

end ManuscriptIBAW.Sporadic.Fi24Three

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
