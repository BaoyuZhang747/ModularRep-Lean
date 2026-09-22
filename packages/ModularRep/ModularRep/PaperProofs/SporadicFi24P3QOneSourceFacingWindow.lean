import ModularRep.PaperProofs.SporadicFi24Definition35Operations
import ModularRep.PaperProofs.SporadicFi24P3PlusRankSourceFacingComposite
import ModularRep.PaperProofs.SporadicFi24P3QOneExtensionBlockObligationsFromSources
import ModularRep.PaperProofs.SporadicFi24P3SourceFacingComposite

/-!
# A source-facing `Q = 1` extension and block window for `Fi'_{24}`

This module joins the source-facing Fischer correspondence to the concrete
Definition 3.5 extension carriers in the trivial-radical branch.  For each
defect-zero datum it constructs the relevant Definition 3.5 block problem
directly from the same literal carrier used by the global correspondence.
The selected Brauer character is the canonical reduction and the selected
weight is the literal weight at the trivial subgroup.

There are two block catalogues in the join.  The global correspondence uses
an arbitrary complete block decomposition, whereas the Definition 3.5
problem uses the operations catalogue of the literal carrier.  Their block
indices are not definitionally equal.  The first theorem below proves the
required equality of literal primitive idempotents: both catalogues select
the idempotent acting as the identity on the same simple module.  No carrier
equality is assumed.

The remaining inputs below the global endpoint are the quotient character,
quotient weight, local inflation, ambient group, cyclic-extension principle,
cyclicity and fixedness, root compatibility, local character compatibility,
and one global block catalogue at every intermediate subgroup.  The common
cyclic extension, its global and local transports, and every intermediate
block equality are constructed.  No `Q = 1` normalisation, abstract
compatible-extension predicate, abstract intermediate-block-equality
predicate, BAW/iBAW assertion, or final Definition 4.1 predicate is assumed.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3QOneSourceFacingWindow

open Formalisation
open ModularRep
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.ComputationTranscriptAdditionalBindings
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SpathQOneCharacterExtensions
open ModularRep.PaperProofs.SpathQOneIntermediateBlockTransport
open ModularRep.PaperProofs.SporadicFi24C2OuterActionFromNonprincipalCensus
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24Definition35Operations
open ModularRep.PaperProofs.SporadicFi24KnownFibreBridgeActual
open ModularRep.PaperProofs.SporadicFi24P3AnDietrichSourceCertificate
open ModularRep.PaperProofs.SporadicFi24P3BlockIndexBindingFromCardinality
open ModularRep.PaperProofs.SporadicFi24P3LiteralSpanBindingConstruction
open ModularRep.PaperProofs.SporadicFi24P3NamedTableCentralCharacterAdapter
open ModularRep.PaperProofs.SporadicFi24P3NonprincipalCensusFromSources
open ModularRep.PaperProofs.SporadicFi24P3NonprincipalWeightCoverageFromLocalCensus
open ModularRep.PaperProofs.SporadicFi24P3PlusRankLiteralBridge
open ModularRep.PaperProofs.SporadicFi24P3PlusRankReplayContract
open ModularRep.PaperProofs.SporadicFi24P3PlusRankSourceFacingComposite
open ModularRep.PaperProofs.SporadicFi24P3QOneExtensionBlockObligationsFromSources
open ModularRep.PaperProofs.SporadicFi24P3QSquaredLocalTableSource
open ModularRep.PaperProofs.SporadicFi24P3SourceFacingComposite
open ModularRep.PaperProofs.SporadicFi24P3ThreeBlockSourceFromSources
open ModularRep.PaperProofs.SporadicFi24QOneNormalisationActual
open ModularRep.PaperProofs.SporadicFi24SelectedOuterInvolutionCarrier
open ModularRep.PaperProofs.SporadicFi24ThreeBlockAutomorphismPromotionActual
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual

universe u

/-! ## The literal block-carrier join -/

section LiteralCarrierJoin

variable {p : ℕ} {k K X BlockIndex : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X] [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}

/-- The operations catalogue of a literal carrier and any other complete
block catalogue assign the same *literal primitive idempotent* to a Brauer
character.  This is the carrier bridge needed below; it is not an equality
between the two index types or between the two decompositions. -/
theorem literalOperations_brauerBlock_eq
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (R : LiteralCarrierAdapter
      (p := p) (k := k) (K := K) (X := X))
    (phi : IBr iota) :
    let O := R.1.operations
    letI : Fintype (ActualBlock (k := k) (X := X)) :=
      O.ambientBlockData.fintypeBlock
    irreducibleBrauerCharacterBlock iota hinj
        O.ambientBlockData.blocks phi =
      brauerBlock iota hinj blocks phi := by
  dsimp only
  let O := R.1.operations
  letI : Fintype (ActualBlock (k := k) (X := X)) :=
    O.ambientBlockData.fintypeBlock
  let C := (simpleModuleClassEquivIBr iota hinj).symm phi
  let V := Representation.asModule (simpleClassFDRep C).ρ
  letI : IsSimpleModule k[X] V :=
    simple_iff_isSimpleModule.mp (simpleClassFDRep_underlying_simple C)
  change
    O.ambientBlockData.blocks.moduleBlock (V := V) =
      actualBlockOfIndex blocks (blocks.moduleBlock (V := V))
  symm
  apply O.ambientBlockData.blocks.moduleBlock_eq_of_smul_eq_self
  intro v
  rw [R.2]
  exact blocks.moduleBlock_smul (V := V) v

/-! ## Canonical Definition 3.5 carriers for the defect-zero data -/

/-- Only the action presentation and selected local reductions needed to
form the literal Definition 3.5 problems.  The block for `d` is fixed to the
literal block of its canonical Brauer reduction. -/
structure QOneDefinition35CarrierSources
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (R : LiteralCarrierAdapter
      (p := p) (k := k) (K := K) (X := X))
    (D : DefectZeroReductionSource iota) where
  Gamma : Type u
  [groupGamma : Group Gamma]
  [finiteGamma : Finite Gamma]
  gamma : Gamma →* MulAut X
  gammaBlock_fixed : ∀
      (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X))
      (a : Gamma),
    inverseOpHom gamma a •
        brauerBlock iota hinj blocks (D.reduce (iota := iota) d) =
      brauerBlock iota hinj blocks (D.reduce (iota := iota) d)
  localReduction : ∀
      (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X))
      (w : LiteralWeightFibre R.1
        (brauerBlock iota hinj blocks (D.reduce (iota := iota) d))),
    SelectedLocalReductionSource R.1
      (brauerBlock iota hinj blocks (D.reduce (iota := iota) d)) w

attribute [instance]
  QOneDefinition35CarrierSources.groupGamma
  QOneDefinition35CarrierSources.finiteGamma

/-- The literal Definition 3.5 problem attached to one defect-zero datum. -/
def qOneDefinition35Problem
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (R : LiteralCarrierAdapter
      (p := p) (k := k) (K := K) (X := X))
    (D : DefectZeroReductionSource iota)
    (Carrier : QOneDefinition35CarrierSources iota hinj blocks R D)
    (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X)) :
    Definition35Problem :=
  literalDefinition35Problem iota hinj R
    (brauerBlock iota hinj blocks (D.reduce (iota := iota) d))
    Carrier.gamma (Carrier.gammaBlock_fixed d) (Carrier.localReduction d)

/-- The canonical reduction, regarded as a Brauer character in the literal
Definition 3.5 block fibre. -/
def qOneDefinition35Brauer
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (R : LiteralCarrierAdapter
      (p := p) (k := k) (K := K) (X := X))
    (D : DefectZeroReductionSource iota)
    (Carrier : QOneDefinition35CarrierSources iota hinj blocks R D)
    (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X)) :
    Definition35Brauer
      (qOneDefinition35Problem iota hinj blocks R D Carrier d) :=
  ⟨D.reduce (iota := iota) d,
    literalOperations_brauerBlock_eq iota hinj blocks R
      (D.reduce (iota := iota) d)⟩

/-- The canonical weight at the trivial subgroup, regarded as a weight in
the same literal Definition 3.5 block fibre. -/
def qOneDefinition35Weight
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (R : LiteralCarrierAdapter
      (p := p) (k := k) (K := K) (X := X))
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource p X)
    (C : TrivialWeightBlockCompatibility iota hinj blocks R D T)
    (Carrier : QOneDefinition35CarrierSources iota hinj blocks R D)
    (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X)) :
    Definition35Weight
      (qOneDefinition35Problem iota hinj blocks R D Carrier d) :=
  ⟨T.atOne d, C.block_atOne d⟩

/-! ## Lower sources and their concrete derived records -/

/-- The lower source packet for one already selected canonical `Q = 1`
pair.  Its final field contains only the global half of every intermediate
block packet. -/
structure QOneCyclicExtensionBlockSources
    {P : Definition35Problem.{u}}
    (T : TrivialWeightSource P.p P.H)
    (d : GlobalDefectZeroCharacter
      (p := P.p) (K := P.K) (X := P.H))
    (psi : Definition35Brauer P)
    (w : Definition35Weight P)
    (hw : w.1 = T.atOne d) where
  reference : Definition35Brauer P
  quotient : CentralQuotientBrauerSource P reference psi
  weight : QuotientWeightBrauerSource P reference w
  localInflation : QuotientLocalInflationSource P reference w weight
  ambient : SpathAmbientGroup P reference psi quotient
  principle :
    Representation.BrauerCyclicExtensionPrinciple.{u, u, u} P.p P.k
  quotientCyclic : IsCyclic (ambient.A ⧸ ambient.base)
  fixed : ∀ a : ambient.A,
    IrreducibleBrauerCharacter.twist
        (quotient.iota.alongMulEquiv ambient.baseEquiv)
        (IrreducibleBrauerCharacter.alongMulEquiv quotient.iota
          ambient.baseEquiv quotient.brauer)
        (MulAut.conjNormal a) =
      IrreducibleBrauerCharacter.alongMulEquiv quotient.iota
        ambient.baseEquiv quotient.brauer
  ambientRoot : PrimeRegularRootEmbedding P.p P.k P.K ambient.A
  lift : (quotient.iota.alongMulEquiv ambient.baseEquiv).lift =
    ambientRoot.lift
  localBrauerCompatibility :
    PrimeRegularClassFunction.pullback
        (qOneAmbientBaseEquiv ambient
          (quotientRadical_eq_bot_of_weight_eq_atOne
            P reference w T d hw)).symm.toMonoidHom
        (IrreducibleBrauerCharacter.alongMulEquiv quotient.iota
          ambient.baseEquiv quotient.brauer).1 =
      (IrreducibleBrauerCharacter.alongMulEquiv localInflation.iota
        (canonicalLocalBaseEquiv ambient) localInflation.brauer).1
  globalBlocks : QOneIntermediateGlobalBlockSource
    (characterExtensionsOfWeightEqAtOneFromCyclicSources
      localInflation ambient T d hw principle quotientCyclic fixed
        ambientRoot lift localBrauerCompatibility)

namespace QOneCyclicExtensionBlockSources

variable {P : Definition35Problem.{u}}
variable {T : TrivialWeightSource P.p P.H}
variable {d : GlobalDefectZeroCharacter
  (p := P.p) (K := P.K) (X := P.H)}
variable {psi : Definition35Brauer P}
variable {w : Definition35Weight P}
variable {hw : w.1 = T.atOne d}

/-- The single common extension selected from the cyclic-extension theorem. -/
noncomputable def common
    (S : QOneCyclicExtensionBlockSources T d psi w hw) :
    LiveQOneCommonExtensionData S.ambient :=
  commonExtensionOfCyclicSources S.ambient S.principle
    S.quotientCyclic S.fixed

/-- The local transport data forced by the canonical weight at `Q = 1`. -/
def localData (S : QOneCyclicExtensionBlockSources T d psi w hw) :
    QOneLocalTransportData S.localInflation S.ambient :=
  localTransportDataOfWeightEqAtOne S.localInflation S.ambient T d hw
    S.localBrauerCompatibility

/-- The concrete global and local extensions obtained from one common cyclic
extension. -/
noncomputable def extensions
    (S : QOneCyclicExtensionBlockSources T d psi w hw) :
    SpathCharacterExtensions P S.reference psi w S.quotient S.weight
      S.localInflation S.ambient :=
  characterExtensionsOfWeightEqAtOneFromCyclicSources
    S.localInflation S.ambient T d hw S.principle S.quotientCyclic S.fixed
      S.ambientRoot S.lift S.localBrauerCompatibility

/-- All intermediate block equalities, transported from the global halves
stored in the lower packet. -/
noncomputable def intermediateBlocks
    (S : QOneCyclicExtensionBlockSources T d psi w hw) :
    IntermediateBlockSource P S.reference psi w S.quotient S.weight
      S.localInflation S.ambient S.extensions :=
  intermediateBlockSourceOfWeightEqAtOneFromGlobal
    S.localInflation S.ambient T d hw S.common S.ambientRoot S.lift
      S.localBrauerCompatibility S.globalBlocks

end QOneCyclicExtensionBlockSources

/-- The concrete output for one `Q = 1` pair.  The two equality fields make
explicit that the returned records are the records constructed from the
lower cyclic and transport sources, not unrelated inhabitants of the same
types. -/
structure DerivedQOneExtensionBlockData
    {P : Definition35Problem.{u}}
    {T : TrivialWeightSource P.p P.H}
    {d : GlobalDefectZeroCharacter
      (p := P.p) (K := P.K) (X := P.H)}
    {psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {hw : w.1 = T.atOne d}
    (S : QOneCyclicExtensionBlockSources T d psi w hw) where
  common : LiveQOneCommonExtensionData S.ambient
  globalLocalExtensions :
    SpathCharacterExtensions P S.reference psi w S.quotient S.weight
      S.localInflation S.ambient
  common_from_cyclicSources : common = S.common
  extensions_from_common : globalLocalExtensions = S.extensions
  intermediateBlocks :
    IntermediateBlockSource P S.reference psi w S.quotient S.weight
      S.localInflation S.ambient globalLocalExtensions
  intermediateBlocks_from_globalSources :
    HEq intermediateBlocks S.intermediateBlocks

/-- Construct the concrete common extension, its global/local transports,
and all intermediate block equalities from the lower packet. -/
noncomputable def derivedQOneExtensionBlockData
    {P : Definition35Problem.{u}}
    {T : TrivialWeightSource P.p P.H}
    {d : GlobalDefectZeroCharacter
      (p := P.p) (K := P.K) (X := P.H)}
    {psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {hw : w.1 = T.atOne d}
    (S : QOneCyclicExtensionBlockSources T d psi w hw) :
    DerivedQOneExtensionBlockData S where
  common := S.common
  globalLocalExtensions := S.extensions
  common_from_cyclicSources := rfl
  extensions_from_common := rfl
  intermediateBlocks := S.intermediateBlocks
  intermediateBlocks_from_globalSources := HEq.rfl

namespace DerivedQOneExtensionBlockData

variable {P : Definition35Problem.{u}}
variable {T : TrivialWeightSource P.p P.H}
variable {d : GlobalDefectZeroCharacter
  (p := P.p) (K := P.K) (X := P.H)}
variable {psi : Definition35Brauer P}
variable {w : Definition35Weight P}
variable {hw : w.1 = T.atOne d}
variable {S : QOneCyclicExtensionBlockSources T d psi w hw}

/-- The derived `Q = 1` data satisfy the Späth condition for the matched
character and weight. The extensions and intermediate blocks are those
already provided by `D`, so the construction requires no additional
extensions or block assumptions. -/
noncomputable def toSpathMatchedBlockCondition
    (D : DerivedQOneExtensionBlockData S) :
    SpathMatchedBlockCondition P S.reference psi w where
  quotient := S.quotient
  tail :=
    { weight := S.weight
      localInflation := S.localInflation
      ambient := S.ambient
      extensions := D.globalLocalExtensions
      intermediateBlocks := D.intermediateBlocks }

@[simp] theorem toSpathMatchedBlockCondition_quotient
    (D : DerivedQOneExtensionBlockData S) :
    D.toSpathMatchedBlockCondition.quotient = S.quotient := rfl

@[simp] theorem toSpathMatchedBlockCondition_extensions
    (D : DerivedQOneExtensionBlockData S) :
    D.toSpathMatchedBlockCondition.extensions =
      D.globalLocalExtensions := rfl

@[simp] theorem toSpathMatchedBlockCondition_intermediateBlocks
    (D : DerivedQOneExtensionBlockData S) :
    D.toSpathMatchedBlockCondition.intermediateBlocks =
      D.intermediateBlocks := rfl

end DerivedQOneExtensionBlockData

/-- A provenance-retaining downstream realisation of the concrete Spath
matched-block package.  The equality prevents the packaged condition from
being replaced by an unrelated inhabitant of the same target type. -/
structure DerivedQOneSpathMatchedBlockData
    {P : Definition35Problem.{u}}
    {T : TrivialWeightSource P.p P.H}
    {d : GlobalDefectZeroCharacter
      (p := P.p) (K := P.K) (X := P.H)}
    {psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {hw : w.1 = T.atOne d}
    (S : QOneCyclicExtensionBlockSources T d psi w hw) where
  derived : DerivedQOneExtensionBlockData S
  matched : SpathMatchedBlockCondition P S.reference psi w
  matched_from_derived :
    matched = derived.toSpathMatchedBlockCondition

/-- Construct the Spath matched-block package without adding any extension,
intermediate-block, or target-predicate premise. -/
noncomputable def derivedQOneSpathMatchedBlockData
    {P : Definition35Problem.{u}}
    {T : TrivialWeightSource P.p P.H}
    {d : GlobalDefectZeroCharacter
      (p := P.p) (K := P.K) (X := P.H)}
    {psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {hw : w.1 = T.atOne d}
    (S : QOneCyclicExtensionBlockSources T d psi w hw) :
    DerivedQOneSpathMatchedBlockData S where
  derived := derivedQOneExtensionBlockData S
  matched := (derivedQOneExtensionBlockData S).toSpathMatchedBlockCondition
  matched_from_derived := rfl

end LiteralCarrierJoin

/-! ## The joined source-facing window -/

variable {SourceAction SourceBrauer SourceWeight : Type u}
variable [Group SourceAction]
variable [MulAction SourceAction SourceBrauer]
variable [MulAction SourceAction SourceWeight]

variable {k K X BlockIndex : Type u}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X] [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}

noncomputable local instance centerFintype :
    Fintype (Subgroup.center X) :=
  Fintype.ofFinite _

variable [Invertible (Fintype.card (Subgroup.center X) : k)]

/-- The source-facing global endpoint together with the complete concrete
`Q = 1` extension and intermediate-block data for every defect-zero datum.

The selected Definition 3.5 weight has underlying literal weight
`T.atOne d`; the endpoint theorem proves that this is precisely
`Omega (D.reduce d)`. -/
theorem exists_sourceFacingOmega_with_qOne_extensionBlocks
    (iota : PrimeRegularRootEmbedding 3 k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (R : LiteralCarrierAdapter
      (p := 3) (k := k) (K := K) (X := X))
    (E1 : RoutineTransportInput iota hinj blocks R)
    (AD : AnDietrichFi24P3SourceCertificate
      (SourceAction := SourceAction)
      (SourceBrauer := SourceBrauer)
      (SourceWeight := SourceWeight))
    (Bridge : AnDietrichFi24P3LiteralCarrierBridge
      (SourceAction := SourceAction)
      (SourceBrauer := SourceBrauer)
      (SourceWeight := SourceWeight) (k := k) (K := K) (X := X) iota)
    (hCenter : Subgroup.center X = ⊥)
    (Involution : SelectedOuterInvolutionCarrier X)
    (BlockBinding : Fi24P3BlockIndexBinding BlockIndex)
    (BlockAction : Fi24P3SelectedOuterBlockActionBinding
      blocks Involution BlockBinding)
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource 3 X)
    (DefectZeroCompatibility :
      TrivialWeightBlockCompatibility iota hinj blocks R D T)
    (DefectZeroBlocks : DefectZeroOrdinaryBlockSource iota hinj blocks D)
    (DefectZeroSubgroups :
      DefectZeroWeightSubgroupSource iota hinj blocks (R := R) D)
    (DefectZeroIdentification :
      Fi24DefectZeroBlockIdentification iota hinj blocks D
        (fi24ThreeBlockSourceOfBindings
          blocks Involution BlockBinding BlockAction))
    (RestrictionBinding :
      BrauerRestrictionSpaceBinding iota hinj blocks
        (fi24ThreeBlockSourceOfBindings
          blocks Involution BlockBinding BlockAction))
    (BrauerAlignment :
      Fi24P3NonprincipalBrauerComputationAlignment iota hinj blocks
        (fi24ThreeBlockSourceOfBindings
          blocks Involution BlockBinding BlockAction)
        RestrictionBinding)
    (Q : Subgroup X)
    (table : Source Q
      (R.1.operations.toLocalNormalizerBlockOperations Q))
    (S414 : PhaseASource R Q table)
    (TableBlockMatch : Fi24P3NamedTableIntervalCentralCharacterMatch
      R
        (fi24ThreeBlockSourceOfBindings
          blocks Involution BlockBinding BlockAction).nonprincipalBlock
        Q table)
    (LocalCensus : Fi24P3LocalDefectZeroCensusBinding R Q table)
    (RadicalSupport : Fi24P3NonprincipalRadicalSupportSource
      R
        (fi24ThreeBlockSourceOfBindings
          blocks Involution BlockBinding BlockAction)
        Q table)
    (WeightActionAlignment :
      Fi24P3NonprincipalTable8ActionAlignment
        R
          (fi24ThreeBlockSourceOfBindings
            blocks Involution BlockBinding BlockAction)
          Q table S414 TableBlockMatch
          (nonprincipalWeightCoverage_of_localCensus_and_radicalSupport
            R
              (fi24ThreeBlockSourceOfBindings
                blocks Involution BlockBinding BlockAction)
              Q table LocalCensus RadicalSupport))
    (hOuterQuotientCard :
      Nat.card
        ((MulAut X)ᵐᵒᵖ ⧸
          (RepresentationWeight.innerInverseOpHom (G := X)).range) = 2)
    (Carrier : QOneDefinition35CarrierSources
      iota hinj blocks R D)
    (Lower : ∀ d :
        GlobalDefectZeroCharacter (p := 3) (K := K) (X := X),
      QOneCyclicExtensionBlockSources
        T d
        (qOneDefinition35Brauer iota hinj blocks R D Carrier d)
        (qOneDefinition35Weight iota hinj blocks R D T
          DefectZeroCompatibility Carrier d)
        rfl) :
    ∃ Omega : IBr iota ≃ WeightClass (p := 3) (K := K) (X := X),
      (∀ (alpha : (MulAut X)ᵐᵒᵖ) (phi : IBr iota),
        Omega (alpha • phi) = alpha • Omega phi) ∧
      (∀ phi,
        R.1.weightBlock (Omega phi) =
          brauerBlock iota hinj blocks phi) ∧
      (∀ d : GlobalDefectZeroCharacter (p := 3) (K := K) (X := X),
        Omega (D.reduce (iota := iota) d) = T.atOne d) ∧
      (∀ d : GlobalDefectZeroCharacter (p := 3) (K := K) (X := X),
        let psi := qOneDefinition35Brauer
          iota hinj blocks R D Carrier d
        let w := qOneDefinition35Weight
          iota hinj blocks R D T DefectZeroCompatibility Carrier d
        psi.1 = D.reduce (iota := iota) d ∧
          w.1 = Omega (D.reduce (iota := iota) d) ∧
          Nonempty (@DerivedQOneExtensionBlockData
            (qOneDefinition35Problem iota hinj blocks R D Carrier d)
            T d psi w rfl (Lower d))) := by
  obtain ⟨Omega, hOmega, hblock, hqOne⟩ :=
    exists_blockPreservingAutEquivariantEquiv_with_qOne_from_narrow_sources
      (R := R) iota hinj blocks E1 AD Bridge hCenter Involution BlockBinding
        BlockAction D T DefectZeroCompatibility DefectZeroBlocks
        DefectZeroSubgroups DefectZeroIdentification RestrictionBinding
        BrauerAlignment Q table S414 TableBlockMatch LocalCensus RadicalSupport
        WeightActionAlignment hOuterQuotientCard
  refine ⟨Omega, hOmega, hblock, hqOne, ?_⟩
  intro d
  dsimp only [qOneDefinition35Brauer, qOneDefinition35Weight]
  exact ⟨rfl, (hqOne d).symm,
    ⟨@derivedQOneExtensionBlockData
      (qOneDefinition35Problem iota hinj blocks R D Carrier d)
      T d
      (qOneDefinition35Brauer iota hinj blocks R D Carrier d)
      (qOneDefinition35Weight iota hinj blocks R D T
        DefectZeroCompatibility Carrier d)
      rfl (Lower d)⟩⟩

/-- The same `Q = 1` extension-and-block window over the narrower plus-rank
source-facing composite.  The block-role binding is reconstructed from the
block injection, while the aggregate nonprincipal Brauer alignment is
reconstructed by the replay source and literal binding; the replay now
proves both required ranks internally.  The final field retains both the
derived cyclic-source record and its concrete Spath matched-block
reorganisation. -/
theorem exists_sourceFacingOmega_with_qOne_spathMatchedBlocks_from_plus_rank_sources
    (iota : PrimeRegularRootEmbedding 3 k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (R : LiteralCarrierAdapter
      (p := 3) (k := k) (K := K) (X := X))
    (E1 : RoutineTransportInput iota hinj blocks R)
    (AD : AnDietrichFi24P3SourceCertificate
      (SourceAction := SourceAction)
      (SourceBrauer := SourceBrauer)
      (SourceWeight := SourceWeight))
    (Bridge : AnDietrichFi24P3LiteralCarrierBridge
      (SourceAction := SourceAction)
      (SourceBrauer := SourceBrauer)
      (SourceWeight := SourceWeight) (k := k) (K := K) (X := X) iota)
    (hCenter : Subgroup.center X = ⊥)
    (Involution : SelectedOuterInvolutionCarrier X)
    (BlockInjection : Fi24P3BlockIndexInjectionSource BlockIndex)
    (BlockAction : Fi24P3SelectedOuterBlockActionBinding
      blocks Involution BlockInjection.toBlockIndexBinding)
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource 3 X)
    (DefectZeroCompatibility :
      TrivialWeightBlockCompatibility iota hinj blocks R D T)
    (DefectZeroBlocks : DefectZeroOrdinaryBlockSource iota hinj blocks D)
    (DefectZeroSubgroups :
      DefectZeroWeightSubgroupSource iota hinj blocks (R := R) D)
    (DefectZeroIdentification :
      Fi24DefectZeroBlockIdentification iota hinj blocks D
        (fi24ThreeBlockSourceOfBindings
          blocks Involution BlockInjection.toBlockIndexBinding BlockAction))
    (RestrictionBinding :
      BrauerRestrictionSpaceBinding iota hinj blocks
        (fi24ThreeBlockSourceOfBindings
          blocks Involution BlockInjection.toBlockIndexBinding BlockAction))
    (Replay : Fi24P3PlusRankReplaySource K)
    (LiteralBinding :
      Fi24P3PlusRankLiteralBinding iota hinj blocks
        (fi24ThreeBlockSourceOfBindings
          blocks Involution BlockInjection.toBlockIndexBinding BlockAction)
        RestrictionBinding Replay)
    (Q : Subgroup X)
    (table : Source Q
      (R.1.operations.toLocalNormalizerBlockOperations Q))
    (S414 : PhaseASource R Q table)
    (TableBlockMatch : Fi24P3NamedTableIntervalCentralCharacterMatch
      R
        (fi24ThreeBlockSourceOfBindings
          blocks Involution BlockInjection.toBlockIndexBinding
            BlockAction).nonprincipalBlock
        Q table)
    (LocalCensus : Fi24P3LocalDefectZeroCensusBinding R Q table)
    (RadicalSupport : Fi24P3NonprincipalRadicalSupportSource
      R
        (fi24ThreeBlockSourceOfBindings
          blocks Involution BlockInjection.toBlockIndexBinding BlockAction)
        Q table)
    (WeightActionAlignment :
      Fi24P3NonprincipalTable8ActionAlignment
        R
          (fi24ThreeBlockSourceOfBindings
            blocks Involution BlockInjection.toBlockIndexBinding BlockAction)
          Q table S414 TableBlockMatch
          (nonprincipalWeightCoverage_of_localCensus_and_radicalSupport
            R
              (fi24ThreeBlockSourceOfBindings
                blocks Involution BlockInjection.toBlockIndexBinding BlockAction)
              Q table LocalCensus RadicalSupport))
    (hOuterQuotientCard :
      Nat.card
        ((MulAut X)ᵐᵒᵖ ⧸
          (RepresentationWeight.innerInverseOpHom (G := X)).range) = 2)
    (Carrier : QOneDefinition35CarrierSources
      iota hinj blocks R D)
    (Lower : ∀ d :
        GlobalDefectZeroCharacter (p := 3) (K := K) (X := X),
      QOneCyclicExtensionBlockSources
        T d
        (qOneDefinition35Brauer iota hinj blocks R D Carrier d)
        (qOneDefinition35Weight iota hinj blocks R D T
          DefectZeroCompatibility Carrier d)
        rfl) :
    ∃ Omega : IBr iota ≃ WeightClass (p := 3) (K := K) (X := X),
      (∀ (alpha : (MulAut X)ᵐᵒᵖ) (phi : IBr iota),
        Omega (alpha • phi) = alpha • Omega phi) ∧
      (∀ phi,
        R.1.weightBlock (Omega phi) =
          brauerBlock iota hinj blocks phi) ∧
      (∀ d : GlobalDefectZeroCharacter (p := 3) (K := K) (X := X),
        Omega (D.reduce (iota := iota) d) = T.atOne d) ∧
      (∀ d : GlobalDefectZeroCharacter (p := 3) (K := K) (X := X),
        let psi := qOneDefinition35Brauer
          iota hinj blocks R D Carrier d
        let w := qOneDefinition35Weight
          iota hinj blocks R D T DefectZeroCompatibility Carrier d
        psi.1 = D.reduce (iota := iota) d ∧
          w.1 = Omega (D.reduce (iota := iota) d) ∧
          Nonempty (@DerivedQOneSpathMatchedBlockData
            (qOneDefinition35Problem iota hinj blocks R D Carrier d)
            T d psi w rfl (Lower d))) := by
  obtain ⟨Omega, hOmega, hblock, hqOne⟩ :=
    exists_blockPreservingAutEquivariantEquiv_with_qOne_from_plus_rank_sources
      (R := R) iota hinj blocks E1 AD Bridge hCenter Involution
        BlockInjection BlockAction D T DefectZeroCompatibility
        DefectZeroBlocks DefectZeroSubgroups DefectZeroIdentification
        RestrictionBinding Replay LiteralBinding Q table S414
        TableBlockMatch LocalCensus RadicalSupport
        WeightActionAlignment hOuterQuotientCard
  refine ⟨Omega, hOmega, hblock, hqOne, ?_⟩
  intro d
  dsimp only [qOneDefinition35Brauer, qOneDefinition35Weight]
  exact ⟨rfl, (hqOne d).symm,
    ⟨@derivedQOneSpathMatchedBlockData
      (qOneDefinition35Problem iota hinj blocks R D Carrier d)
      T d
      (qOneDefinition35Brauer iota hinj blocks R D Carrier d)
      (qOneDefinition35Weight iota hinj blocks R D T
        DefectZeroCompatibility Carrier d)
      rfl (Lower d)⟩⟩

end ModularRep.PaperProofs.SporadicFi24P3QOneSourceFacingWindow


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
