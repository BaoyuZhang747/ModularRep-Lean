import ModularRep.PaperProofs.SporadicFi24P3PositiveQExtensionBlockObligationsJoin
import ModularRep.PaperProofs.SporadicFi24P3QOneSourceFacingWindow

/-!
# A concrete matched-pair construction window for `Fi'_{24}` at `p = 3`

The manuscript treats the trivial-radical pairs by the normalised `Q = 1`
map, the four weights in the unique nonprincipal positive-defect block by the
`Q \cong C_3^2` table, and obtains the principal-block bijection by block
cancellation.  The first two branches have concrete extension and
intermediate-block packets in the current library; cancellation alone does
not provide such a packet for a principal-block weight.

This module records that exact boundary.  The three-block catalogue gives an
explicit exhaustive block split.  Trivial-radical completeness comes from the
canonical `atOne` theorem.  In the positive-radical case, the selected
defect-zero block is impossible by its singleton Brauer fibre, while the
nonprincipal block is covered by a named table row using the local census and
radical-support certificates.  Hence every matched pair has one of three
concrete outcomes:

* a provenance-retaining `Q = 1` Spath matched-block packet;
* a named-row, positive-`Q`, nonprincipal Spath matched-block packet; or
* an explicitly unresolved positive-radical principal-block pair.

No arbitrary compatible-extension predicate, intermediate-block predicate,
character-triple predicate, BAW/iBAW predicate, final Definition 4.1
predicate, or assumed case split occurs below.  In particular this is the
closest concrete analogue of `SpathLemma61Input` supported by the present
source data: that generic record is parametrised by two opaque propositions
and therefore cannot be populated from these concrete records without an
additional semantic bridge.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3MatchedPairAssemblyWindow

open Formalisation
open ModularRep
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.NavarroBrauerRestrictionCovering
open ModularRep.NavarroCoveringBrauerExtension
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SpathPositiveQBaseBlock
open ModularRep.PaperProofs.SpathPositiveQTopBlockChoice
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24Definition35Operations
open ModularRep.PaperProofs.SporadicFi24KnownFibreBridgeActual
open ModularRep.PaperProofs.SporadicFi24P3NamedTableLiteralWeightRows
open ModularRep.PaperProofs.SporadicFi24P3NonprincipalCensusFromSources
open ModularRep.PaperProofs.SporadicFi24P3NonprincipalWeightCoverageFromLocalCensus
open ModularRep.PaperProofs.SporadicFi24P3PositiveQBaseInductionTransport
open ModularRep.PaperProofs.SporadicFi24P3PositiveQExtensionBlockObligationsFromSources
open ModularRep.PaperProofs.SporadicFi24P3PositiveQExtensionBlockObligationsJoin
open ModularRep.PaperProofs.SporadicFi24P3QOneSourceFacingWindow
open ModularRep.PaperProofs.SporadicFi24P3QSquaredLocalTableSource
open ModularRep.PaperProofs.SporadicFi24QOneNormalisationActual
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual
open ModularRep.PaperProofs.SporadicFi24ThreeBlockQOneNormalisationActual

universe u

/-! ## Concrete positive-radical output from the cyclic packet -/

/-- The exact lower positive-radical sources for one already selected pair.
The final field is the narrowed from-base cyclic packet; it contains no
chosen top block or final matched-block condition. -/
structure PositiveQExtensionBlockSources
    {P : Definition35Problem.{u}}
    (psi : Definition35Brauer P)
    (w : Definition35Weight P) where
  reference : Definition35Brauer P
  quotient : CentralQuotientBrauerSource P reference psi
  weight : QuotientWeightBrauerSource P reference w
  localInflation : QuotientLocalInflationSource P reference w weight
  ambient : SpathAmbientGroup P reference psi quotient
  S9295 : Navarro9295BrauerRestrictionCoveringPrinciple P.p P.k P.K
  S9495 : Navarro9495BrauerCoveringPrinciple P.p P.k P.K
  S820 : Navarro820CyclicBrauerTwistPrinciple P.p P.k P.K
  fixedLocal : FixedLocalExtensionData localInflation ambient
  initialGlobal : ChosenGlobalExtensionData ambient
  base : BaseBlockInducesFromSelectedWeight
    (characterExtensionsOfLocalAndGlobal fixedLocal initialGlobal)
  cyclicSource : PositiveQPairCyclicSourceFromBase
    fixedLocal initialGlobal base

namespace PositiveQExtensionBlockSources

variable {P : Definition35Problem.{u}}
variable {psi : Definition35Brauer P}
variable {w : Definition35Weight P}

/-- The existential cyclic construction specialised to the exact fields of
the lower source packet. -/
theorem exists_extensions_and_intermediateBlocks
    (S : PositiveQExtensionBlockSources psi w) :
    ∃ extensions : SpathCharacterExtensions P S.reference psi w S.quotient
        S.weight S.localInflation S.ambient,
      Nonempty (IntermediateBlockSource P S.reference psi w S.quotient
        S.weight S.localInflation S.ambient extensions) :=
  exists_extensions_and_intermediate_blocks
    S.S9295 S.S9495 S.S820 S.fixedLocal S.initialGlobal S.base
      S.cyclicSource.toPositiveQPairCyclicSource

/-- The global/local extensions canonically chosen from the proved
existential packet. -/
noncomputable def extensions
    (S : PositiveQExtensionBlockSources psi w) :
    SpathCharacterExtensions P S.reference psi w S.quotient S.weight
      S.localInflation S.ambient :=
  Classical.choose S.exists_extensions_and_intermediateBlocks

/-- The intermediate block equalities accompanying the same chosen
extensions. -/
noncomputable def intermediateBlocks
    (S : PositiveQExtensionBlockSources psi w) :
    IntermediateBlockSource P S.reference psi w S.quotient S.weight
      S.localInflation S.ambient S.extensions :=
  Classical.choice (Classical.choose_spec
    S.exists_extensions_and_intermediateBlocks)

end PositiveQExtensionBlockSources

/-- Provenance-retaining positive-radical extension and intermediate-block
data.  Both returned objects are definitionally the objects chosen from the
single cyclic-source theorem above. -/
structure DerivedPositiveQExtensionBlockData
    {P : Definition35Problem.{u}}
    {psi : Definition35Brauer P}
    {w : Definition35Weight P}
    (S : PositiveQExtensionBlockSources psi w) where
  globalLocalExtensions :
    SpathCharacterExtensions P S.reference psi w S.quotient S.weight
      S.localInflation S.ambient
  extensions_from_cyclicSources : globalLocalExtensions = S.extensions
  intermediateBlocks :
    IntermediateBlockSource P S.reference psi w S.quotient S.weight
      S.localInflation S.ambient globalLocalExtensions
  intermediateBlocks_from_cyclicSources :
    HEq intermediateBlocks S.intermediateBlocks

/-- Construct both positive-radical records without adding a target-shaped
premise. -/
noncomputable def derivedPositiveQExtensionBlockData
    {P : Definition35Problem.{u}}
    {psi : Definition35Brauer P}
    {w : Definition35Weight P}
    (S : PositiveQExtensionBlockSources psi w) :
    DerivedPositiveQExtensionBlockData S where
  globalLocalExtensions := S.extensions
  extensions_from_cyclicSources := rfl
  intermediateBlocks := S.intermediateBlocks
  intermediateBlocks_from_cyclicSources := HEq.rfl

namespace DerivedPositiveQExtensionBlockData

variable {P : Definition35Problem.{u}}
variable {psi : Definition35Brauer P}
variable {w : Definition35Weight P}
variable {S : PositiveQExtensionBlockSources psi w}

/-- The derived extension and intermediate block data satisfy the
Späth condition for the matched character and weight. -/
noncomputable def toSpathMatchedBlockCondition
    (D : DerivedPositiveQExtensionBlockData S) :
    SpathMatchedBlockCondition P S.reference psi w where
  quotient := S.quotient
  tail :=
    { weight := S.weight
      localInflation := S.localInflation
      ambient := S.ambient
      extensions := D.globalLocalExtensions
      intermediateBlocks := D.intermediateBlocks }

end DerivedPositiveQExtensionBlockData

/-- The concrete Spath packet together with equality to the packet built
from the derived extension and intermediate-block records. -/
structure DerivedPositiveQSpathMatchedBlockData
    {P : Definition35Problem.{u}}
    {psi : Definition35Brauer P}
    {w : Definition35Weight P}
    (S : PositiveQExtensionBlockSources psi w) where
  derived : DerivedPositiveQExtensionBlockData S
  matched : SpathMatchedBlockCondition P S.reference psi w
  matched_from_derived : matched = derived.toSpathMatchedBlockCondition

/-- Canonical construction of the positive-radical concrete Spath packet. -/
noncomputable def derivedPositiveQSpathMatchedBlockData
    {P : Definition35Problem.{u}}
    {psi : Definition35Brauer P}
    {w : Definition35Weight P}
    (S : PositiveQExtensionBlockSources psi w) :
    DerivedPositiveQSpathMatchedBlockData S where
  derived := derivedPositiveQExtensionBlockData S
  matched :=
    (derivedPositiveQExtensionBlockData S).toSpathMatchedBlockCondition
  matched_from_derived := rfl

/-! ## The literal nonprincipal Definition 3.5 carrier -/

variable {k K X BlockIndex : Type u}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X] [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}

/-- The action presentation and local reductions needed for the
nonprincipal literal Definition 3.5 problem. -/
structure NonprincipalDefinition35CarrierSources
    (iota : PrimeRegularRootEmbedding 3 k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralCarrierAdapter
      (p := 3) (k := k) (K := K) (X := X))
    (S : Fi24ThreeBlockSource (k := k) (X := X)) where
  Gamma : Type u
  [groupGamma : Group Gamma]
  [finiteGamma : Finite Gamma]
  gamma : Gamma →* MulAut X
  gammaBlock_fixed : ∀ a : Gamma,
    inverseOpHom gamma a • S.nonprincipalBlock = S.nonprincipalBlock
  localReduction : ∀ w : LiteralWeightFibre R.1 S.nonprincipalBlock,
    SelectedLocalReductionSource R.1 S.nonprincipalBlock w

attribute [instance]
  NonprincipalDefinition35CarrierSources.groupGamma
  NonprincipalDefinition35CarrierSources.finiteGamma

/-- The literal Definition 3.5 problem on the unique nonprincipal
positive-defect block. -/
def nonprincipalDefinition35Problem
    (iota : PrimeRegularRootEmbedding 3 k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralCarrierAdapter
      (p := 3) (k := k) (K := K) (X := X))
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (Carrier : NonprincipalDefinition35CarrierSources iota hinj R S) :
    Definition35Problem :=
  literalDefinition35Problem iota hinj R S.nonprincipalBlock Carrier.gamma
    Carrier.gammaBlock_fixed Carrier.localReduction

/-- A globally selected Brauer character in the nonprincipal block, viewed
on the operations-aligned Definition 3.5 carrier. -/
def nonprincipalDefinition35Brauer
    (iota : PrimeRegularRootEmbedding 3 k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (R : LiteralCarrierAdapter
      (p := 3) (k := k) (K := K) (X := X))
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (Carrier : NonprincipalDefinition35CarrierSources iota hinj R S)
    (phi : IBr iota)
    (hphi : brauerBlock iota hinj blocks phi = S.nonprincipalBlock) :
    Definition35Brauer
      (nonprincipalDefinition35Problem iota hinj R S Carrier) :=
  ⟨phi, (literalOperations_brauerBlock_eq iota hinj blocks R phi).trans hphi⟩

/-- The corresponding globally selected weight in the nonprincipal block,
viewed on the same Definition 3.5 carrier. -/
def nonprincipalDefinition35Weight
    (iota : PrimeRegularRootEmbedding 3 k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralCarrierAdapter
      (p := 3) (k := k) (K := K) (X := X))
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (Carrier : NonprincipalDefinition35CarrierSources iota hinj R S)
    (w : WeightClass (p := 3) (K := K) (X := X))
    (hw : R.1.weightBlock w = S.nonprincipalBlock) :
    Definition35Weight
      (nonprincipalDefinition35Problem iota hinj R S Carrier) :=
  ⟨w, hw⟩

/-! ## Exact source packet for the matched-pair split -/

/-- Source data used to classify every pair selected by one fixed global
equivalence.  Exhaustiveness is inherited from `S.all_blocks`; named-row
coverage is *derived* from the two lower census certificates.

The two lower extension fields are indexed by the selected pair.  They do
not assert a final predicate: each returns only the exact cyclic source
packet consumed by the concrete constructors above. -/
structure Fi24P3MatchedPairAssemblySources
    (iota : PrimeRegularRootEmbedding 3 k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (R : LiteralCarrierAdapter
      (p := 3) (k := k) (K := K) (X := X))
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource 3 X)
    (Q : Subgroup X)
    (table : Source Q
      (R.1.operations.toLocalNormalizerBlockOperations Q))
    (Omega : IBr iota ≃ WeightClass (p := 3) (K := K) (X := X)) where
  automorphismEquivariant : ∀ (alpha : (MulAut X)ᵐᵒᵖ) (phi : IBr iota),
    Omega (alpha • phi) = alpha • Omega phi
  blockPreserving : ∀ phi,
    R.1.weightBlock (Omega phi) = brauerBlock iota hinj blocks phi
  qOneNormalisation : ∀ d :
      GlobalDefectZeroCharacter (p := 3) (K := K) (X := X),
    Omega (D.reduce (iota := iota) d) = T.atOne d
  defectZeroCompatibility :
    TrivialWeightBlockCompatibility iota hinj blocks R D T
  defectZeroBlocks : DefectZeroOrdinaryBlockSource iota hinj blocks D
  defectZeroIdentification :
    Fi24DefectZeroBlockIdentification iota hinj blocks D S
  localCensus : Fi24P3LocalDefectZeroCensusBinding R Q table
  radicalSupport : Fi24P3NonprincipalRadicalSupportSource R S Q table
  qOneCarrier : QOneDefinition35CarrierSources iota hinj blocks R D
  qOneLower : ∀ d :
      GlobalDefectZeroCharacter (p := 3) (K := K) (X := X),
    QOneCyclicExtensionBlockSources
      T d
      (qOneDefinition35Brauer iota hinj blocks R D qOneCarrier d)
      (qOneDefinition35Weight iota hinj blocks R D T
        defectZeroCompatibility qOneCarrier d)
      rfl
  nonprincipalCarrier :
    NonprincipalDefinition35CarrierSources iota hinj R S
  positiveLower : ∀ (phi : IBr iota)
      (hblock : brauerBlock iota hinj blocks phi = S.nonprincipalBlock)
      (_hpositive : CharacterWeight.radicalClass (Omega phi) ≠
        RadicalConjugacyClass.trivialClass T.trivialRadical),
    PositiveQExtensionBlockSources
      (nonprincipalDefinition35Brauer iota hinj blocks R S
        nonprincipalCarrier phi hblock)
      (nonprincipalDefinition35Weight iota hinj R S nonprincipalCarrier
        (Omega phi) ((blockPreserving phi).trans hblock))

namespace Fi24P3MatchedPairAssemblySources

variable {iota : PrimeRegularRootEmbedding 3 k K X}
variable {hinj : IrreducibleBrauerCharacterInjectivity iota}
variable {blocks : BlockIdempotentDecomposition blockIdempotent}
variable {R : LiteralCarrierAdapter
  (p := 3) (k := k) (K := K) (X := X)}
variable {S : Fi24ThreeBlockSource (k := k) (X := X)}
variable {D : DefectZeroReductionSource iota}
variable {T : TrivialWeightSource 3 X}
variable {Q : Subgroup X}
variable {table : Source Q
  (R.1.operations.toLocalNormalizerBlockOperations Q)}
variable {Omega : IBr iota ≃ WeightClass (p := 3) (K := K) (X := X)}

/-- The nonprincipal named-row coverage is a theorem from the two lower
census fields, not an aggregate premise of the construction source. -/
theorem nonprincipalCoverage
    (C : Fi24P3MatchedPairAssemblySources iota hinj blocks R S D T Q table
      Omega) :
    Fi24P3NonprincipalWeightCoverage R S Q table :=
  nonprincipalWeightCoverage_of_localCensus_and_radicalSupport
    R S Q table C.localCensus C.radicalSupport

/-- The global map already supplies a literal Brauer/weight equivalence on
every block fibre.  This is the concrete numerical-AWC-level input available
before invoking Spath's extension theorem; it is not itself AWC-goodness. -/
def blockFibreEquiv
    (C : Fi24P3MatchedPairAssemblySources iota hinj blocks R S D T Q table
      Omega)
    (b : ActualBlock (k := k) (X := X)) :
    {phi : IBr iota // brauerBlock iota hinj blocks phi = b} ≃
      {w : WeightClass (p := 3) (K := K) (X := X) //
        R.1.weightBlock w = b} :=
  threeBlockBlockEquiv iota hinj blocks Omega C.blockPreserving b

end Fi24P3MatchedPairAssemblySources

/-! ## Concrete coverage of every matched pair -/

variable {iota : PrimeRegularRootEmbedding 3 k K X}
variable {hinj : IrreducibleBrauerCharacterInjectivity iota}
variable {blocks : BlockIdempotentDecomposition blockIdempotent}
variable {R : LiteralCarrierAdapter
  (p := 3) (k := k) (K := K) (X := X)}
variable {S : Fi24ThreeBlockSource (k := k) (X := X)}
variable {D : DefectZeroReductionSource iota}
variable {T : TrivialWeightSource 3 X}
variable {Q : Subgroup X}
variable {table : Source Q
  (R.1.operations.toLocalNormalizerBlockOperations Q)}
variable {Omega : IBr iota ≃ WeightClass (p := 3) (K := K) (X := X)}

/-- A trivial-radical matched pair, identified with a canonical defect-zero
datum and equipped with its concrete `Q = 1` Spath packet.

The current source API does not certify that every such datum lies in the
single role-labelled block `S.defectZeroBlock`; only the selected datum in
`defectZeroIdentification` has that equality.  Accordingly no such block
equality is asserted here. -/
structure QOneMatchedPairRealization
    (C : Fi24P3MatchedPairAssemblySources iota hinj blocks R S D T Q table
      Omega)
    (phi : IBr iota) where
  datum : GlobalDefectZeroCharacter (p := 3) (K := K) (X := X)
  phi_eq : phi = D.reduce (iota := iota) datum
  weight_eq : Omega phi = T.atOne datum
  matched : DerivedQOneSpathMatchedBlockData (C.qOneLower datum)

/-- A positive-radical nonprincipal pair, with its covering table row,
representative-level conjugator, and concrete positive-`Q` Spath packet. -/
structure NonprincipalPositiveMatchedPairRealization
    (C : Fi24P3MatchedPairAssemblySources iota hinj blocks R S D T Q table
      Omega)
    (phi : IBr iota) where
  radical_ne_trivial : CharacterWeight.radicalClass (Omega phi) ≠
    RadicalConjugacyClass.trivialClass T.trivialRadical
  block_eq : brauerBlock iota hinj blocks phi = S.nonprincipalBlock
  row : P3QSquaredTableRow
  row_weight_eq : tableRowWeight R Q table row = Omega phi
  rowAlignment : NamedTableRowSelectedWeightAlignment
    R S.nonprincipalBlock
      (nonprincipalDefinition35Weight iota hinj R S
        C.nonprincipalCarrier (Omega phi)
        ((C.blockPreserving phi).trans block_eq))
      Q table row
  matched : DerivedPositiveQSpathMatchedBlockData
    (C.positiveLower phi block_eq radical_ne_trivial)

/-- The precise remaining manuscript case: a matched weight with positive
radical in the principal block.  Block cancellation supplies its bijection,
but the current concrete APIs contain no principal analogue of the lower
extension and intermediate-block packet. -/
structure PrincipalPositiveMatchedPairResidual
    (C : Fi24P3MatchedPairAssemblySources iota hinj blocks R S D T Q table
      Omega)
    (phi : IBr iota) : Prop where
  radical_ne_trivial : CharacterWeight.radicalClass (Omega phi) ≠
    RadicalConjugacyClass.trivialClass T.trivialRadical
  block_eq : brauerBlock iota hinj blocks phi = S.principalBlock

/-- A conclusion-free exhaustive classification of one matched pair.  Its
recursor is the desired eliminator and exposes the principal residual rather
than accepting an arbitrary predicate as an endpoint. -/
inductive MatchedPairCoverageCase
    (C : Fi24P3MatchedPairAssemblySources iota hinj blocks R S D T Q table
      Omega)
    (phi : IBr iota) where
  | qOne (data : QOneMatchedPairRealization C phi)
  | nonprincipalPositive
      (data : NonprincipalPositiveMatchedPairRealization C phi)
  | principalPositive
      (data : PrincipalPositiveMatchedPairResidual C phi)

/-- Construct the exhaustive concrete matched-pair classification from the
literal source certificates. -/
noncomputable def matchedPairCoverageCase
    (C : Fi24P3MatchedPairAssemblySources iota hinj blocks R S D T Q table
      Omega)
    (phi : IBr iota) : MatchedPairCoverageCase C phi := by
  classical
  by_cases hqOne : CharacterWeight.radicalClass (Omega phi) =
      RadicalConjugacyClass.trivialClass T.trivialRadical
  · let hexists :=
      T.exists_atOne_of_radicalClass_eq_trivial (Omega phi) hqOne
    let d := Classical.choose hexists
    have hd : T.atOne d = Omega phi := Classical.choose_spec hexists
    have hreduce : D.reduce (iota := iota) d = phi :=
      Omega.injective ((C.qOneNormalisation d).trans hd)
    exact .qOne
      { datum := d
        phi_eq := hreduce.symm
        weight_eq := hd.symm
        matched := derivedQOneSpathMatchedBlockData (C.qOneLower d) }
  · by_cases hprincipal :
        brauerBlock iota hinj blocks phi = S.principalBlock
    · exact .principalPositive
        { radical_ne_trivial := hqOne
          block_eq := hprincipal }
    · by_cases hnonprincipal :
          brauerBlock iota hinj blocks phi = S.nonprincipalBlock
      · let w : WeightFibre (R := R) S.nonprincipalBlock :=
          ⟨Omega phi, (C.blockPreserving phi).trans hnonprincipal⟩
        let hrowExists := C.nonprincipalCoverage.covers w
        let row := Classical.choose hrowExists
        have hrow : tableRowWeight R Q table row = Omega phi :=
          Classical.choose_spec hrowExists
        exact .nonprincipalPositive
          { radical_ne_trivial := hqOne
            block_eq := hnonprincipal
            row := row
            row_weight_eq := hrow
            rowAlignment :=
              NamedTableRowSelectedWeightAlignment.ofWeightClassEq hrow
            matched := derivedPositiveQSpathMatchedBlockData
              (C.positiveLower phi hnonprincipal hqOne) }
      · have hdefectZero :
            brauerBlock iota hinj blocks phi = S.defectZeroBlock := by
          rcases S.all_blocks (brauerBlock iota hinj blocks phi) with
            hp | hn | hz
          · exact (hprincipal hp).elim
          · exact (hnonprincipal hn).elim
          · exact hz
        let d := C.defectZeroIdentification.character
        have hsameBlock : brauerBlock iota hinj blocks phi =
            brauerBlock iota hinj blocks (D.reduce (iota := iota) d) :=
          hdefectZero.trans C.defectZeroIdentification.block_eq
        have hphi : phi = D.reduce (iota := iota) d :=
          DefectZeroOrdinaryBlockSource.uniqueBrauer
            (iota := iota) (hinj := hinj) (blocks := blocks)
            D C.defectZeroBlocks d phi hsameBlock
        have hradical : CharacterWeight.radicalClass (Omega phi) =
            RadicalConjugacyClass.trivialClass T.trivialRadical := by
          rw [hphi, C.qOneNormalisation d]
          exact T.radicalClass_atOne d
        exact (hqOne hradical).elim

/-- The full conclusion-free coverage object.  It is stronger than a bare
disjunction because each solved branch retains the exact lower-source
provenance of its concrete Spath packet. -/
structure ConcreteMatchedPairCoverage
    (C : Fi24P3MatchedPairAssemblySources iota hinj blocks R S D T Q table
      Omega) where
  caseAt : ∀ phi : IBr iota, MatchedPairCoverageCase C phi

/-- Combine the coverage function for every matched pair. -/
noncomputable def concreteMatchedPairCoverage
    (C : Fi24P3MatchedPairAssemblySources iota hinj blocks R S D T Q table
      Omega) :
    ConcreteMatchedPairCoverage C where
  caseAt := matchedPairCoverageCase C

end ModularRep.PaperProofs.SporadicFi24P3MatchedPairAssemblyWindow


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
