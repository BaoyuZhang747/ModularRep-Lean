import ModularRep.PaperProofs.SporadicFi24Definition35Operations
import ModularRep.PaperProofs.SporadicFi24P3PositiveQBaseInductionTransport
import ModularRep.PaperProofs.SporadicFi24P3PositiveQExtensionBlockObligationsFromSources

/-!
# Joining the positive-radical base and cyclic source packets

This module removes the duplicated intersection block-induction premise from
the source-facing positive-radical API.  Its generic packet contains the
cyclic and interval data used by `PositiveQPairCyclicSource`, but replaces
`intersectionBaseInduction` by the single selected primitive-idempotent match
needed to transport the already supplied
`BaseBlockInducesFromSelectedWeight.inductionEquality`.

The literal Fischer specialization separately pairs that generic packet with
the conjugator-bearing alignment of a named table row and the opaque
`selectedCharacterWeight` representative.  Equality is required only after
passing to the global weight conjugacy class carrier; the raw representative
alignment and radical conjugacy are derived.

No theorem in this file chooses a top block or character extensions, and no
character triple, BAW assertion, or iBAW assertion occurs in its source
interfaces.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3PositiveQExtensionBlockObligationsJoin

open Formalisation
open ModularRep
open ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SpathPositiveQBaseBlock
open ModularRep.PaperProofs.SpathPositiveQTopBlockChoice
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24Definition35Operations
open ModularRep.PaperProofs.SporadicFi24P3NamedTableLiteralWeightRows
open ModularRep.PaperProofs.SporadicFi24P3PositiveQBaseInductionTransport
open ModularRep.PaperProofs.SporadicFi24P3PositiveQExtensionBlockObligationsFromSources
open ModularRep.PaperProofs.SporadicFi24P3QSquaredLocalTableSource

universe u

noncomputable local instance subgroupFintype
    {G : Type u} [Group G] [Finite G] (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

local instance definition35ProblemPrime (P : Definition35Problem.{u}) :
    Fact P.p.Prime :=
  ⟨P.iota.prime⟩

/-! ## Generic replacement of the duplicated induction premise -/

/-- Exact cyclic-source data with the intersection induction relation
replaced by its one honest selected-idempotent alignment.

All fields other than `selectedIntersectionIdempotentMatch` are direct
projections required by `PositiveQPairCyclicSource`.  In particular, this
record contains no `BlockInducesTo` field. -/
structure PositiveQPairCyclicSourceFromBase
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation : QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    (fixedLocal : FixedLocalExtensionData localInflation ambient)
    (initialGlobal : ChosenGlobalExtensionData ambient)
    (base : BaseBlockInducesFromSelectedWeight
      (characterExtensionsOfLocalAndGlobal fixedLocal initialGlobal)) where
  AmbientBlock : Type u
  LocalBlock : Type u
  IntersectionBlock : Type u
  [fintypeAmbientBlock : Fintype AmbientBlock]
  [fintypeLocalBlock : Fintype LocalBlock]
  [fintypeIntersectionBlock : Fintype IntersectionBlock]
  ambientBlockIdempotent : AmbientBlock → MonoidAlgebra P.k ambient.A
  localBlockIdempotent : LocalBlock → MonoidAlgebra P.k
    (AmbientLocalGroup P reference psi w quotient ambient)
  intersectionBlockIdempotent : IntersectionBlock → MonoidAlgebra P.k
    (ambient.base.comap
      (AmbientLocalGroup P reference psi w quotient ambient).subtype)
  ambientBlocks : BlockIdempotentDecomposition ambientBlockIdempotent
  localBlocks : BlockIdempotentDecomposition localBlockIdempotent
  intersectionBlocks :
    BlockIdempotentDecomposition intersectionBlockIdempotent
  ambientBrauerInjective :
    IrreducibleBrauerCharacterInjectivity initialGlobal.ambientRoot
  localBrauerInjective :
    IrreducibleBrauerCharacterInjectivity fixedLocal.localAmbientRoot
  intersectionBrauerInjective : IrreducibleBrauerCharacterInjectivity
    (intersectionLocalBaseRoot localInflation ambient)
  ambientCentralCharacters : BlockCentralCharacterCatalogue ambientBlocks
  localCentralCharacters : BlockCentralCharacterCatalogue localBlocks
  intersectionCentralCharacters :
    BlockCentralCharacterCatalogue intersectionBlocks
  prime_eq_three : P.p = 3
  radicalSquared :
    quotientRadical P reference w ≃*
      Multiplicative (Fin 2 → ZMod 3)
  fieldSource : SpathCoefficientField P.p P.k P.iota.prime
  globalRootAgreement :
    ∀ zeta : rootsOfUnity (primeRegularExponent P.p ambient.base) P.k,
      (baseGlobalRoot
        (characterExtensionsOfLocalAndGlobal fixedLocal initialGlobal)).lift
          (((zeta : P.kˣ) : P.k)) =
        initialGlobal.ambientRoot.lift (((zeta : P.kˣ) : P.k))
  localRootAgreement :
    ∀ zeta : rootsOfUnity
        (primeRegularExponent P.p
          (ambient.base.comap
            (AmbientLocalGroup P reference psi w quotient ambient).subtype))
        P.k,
      (intersectionLocalBaseRoot localInflation ambient).lift
          (((zeta : P.kˣ) : P.k)) =
        fixedLocal.localAmbientRoot.lift (((zeta : P.kˣ) : P.k))
  quotientCyclic : IsCyclic (ambient.A ⧸ ambient.base)
  quotientCard_le_two : Nat.card (ambient.A ⧸ ambient.base) ≤ 2
  interval : CentralBrauerInterval (p := P.p)
    (ambientRadical P reference psi w quotient ambient)
    (AmbientLocalGroup P reference psi w quotient ambient)
  intervalSource : Navarro414IntervalCentralCharacterSource interval
    localBlocks localCentralCharacters
  selectedIntersectionIdempotentMatch :
    IntersectionBaseSelectedIdempotentMatch fixedLocal initialGlobal base
      intersectionBlockIdempotent intersectionBlocks
      intersectionBrauerInjective

attribute [instance]
  PositiveQPairCyclicSourceFromBase.fintypeAmbientBlock
  PositiveQPairCyclicSourceFromBase.fintypeLocalBlock
  PositiveQPairCyclicSourceFromBase.fintypeIntersectionBlock

namespace PositiveQPairCyclicSourceFromBase

/-- Fill the legacy cyclic source packet.  Its intersection induction field
is a theorem from the base equality and the selected-idempotent match, not a
second source premise. -/
def toPositiveQPairCyclicSource
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation : QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    {fixedLocal : FixedLocalExtensionData localInflation ambient}
    {initialGlobal : ChosenGlobalExtensionData ambient}
    {base : BaseBlockInducesFromSelectedWeight
      (characterExtensionsOfLocalAndGlobal fixedLocal initialGlobal)}
    (source : PositiveQPairCyclicSourceFromBase
      fixedLocal initialGlobal base) :
    PositiveQPairCyclicSource fixedLocal initialGlobal base where
  AmbientBlock := source.AmbientBlock
  LocalBlock := source.LocalBlock
  IntersectionBlock := source.IntersectionBlock
  fintypeAmbientBlock := source.fintypeAmbientBlock
  fintypeLocalBlock := source.fintypeLocalBlock
  fintypeIntersectionBlock := source.fintypeIntersectionBlock
  ambientBlockIdempotent := source.ambientBlockIdempotent
  localBlockIdempotent := source.localBlockIdempotent
  intersectionBlockIdempotent := source.intersectionBlockIdempotent
  ambientBlocks := source.ambientBlocks
  localBlocks := source.localBlocks
  intersectionBlocks := source.intersectionBlocks
  ambientBrauerInjective := source.ambientBrauerInjective
  localBrauerInjective := source.localBrauerInjective
  intersectionBrauerInjective := source.intersectionBrauerInjective
  ambientCentralCharacters := source.ambientCentralCharacters
  localCentralCharacters := source.localCentralCharacters
  intersectionCentralCharacters := source.intersectionCentralCharacters
  prime_eq_three := source.prime_eq_three
  radicalSquared := source.radicalSquared
  fieldSource := source.fieldSource
  globalRootAgreement := source.globalRootAgreement
  localRootAgreement := source.localRootAgreement
  quotientCyclic := source.quotientCyclic
  quotientCard_le_two := source.quotientCard_le_two
  interval := source.interval
  intervalSource := source.intervalSource
  intersectionBaseInduction :=
    intersectionBaseInduction_of_base base source.intersectionBlocks
      source.intersectionBrauerInjective source.intersectionCentralCharacters
      source.selectedIntersectionIdempotentMatch

end PositiveQPairCyclicSourceFromBase

/-! ## Type-correct literal Fi24 table-row pairing -/

variable {k K X Gamma : Type u}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X] [Group Gamma] [Finite Gamma]

/-- A short name for the exact operations-aligned Definition 3.5 problem on
which both the named table row and `selectedCharacterWeight` live. -/
abbrev LiteralPositiveQProblem
    (iota : PrimeRegularRootEmbedding 3 k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := X))
    (B : ActualBlock (k := k) (X := X))
    (gamma : Gamma →* MulAut X)
    (gammaBlock_fixed : ∀ a : Gamma,
      inverseOpHom gamma a • B = B)
    (localReduction : ∀ w : LiteralWeightFibre R.1 B,
      SelectedLocalReductionSource R.1 B w) :
    Definition35Problem :=
  literalDefinition35Problem iota hinj R B gamma gammaBlock_fixed
    localReduction

/-- A generic from-base cyclic packet paired with a named row on the exact
same literal operations carrier.

The row alignment is representative-level and retains its conjugator, but it
is not used as a substitute for literal equality of the selected radical and
the table subgroup. -/
structure NamedTablePositiveQPairCyclicSource
    (iota : PrimeRegularRootEmbedding 3 k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := X))
    (B : ActualBlock (k := k) (X := X))
    (gamma : Gamma →* MulAut X)
    (gammaBlock_fixed : ∀ a : Gamma,
      inverseOpHom gamma a • B = B)
    (localReduction : ∀ w : LiteralWeightFibre R.1 B,
      SelectedLocalReductionSource R.1 B w)
    {reference psi : Definition35Brauer
      (LiteralPositiveQProblem iota hinj R B gamma gammaBlock_fixed
        localReduction)}
    {w : Definition35Weight
      (LiteralPositiveQProblem iota hinj R B gamma gammaBlock_fixed
        localReduction)}
    {quotient : CentralQuotientBrauerSource
      (LiteralPositiveQProblem iota hinj R B gamma gammaBlock_fixed
        localReduction) reference psi}
    {weight : QuotientWeightBrauerSource
      (LiteralPositiveQProblem iota hinj R B gamma gammaBlock_fixed
        localReduction) reference w}
    {localInflation : QuotientLocalInflationSource
      (LiteralPositiveQProblem iota hinj R B gamma gammaBlock_fixed
        localReduction) reference w weight}
    {ambient : SpathAmbientGroup
      (LiteralPositiveQProblem iota hinj R B gamma gammaBlock_fixed
        localReduction) reference psi quotient}
    (fixedLocal : FixedLocalExtensionData localInflation ambient)
    (initialGlobal : ChosenGlobalExtensionData ambient)
    (base : BaseBlockInducesFromSelectedWeight
      (characterExtensionsOfLocalAndGlobal fixedLocal initialGlobal))
    (Q : Subgroup X)
    (table : SporadicFi24P3QSquaredLocalTableSource.Source Q
      (R.1.operations.toLocalNormalizerBlockOperations Q))
    (r : P3QSquaredTableRow) where
  cyclicSource : PositiveQPairCyclicSourceFromBase
    fixedLocal initialGlobal base
  rowAlignment : NamedTableRowSelectedWeightAlignment R B w Q table r

namespace NamedTablePositiveQPairCyclicSource

/-- Pair an existing from-base cyclic packet with the explicit conjugator
deduced from equality on the global weight-class carrier. -/
noncomputable def ofWeightClassEq
    (iota : PrimeRegularRootEmbedding 3 k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := X))
    (B : ActualBlock (k := k) (X := X))
    (gamma : Gamma →* MulAut X)
    (gammaBlock_fixed : ∀ a : Gamma,
      inverseOpHom gamma a • B = B)
    (localReduction : ∀ w : LiteralWeightFibre R.1 B,
      SelectedLocalReductionSource R.1 B w)
    {reference psi : Definition35Brauer
      (LiteralPositiveQProblem iota hinj R B gamma gammaBlock_fixed
        localReduction)}
    {w : Definition35Weight
      (LiteralPositiveQProblem iota hinj R B gamma gammaBlock_fixed
        localReduction)}
    {quotient : CentralQuotientBrauerSource
      (LiteralPositiveQProblem iota hinj R B gamma gammaBlock_fixed
        localReduction) reference psi}
    {weight : QuotientWeightBrauerSource
      (LiteralPositiveQProblem iota hinj R B gamma gammaBlock_fixed
        localReduction) reference w}
    {localInflation : QuotientLocalInflationSource
      (LiteralPositiveQProblem iota hinj R B gamma gammaBlock_fixed
        localReduction) reference w weight}
    {ambient : SpathAmbientGroup
      (LiteralPositiveQProblem iota hinj R B gamma gammaBlock_fixed
        localReduction) reference psi quotient}
    {fixedLocal : FixedLocalExtensionData localInflation ambient}
    {initialGlobal : ChosenGlobalExtensionData ambient}
    {base : BaseBlockInducesFromSelectedWeight
      (characterExtensionsOfLocalAndGlobal fixedLocal initialGlobal)}
    (cyclicSource : PositiveQPairCyclicSourceFromBase
      fixedLocal initialGlobal base)
    (Q : Subgroup X)
    (table : SporadicFi24P3QSquaredLocalTableSource.Source Q
      (R.1.operations.toLocalNormalizerBlockOperations Q))
    (r : P3QSquaredTableRow)
    (hrow : tableRowWeight R Q table r = w.1) :
    NamedTablePositiveQPairCyclicSource iota hinj R B gamma
      gammaBlock_fixed localReduction fixedLocal initialGlobal base
      Q table r where
  cyclicSource := cyclicSource
  rowAlignment :=
    NamedTableRowSelectedWeightAlignment.ofWeightClassEq hrow

/-- Forget the optional named-row witness and construct the legacy cyclic
source with its intersection induction relation derived from the base. -/
def toPositiveQPairCyclicSource
    {iota : PrimeRegularRootEmbedding 3 k K X}
    {hinj : IrreducibleBrauerCharacterInjectivity iota}
    {R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := X)}
    {B : ActualBlock (k := k) (X := X)}
    {gamma : Gamma →* MulAut X}
    {gammaBlock_fixed : ∀ a : Gamma,
      inverseOpHom gamma a • B = B}
    {localReduction : ∀ w : LiteralWeightFibre R.1 B,
      SelectedLocalReductionSource R.1 B w}
    {reference psi : Definition35Brauer
      (LiteralPositiveQProblem iota hinj R B gamma gammaBlock_fixed
        localReduction)}
    {w : Definition35Weight
      (LiteralPositiveQProblem iota hinj R B gamma gammaBlock_fixed
        localReduction)}
    {quotient : CentralQuotientBrauerSource
      (LiteralPositiveQProblem iota hinj R B gamma gammaBlock_fixed
        localReduction) reference psi}
    {weight : QuotientWeightBrauerSource
      (LiteralPositiveQProblem iota hinj R B gamma gammaBlock_fixed
        localReduction) reference w}
    {localInflation : QuotientLocalInflationSource
      (LiteralPositiveQProblem iota hinj R B gamma gammaBlock_fixed
        localReduction) reference w weight}
    {ambient : SpathAmbientGroup
      (LiteralPositiveQProblem iota hinj R B gamma gammaBlock_fixed
        localReduction) reference psi quotient}
    {fixedLocal : FixedLocalExtensionData localInflation ambient}
    {initialGlobal : ChosenGlobalExtensionData ambient}
    {base : BaseBlockInducesFromSelectedWeight
      (characterExtensionsOfLocalAndGlobal fixedLocal initialGlobal)}
    {Q : Subgroup X}
    {table : SporadicFi24P3QSquaredLocalTableSource.Source Q
      (R.1.operations.toLocalNormalizerBlockOperations Q)}
    {r : P3QSquaredTableRow}
    (source : NamedTablePositiveQPairCyclicSource iota hinj R B gamma
      gammaBlock_fixed localReduction fixedLocal initialGlobal base
      Q table r) :
    PositiveQPairCyclicSource fixedLocal initialGlobal base :=
  source.cyclicSource.toPositiveQPairCyclicSource

end NamedTablePositiveQPairCyclicSource

end ModularRep.PaperProofs.SporadicFi24P3PositiveQExtensionBlockObligationsJoin


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
