import ModularRep.PaperProofs.SporadicFi24P3NamedTableLiteralWeightRows
import ModularRep.CentralCharacterCovering
import ModularRep.PaperProofs.SpathPositiveQBaseBlock
import ModularRep.PaperProofs.SpathPositiveQTopBlockChoice

/-!
# The positive-radical table and base-intersection transports

This module records the two carrier transports needed between the named
`Fi'_{24}` table rows and the cyclic positive-radical argument.

First, a table row is aligned with the representative chosen by
`selectedCharacterWeight` at the isomorphism-class level.  The alignment
retains an actual conjugating element.  Consequently the selected radical is
proved to be a conjugate of the table subgroup; it is never silently replaced
by that subgroup.

Second, the base block-induction equality is moved to the intersection
presentation used by the cyclic covering argument.  The only residual source
field is equality of the two selected primitive idempotents after transport
through `subgroupIntersectionEquiv`.  The corresponding central character
identity, and hence the required `BlockInducesTo`, are kernel deductions.

There is no second block-induction premise, top-block choice, new extension
premise, character triple, BAW assertion, or iBAW assertion here.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3PositiveQBaseInductionTransport

open ModularRep
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SpathPositiveQBaseBlock
open ModularRep.PaperProofs.SpathPositiveQTopBlockChoice
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24P3NamedTableLiteralWeightRows
open ModularRep.PaperProofs.SporadicFi24P3QSquaredLocalTableSource

universe u

noncomputable local instance subgroupFintype
    {G : Type u} [Group G] [Finite G] (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

/-! ## A named row and the opaque selected representative -/

variable {k K X : Type u}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

/-- The actual character weight before either of the two quotient maps is
applied to a named table row. -/
abbrev namedTableRowRepresentative
    (R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := X))
    (Q : Subgroup X)
    (table : SporadicFi24P3QSquaredLocalTableSource.Source Q
      (R.1.operations.toLocalNormalizerBlockOperations Q))
    (r : P3QSquaredTableRow) :
    CharacterWeight 3 K X :=
  CharacterWeight.characterWeightAt Nat.prime_three
    (tableRadical R Q table) (tableLocalDZ R Q table r)

/-- Minimal representative-level alignment between one named table row and
the representative hidden behind `selectedCharacterWeight`.

The equality lives after the first, isomorphism-class quotient but before the
ambient-conjugacy quotient.  Thus `conjugator` is retained explicitly. -/
structure NamedTableRowSelectedWeightAlignment
    (R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := X))
    (B : ActualBlock (k := k) (X := X))
    (w : LiteralWeightFibre R.1 B)
    (Q : Subgroup X)
    (table : SporadicFi24P3QSquaredLocalTableSource.Source Q
      (R.1.operations.toLocalNormalizerBlockOperations Q))
    (r : P3QSquaredTableRow) where
  conjugator : X
  selectedIsoClass_eq :
    selectedRawWeight R.1 B w =
      conjugator •
        (Quotient.mk'' (namedTableRowRepresentative R Q table r) :
          CharacterWeight.IsoClass (p := 3) (K := K) (G := X))

namespace NamedTableRowSelectedWeightAlignment

variable
  {R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := X)}
  {B : ActualBlock (k := k) (X := X)}
  {w : LiteralWeightFibre R.1 B}
  {Q : Subgroup X}
  {table : SporadicFi24P3QSquaredLocalTableSource.Source Q
    (R.1.operations.toLocalNormalizerBlockOperations Q)}
  {r : P3QSquaredTableRow}

/-- Equality of the two global weight classes is enough to recover an
explicit representative-level conjugator. -/
noncomputable def ofWeightClassEq
    (hrow : tableRowWeight R Q table r = w.1) :
    NamedTableRowSelectedWeightAlignment R B w Q table r := by
  letI : Fintype (ActualBlock (k := k) (X := X)) :=
    R.1.operations.ambientBlockData.fintypeBlock
  let rowIso : CharacterWeight.IsoClass (p := 3) (K := K) (G := X) :=
    Quotient.mk'' (namedTableRowRepresentative R Q table r)
  have hclasses :
      (Quotient.mk'' (selectedRawWeight R.1 B w) :
          CharacterWeight.ConjugacyClass (p := 3) (K := K) (G := X)) =
        (Quotient.mk'' rowIso :
          CharacterWeight.ConjugacyClass (p := 3) (K := K) (G := X)) := by
    calc
      (Quotient.mk'' (selectedRawWeight R.1 B w) :
          CharacterWeight.ConjugacyClass (p := 3) (K := K) (G := X)) =
          w.1 := selectedCharacterWeight_spec R.1 B w
      _ = tableRowWeight R Q table r := hrow.symm
      _ = Quotient.mk'' rowIso := by
        rw [tableRowWeight,
          CharacterWeight.localDefectZeroEquivWeightRadicalFibre_apply_val]
  have horbit : selectedRawWeight R.1 B w ∈ MulAction.orbit X rowIso :=
    MulAction.orbitRel_apply.mp (Quotient.exact hclasses)
  let g := Classical.choose horbit
  have hg := Classical.choose_spec horbit
  exact ⟨g, hg.symm⟩

/-- Forgetting the retained conjugator recovers equality of the named table
weight class with the original element of the literal block fibre. -/
theorem tableRowWeight_eq
    (alignment : NamedTableRowSelectedWeightAlignment R B w Q table r) :
    tableRowWeight R Q table r = w.1 := by
  let _ : Fintype (ActualBlock (k := k) (X := X)) :=
    R.1.operations.ambientBlockData.fintypeBlock
  let rowIso : CharacterWeight.IsoClass (p := 3) (K := K) (G := X) :=
    Quotient.mk'' (namedTableRowRepresentative R Q table r)
  calc
    tableRowWeight R Q table r =
        (Quotient.mk'' rowIso :
          CharacterWeight.ConjugacyClass (p := 3) (K := K) (G := X)) := by
      rw [tableRowWeight,
        CharacterWeight.localDefectZeroEquivWeightRadicalFibre_apply_val]
    _ = Quotient.mk'' (alignment.conjugator • rowIso) :=
      (MulAction.orbitRel.Quotient.quotient_smul_eq).symm
    _ = Quotient.mk'' (selectedRawWeight R.1 B w) :=
      congrArg Quotient.mk'' alignment.selectedIsoClass_eq.symm
    _ = w.1 := selectedCharacterWeight_spec R.1 B w

/-- The radical selected from the opaque representative is the displayed
conjugate of the table subgroup.  In particular this theorem does not claim
that it is literally `Q`. -/
theorem selectedRadical_eq_conjugate
    (alignment : NamedTableRowSelectedWeightAlignment R B w Q table r) :
    (selectedCharacterWeight R.1 B w).subgroup =
      Q.map (MulAut.conj alignment.conjugator).toMonoidHom := by
  let rowIso : CharacterWeight.IsoClass (p := 3) (K := K) (G := X) :=
    Quotient.mk'' (namedTableRowRepresentative R Q table r)
  calc
    (selectedCharacterWeight R.1 B w).subgroup =
        rawSubgroup (selectedRawWeight R.1 B w) := rfl
    _ = rawSubgroup (alignment.conjugator • rowIso) :=
      congrArg rawSubgroup alignment.selectedIsoClass_eq
    _ = (rawSubgroup rowIso).map
          (MulAut.conj alignment.conjugator).toMonoidHom :=
      rawSubgroup_conjugate alignment.conjugator rowIso
    _ = Q.map (MulAut.conj alignment.conjugator).toMonoidHom := rfl

end NamedTableRowSelectedWeightAlignment

/-! ## From the base induction equality to the intersection presentation -/

/-- The quotient-normaliser root on the intersection-inside-local-group
presentation.  This is definitionally the root called `cyclicLocalBaseRoot`
by `PositiveQPairCyclicSource`. -/
abbrev intersectionLocalBaseRoot
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    (localInflation : QuotientLocalInflationSource P reference w weight)
    (ambient : SpathAmbientGroup P reference psi quotient) :
    PrimeRegularRootEmbedding P.p P.k P.K
      (ambient.base.comap
        (AmbientLocalGroup P reference psi w quotient ambient).subtype) :=
  localInflation.iota.alongMulEquiv (canonicalLocalBaseEquiv ambient)

/-- The corresponding quotient-normaliser Brauer character.  This is
definitionally the character called `cyclicLocalBaseBrauer` by
`PositiveQPairCyclicSource`. -/
abbrev intersectionLocalBaseBrauer
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    (localInflation : QuotientLocalInflationSource P reference w weight)
    (ambient : SpathAmbientGroup P reference psi quotient) :
    IBr (intersectionLocalBaseRoot localInflation ambient) :=
  IrreducibleBrauerCharacter.alongMulEquiv localInflation.iota
    (canonicalLocalBaseEquiv ambient) localInflation.brauer

/-- The local block selected in the base presentation. -/
abbrev baseSelectedLocalBlock
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation : QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    {extensions : SpathCharacterExtensions P reference psi w quotient weight
      localInflation ambient}
    (base : BaseBlockInducesFromSelectedWeight extensions) :
    base.LocalBlock :=
  irreducibleBrauerCharacterBlock
    (baseLocalRoot extensions) base.localBrauerInjective
    base.localBlocks (baseLocalBrauer extensions)

/-- The local block selected before changing from the intersection-inside-
`N_A(Q)` presentation to the intersection-inside-base presentation. -/
abbrev intersectionSelectedLocalBlock
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation : QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    {IntersectionBlock : Type u} [Fintype IntersectionBlock]
    {intersectionBlockIdempotent : IntersectionBlock → MonoidAlgebra P.k
      (ambient.base.comap
        (AmbientLocalGroup P reference psi w quotient ambient).subtype)}
    (intersectionBlocks :
      BlockIdempotentDecomposition intersectionBlockIdempotent)
    (intersectionBrauerInjective : IrreducibleBrauerCharacterInjectivity
      (intersectionLocalBaseRoot localInflation ambient)) :
    IntersectionBlock :=
  irreducibleBrauerCharacterBlock
    (intersectionLocalBaseRoot localInflation ambient)
    intersectionBrauerInjective intersectionBlocks
    (intersectionLocalBaseBrauer localInflation ambient)

/-- The sole residual block-carrier identification needed for the base to
intersection transport.

It matches only the two selected primitive idempotents.  It is strictly
weaker than a second `BlockInducesTo` premise and does not postulate equality
of whole catalogues. -/
structure IntersectionBaseSelectedIdempotentMatch
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
      (characterExtensionsOfLocalAndGlobal fixedLocal initialGlobal))
    {IntersectionBlock : Type u} [Fintype IntersectionBlock]
    (intersectionBlockIdempotent : IntersectionBlock → MonoidAlgebra P.k
      (ambient.base.comap
        (AmbientLocalGroup P reference psi w quotient ambient).subtype))
    (intersectionBlocks :
      BlockIdempotentDecomposition intersectionBlockIdempotent)
    (intersectionBrauerInjective : IrreducibleBrauerCharacterInjectivity
      (intersectionLocalBaseRoot localInflation ambient)) : Prop where
  selectedIdempotent_eq :
    MonoidAlgebra.domCongr P.k P.k
        (subgroupIntersectionEquiv
          (AmbientLocalGroup P reference psi w quotient ambient) ambient.base)
        (intersectionBlockIdempotent
          (intersectionSelectedLocalBlock intersectionBlocks
            intersectionBrauerInjective)) =
      base.localBlockIdempotent (baseSelectedLocalBlock base)

/-- The selected-idempotent match determines the corresponding equality of
block central characters. -/
theorem intersectionSelectedCentralCharacter_eq_base
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
    {IntersectionBlock : Type u} [Fintype IntersectionBlock]
    {intersectionBlockIdempotent : IntersectionBlock → MonoidAlgebra P.k
      (ambient.base.comap
        (AmbientLocalGroup P reference psi w quotient ambient).subtype)}
    {intersectionBlocks :
      BlockIdempotentDecomposition intersectionBlockIdempotent}
    {intersectionBrauerInjective : IrreducibleBrauerCharacterInjectivity
      (intersectionLocalBaseRoot localInflation ambient)}
    (intersectionCentralCharacters :
      BlockCentralCharacterCatalogue intersectionBlocks)
    (idempotentMatch : IntersectionBaseSelectedIdempotentMatch
      fixedLocal initialGlobal
      base intersectionBlockIdempotent intersectionBlocks
      intersectionBrauerInjective) :
    centralCharacterAlongMulEquiv
        (subgroupIntersectionEquiv
          (AmbientLocalGroup P reference psi w quotient ambient) ambient.base)
        (intersectionCentralCharacters.centralCharacter
          (intersectionSelectedLocalBlock intersectionBlocks
            intersectionBrauerInjective)) =
      base.localCentralCharacters.centralCharacter
        (baseSelectedLocalBlock base) := by
  apply centralCharacterAlongMulEquiv_eq_of_blockIdempotent
    (subgroupIntersectionEquiv
      (AmbientLocalGroup P reference psi w quotient ambient) ambient.base)
    intersectionCentralCharacters base.localCentralCharacters
  apply Subtype.ext
  change
    MonoidAlgebra.domCongr P.k P.k
        (subgroupIntersectionEquiv
          (AmbientLocalGroup P reference psi w quotient ambient) ambient.base)
        (intersectionBlockIdempotent
          (intersectionSelectedLocalBlock intersectionBlocks
            intersectionBrauerInjective)) =
      base.localBlockIdempotent (baseSelectedLocalBlock base)
  exact idempotentMatch.selectedIdempotent_eq

/-- Transport the already supplied base induction equality into exactly the
intersection presentation consumed by `PositiveQPairCyclicSource`.

The proof changes only the selected local central character.  The ambient
base catalogue and selected global block are literally those of `base`. -/
theorem intersectionBaseInduction_of_base
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation : QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    {fixedLocal : FixedLocalExtensionData localInflation ambient}
    {initialGlobal : ChosenGlobalExtensionData ambient}
    (base : BaseBlockInducesFromSelectedWeight
      (characterExtensionsOfLocalAndGlobal fixedLocal initialGlobal))
    {IntersectionBlock : Type u} [Fintype IntersectionBlock]
    {intersectionBlockIdempotent : IntersectionBlock → MonoidAlgebra P.k
      (ambient.base.comap
        (AmbientLocalGroup P reference psi w quotient ambient).subtype)}
    (intersectionBlocks :
      BlockIdempotentDecomposition intersectionBlockIdempotent)
    (intersectionBrauerInjective : IrreducibleBrauerCharacterInjectivity
      (intersectionLocalBaseRoot localInflation ambient))
    (intersectionCentralCharacters :
      BlockCentralCharacterCatalogue intersectionBlocks)
    (idempotentMatch : IntersectionBaseSelectedIdempotentMatch
      fixedLocal initialGlobal
      base intersectionBlockIdempotent intersectionBlocks
      intersectionBrauerInjective) :
    BlockInducesTo
      ((AmbientLocalGroup P reference psi w quotient ambient).comap
        ambient.base.subtype)
      (intersectionCentralCharacters.alongMulEquiv
        (subgroupIntersectionEquiv
          (AmbientLocalGroup P reference psi w quotient ambient) ambient.base))
      base.globalCentralCharacters
      (intersectionSelectedLocalBlock intersectionBlocks
        intersectionBrauerInjective)
      (irreducibleBrauerCharacterBlock
        (baseGlobalRoot
          (characterExtensionsOfLocalAndGlobal fixedLocal initialGlobal))
        base.globalBrauerInjective base.globalBlocks
        (baseGlobalBrauer
          (characterExtensionsOfLocalAndGlobal fixedLocal initialGlobal))) := by
  have hlocal := intersectionSelectedCentralCharacter_eq_base
    intersectionCentralCharacters idempotentMatch
  have hlocal' :
      (intersectionCentralCharacters.alongMulEquiv
          (subgroupIntersectionEquiv
            (AmbientLocalGroup P reference psi w quotient ambient)
            ambient.base)).centralCharacter
          (intersectionSelectedLocalBlock intersectionBlocks
            intersectionBrauerInjective) =
        base.localCentralCharacters.centralCharacter
          (baseSelectedLocalBlock base) :=
    hlocal
  have hbase := base.inductionEquality
  unfold BlockInducesTo at hbase ⊢
  rw [hlocal']
  exact hbase

end ModularRep.PaperProofs.SporadicFi24P3PositiveQBaseInductionTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
