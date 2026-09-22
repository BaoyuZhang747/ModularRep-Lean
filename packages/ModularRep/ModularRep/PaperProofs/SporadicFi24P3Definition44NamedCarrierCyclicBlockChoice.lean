import ModularRep.CyclicBrauerTopBlockFromBaseInduction
import ModularRep.IBrBlockEquivTransport
import ModularRep.SubgroupIntervalTwo
import ModularRep.PaperProofs.SpathPositiveQBaseBlock
import ModularRep.PaperProofs.SpathPositiveQTopBlockChoice

/-!
# Cyclic block choice on the fixed Späth carriers

Choose a global extension in the block induced from the fixed local extension,
then use the quotient order bound to prove every intermediate block equality.
The input contains only the existing base relation, individual extensions,
actual block catalogues, and the lower covering, twist and interval sources.
The intersection catalogue and its base induction relation are derived from
that same base relation. No condition on the rank or nontriviality of the
selected radical is used.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCyclicBlockChoice

open ModularRep
open ModularRep.FDRepSimpleClassKZero
open ModularRep.NavarroBrauerRestrictionCovering
open ModularRep.NavarroCoveringBrauerExtension
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SpathPositiveQBaseBlock
open ModularRep.PaperProofs.SpathPositiveQTopBlockChoice
open Representation.Extension

universe u

noncomputable local instance subgroupFintype
    {G : Type u} [Group G] [Finite G] (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

local instance definition35ProblemPrime (P : Definition35Problem.{u}) :
    Fact P.p.Prime :=
  ⟨P.iota.prime⟩

/-- The local character on `N_A(Q) \cap \bar G`, in the presentation used by
the covering theorems in the cyclic step. -/
abbrev cyclicLocalBaseRoot
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

abbrev cyclicLocalBaseBrauer
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    (localInflation : QuotientLocalInflationSource P reference w weight)
    (ambient : SpathAmbientGroup P reference psi quotient) :
    IBr (cyclicLocalBaseRoot localInflation ambient) :=
  IrreducibleBrauerCharacter.alongMulEquiv localInflation.iota
    (canonicalLocalBaseEquiv ambient) localInflation.brauer

/-- Lower source data for the cyclic choice, with actual block catalogues.
There is no selected top or intermediate block relation among the fields. -/
structure CyclicBlockSource
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation :
      QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    (fixedLocal : FixedLocalExtensionData localInflation ambient)
    (initialGlobal : ChosenGlobalExtensionData ambient)
    (base : BaseBlockInducesFromSelectedWeight
      (characterExtensionsOfLocalAndGlobal fixedLocal initialGlobal)) where
  AmbientBlock : Type u
  LocalBlock : Type u
  [fintypeAmbientBlock : Fintype AmbientBlock]
  [fintypeLocalBlock : Fintype LocalBlock]
  ambientBlockIdempotent : AmbientBlock → MonoidAlgebra P.k ambient.A
  localBlockIdempotent : LocalBlock → MonoidAlgebra P.k
    (AmbientLocalGroup P reference psi w quotient ambient)
  ambientBlocks : BlockIdempotentDecomposition ambientBlockIdempotent
  localBlocks : BlockIdempotentDecomposition localBlockIdempotent
  ambientBrauerInjective :
    IrreducibleBrauerCharacterInjectivity initialGlobal.ambientRoot
  localBrauerInjective :
    IrreducibleBrauerCharacterInjectivity fixedLocal.localAmbientRoot
  ambientCentralCharacters : BlockCentralCharacterCatalogue ambientBlocks
  localCentralCharacters : BlockCentralCharacterCatalogue localBlocks
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
      (cyclicLocalBaseRoot localInflation ambient).lift
          (((zeta : P.kˣ) : P.k)) =
        fixedLocal.localAmbientRoot.lift (((zeta : P.kˣ) : P.k))
  quotientCyclic : IsCyclic (ambient.A ⧸ ambient.base)
  quotientCard_le_two : Nat.card (ambient.A ⧸ ambient.base) ≤ 2
  interval : CentralBrauerInterval (p := P.p)
    (ambientRadical P reference psi w quotient ambient)
    (AmbientLocalGroup P reference psi w quotient ambient)
  intervalSource : Navarro414IntervalCentralCharacterSource interval
    localBlocks localCentralCharacters

attribute [instance]
  CyclicBlockSource.fintypeAmbientBlock
  CyclicBlockSource.fintypeLocalBlock

theorem groupAlgebra_domCongr_roundtrip
    {k G H : Type u} [Field k] [Group G] [Group H]
    (e : G ≃* H) (f : k[H]) :
    MonoidAlgebra.domCongr k k e (MonoidAlgebra.domCongr k k e.symm f) = f := by
  ext x
  simp only [MonoidAlgebra.coeff_domCongr, MulEquiv.symm_symm,
    MulEquiv.apply_symm_apply]

/-- Späth's cyclic choice, followed by the two-point interval argument, for
one fixed matched pair. -/
theorem exists_extensions_and_intermediate_blocks
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation :
      QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    (S9295 : Navarro9295BrauerRestrictionCoveringPrinciple P.p P.k P.K)
    (S9495 : Navarro9495BrauerCoveringPrinciple P.p P.k P.K)
    (S820 : Navarro820CyclicBrauerTwistPrinciple P.p P.k P.K)
    (fixedLocal : FixedLocalExtensionData localInflation ambient)
    (initialGlobal : ChosenGlobalExtensionData ambient)
    (base : BaseBlockInducesFromSelectedWeight
      (characterExtensionsOfLocalAndGlobal fixedLocal initialGlobal))
    (source : CyclicBlockSource fixedLocal initialGlobal base) :
    ∃ extensions : SpathCharacterExtensions P reference psi w quotient weight
        localInflation ambient,
      Nonempty (IntermediateBlockSource P reference psi w quotient weight
        localInflation ambient extensions) := by
  let initialExtensions :=
    characterExtensionsOfLocalAndGlobal fixedLocal initialGlobal
  let H := AmbientLocalGroup P reference psi w quotient ambient
  let d := subgroupIntersectionEquiv H ambient.base
  let intersectionBlocks := base.localBlocks.alongMulEquiv d.symm
  let intersectionCatalogue := base.localCentralCharacters.alongMulEquiv d.symm
  let intersectionInjective :
      IrreducibleBrauerCharacterInjectivity (cyclicLocalBaseRoot localInflation ambient) :=
    irreducibleBrauerCharacterInjectivity_of_rootEmbedding
      (cyclicLocalBaseRoot localInflation ambient)
  have hblock :
      irreducibleBrauerCharacterBlock (cyclicLocalBaseRoot localInflation ambient)
          intersectionInjective intersectionBlocks
          (cyclicLocalBaseBrauer localInflation ambient) =
        irreducibleBrauerCharacterBlock (baseLocalRoot initialExtensions)
          base.localBrauerInjective base.localBlocks (baseLocalBrauer initialExtensions) := by
    apply irreducibleBrauerCharacterBlock_alongMulEquiv_of_lift_eq
      (baseLocalRoot initialExtensions) base.localBrauerInjective
      (cyclicLocalBaseRoot localInflation ambient) intersectionInjective
      d.symm base.localBlocks (baseLocalBrauer initialExtensions)
      (cyclicLocalBaseBrauer localInflation ambient)
    · exact funext fun z =>
        ((cyclicLocalBaseRoot localInflation ambient).alongMulEquiv_lift
          (ambientLocalBaseEquivIntermediateLocalBase ambient) z).symm
    · apply PrimeRegularClassFunction.ext
      intro x
      rfl
  have hcatalogue (b : base.LocalBlock) :
      (intersectionCatalogue.alongMulEquiv d).centralCharacter b =
        base.localCentralCharacters.centralCharacter b := by
    apply centralCharacterAlongMulEquiv_eq_of_blockIdempotent
      d intersectionCatalogue base.localCentralCharacters
    apply Subtype.ext
    exact groupAlgebra_domCongr_roundtrip d
      (show P.k[H.comap ambient.base.subtype] from base.localBlockIdempotent b)
  have hbase : BlockInducesTo (H.comap ambient.base.subtype)
      (intersectionCatalogue.alongMulEquiv d) base.globalCentralCharacters
      (irreducibleBrauerCharacterBlock (cyclicLocalBaseRoot localInflation ambient)
        intersectionInjective intersectionBlocks
        (cyclicLocalBaseBrauer localInflation ambient))
      (irreducibleBrauerCharacterBlock (baseGlobalRoot initialExtensions)
        base.globalBrauerInjective base.globalBlocks (baseGlobalBrauer initialExtensions)) := by
    unfold BlockInducesTo
    rw [hblock, hcatalogue]
    exact base.inductionEquality
  obtain ⟨globalExtension, htop⟩ :=
    ModularRep.CyclicBrauerTopBlockFromBaseInduction.exists_global_extension_with_induced_block
        S9295 S9495 S820 ambient.base
        (AmbientLocalGroup P reference psi w quotient ambient)
        initialGlobal.ambientRoot (baseGlobalRoot initialExtensions)
        fixedLocal.localAmbientRoot
        (cyclicLocalBaseRoot localInflation ambient)
        source.globalRootAgreement source.localRootAgreement
        source.fieldSource source.quotientCyclic
        source.ambientBlocks base.globalBlocks source.localBlocks
        intersectionBlocks source.ambientBrauerInjective
        base.globalBrauerInjective source.localBrauerInjective
        intersectionInjective
        source.ambientCentralCharacters base.globalCentralCharacters
        source.localCentralCharacters intersectionCatalogue
        (baseGlobalBrauer initialExtensions)
        (cyclicLocalBaseBrauer localInflation ambient)
        initialGlobal.globalExtension fixedLocal.localExtension
        (ambientRadical P reference psi w quotient ambient)
        source.interval source.intervalSource
        hbase
  let chosenGlobal : ChosenGlobalExtensionData ambient := {
    ambientRoot := initialGlobal.ambientRoot
    globalExtension := globalExtension }
  let extensions :=
    characterExtensionsOfLocalAndGlobal fixedLocal chosenGlobal
  let baseForChosen : BaseBlockInducesFromSelectedWeight extensions := {
    GlobalBlock := base.GlobalBlock
    LocalBlock := base.LocalBlock
    fintypeGlobalBlock := base.fintypeGlobalBlock
    fintypeLocalBlock := base.fintypeLocalBlock
    globalBlockIdempotent := base.globalBlockIdempotent
    localBlockIdempotent := base.localBlockIdempotent
    globalBlocks := base.globalBlocks
    localBlocks := base.localBlocks
    globalBrauerInjective := base.globalBrauerInjective
    localBrauerInjective := base.localBrauerInjective
    globalCentralCharacters := base.globalCentralCharacters
    localCentralCharacters := base.localCentralCharacters
    globalCentralCharactersNavarro311 :=
      base.globalCentralCharactersNavarro311
    localCentralCharactersNavarro311 :=
      base.localCentralCharactersNavarro311
    inductionEquality := base.inductionEquality }
  let eA := (topToAmbientEquiv ambient).symm
  let eL := (topLocalToAmbientLocalEquiv (w := w) ambient).symm
  let topGlobalInjective :
      IrreducibleBrauerCharacterInjectivity (topGlobalRoot extensions) :=
    irreducibleBrauerCharacterInjectivity_of_rootEmbedding
      (topGlobalRoot extensions)
  let topLocalInjective :
      IrreducibleBrauerCharacterInjectivity (topLocalRoot extensions) :=
    irreducibleBrauerCharacterInjectivity_of_rootEmbedding
      (topLocalRoot extensions)
  have hsquare :
      eA.toMonoidHom.comp
          (AmbientLocalGroup P reference psi w quotient ambient).subtype =
        (IntermediateLocalNormalizer (w := w) ambient
          (⊤ : Subgroup ambient.A)).subtype.comp eL.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    rfl
  have htopTransport := blockInducesTo_alongMulEquiv
    (AmbientLocalGroup P reference psi w quotient ambient)
    (IntermediateLocalNormalizer (w := w) ambient
      (⊤ : Subgroup ambient.A))
    eA eL hsquare source.localCentralCharacters
    source.ambientCentralCharacters
    (source.localCentralCharacters.alongMulEquiv eL)
    (source.ambientCentralCharacters.alongMulEquiv eA)
    (b := irreducibleBrauerCharacterBlock fixedLocal.localAmbientRoot
      source.localBrauerInjective source.localBlocks fixedLocal.localExtension.1)
    (B := irreducibleBrauerCharacterBlock initialGlobal.ambientRoot
      source.ambientBrauerInjective source.ambientBlocks globalExtension.1)
    (b' := irreducibleBrauerCharacterBlock fixedLocal.localAmbientRoot
      source.localBrauerInjective source.localBlocks fixedLocal.localExtension.1)
    (B' := irreducibleBrauerCharacterBlock initialGlobal.ambientRoot
      source.ambientBrauerInjective source.ambientBlocks globalExtension.1)
    (by rfl) (by rfl) htop
  have hlocalBlock :
      irreducibleBrauerCharacterBlock
          (topLocalRoot extensions) topLocalInjective
          (source.localBlocks.alongMulEquiv eL)
          (topLocalBrauer extensions) =
        irreducibleBrauerCharacterBlock fixedLocal.localAmbientRoot
          source.localBrauerInjective source.localBlocks
          fixedLocal.localExtension.1 := by
    exact irreducibleBrauerCharacterBlock_alongMulEquiv
      fixedLocal.localAmbientRoot source.localBrauerInjective eL
      topLocalInjective source.localBlocks fixedLocal.localExtension.1
  have hglobalBlock :
      irreducibleBrauerCharacterBlock
          (topGlobalRoot extensions) topGlobalInjective
          (source.ambientBlocks.alongMulEquiv eA)
          (topGlobalBrauer extensions) =
        irreducibleBrauerCharacterBlock initialGlobal.ambientRoot
          source.ambientBrauerInjective source.ambientBlocks
          globalExtension.1 := by
    exact irreducibleBrauerCharacterBlock_alongMulEquiv
      initialGlobal.ambientRoot source.ambientBrauerInjective eA
      topGlobalInjective source.ambientBlocks globalExtension.1
  let topForChosen : TopBlockInducesFromFixedLocal extensions := {
    GlobalBlock := source.AmbientBlock
    LocalBlock := source.LocalBlock
    fintypeGlobalBlock := source.fintypeAmbientBlock
    fintypeLocalBlock := source.fintypeLocalBlock
    globalBlockIdempotent := fun B =>
      MonoidAlgebra.domCongr P.k P.k eA (source.ambientBlockIdempotent B)
    localBlockIdempotent := fun b =>
      MonoidAlgebra.domCongr P.k P.k eL (source.localBlockIdempotent b)
    globalBlocks := source.ambientBlocks.alongMulEquiv eA
    localBlocks := source.localBlocks.alongMulEquiv eL
    globalBrauerInjective := topGlobalInjective
    localBrauerInjective := topLocalInjective
    globalCentralCharacters := source.ambientCentralCharacters.alongMulEquiv eA
    localCentralCharacters := source.localCentralCharacters.alongMulEquiv eL
    globalCentralCharactersNavarro311 := ⟨source.fieldSource⟩
    localCentralCharactersNavarro311 := ⟨source.fieldSource⟩
    inductionEquality := by
      rw [hlocalBlock, hglobalBlock]
      exact htopTransport }
  refine ⟨extensions, ⟨?_⟩⟩
  exact IntermediateBlockSource.ofBaseOrTop
    (fun J hJ => subgroup_eq_base_or_top_of_quotient_card_le_two
      ambient.base source.quotientCard_le_two J hJ)
    (intermediateBlockEqualityAtBase baseForChosen)
    (intermediateBlockEqualityAtTop topForChosen)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCyclicBlockChoice


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
