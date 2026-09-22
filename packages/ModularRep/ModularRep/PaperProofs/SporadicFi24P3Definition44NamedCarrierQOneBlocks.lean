import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQOneExtensions
import ModularRep.PaperProofs.SpathQOneIntermediateBlockTransport

/-!
# Q=1 block transport for the same constructed extension packet

The local character is the literal restriction of the chosen global
extension. At each intermediate subgroup, transport its actual global
Brauer character and complete block catalogue to the identical local group.
This proves self-induction without a whole-field root-lift equality.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQOneBlocks

open ModularRep
open ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SpathPositiveQTopBlockChoice
open ModularRep.PaperProofs.SpathQOneCharacterExtensions
open ModularRep.PaperProofs.SpathQOneIntermediateBlockTransport
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQOneExtensions

universe u

local instance subgroupFintype {G : Type u} [Group G] [Finite G] (H : Subgroup G) :
    Fintype H := Fintype.ofFinite H

theorem localRestrictionOfGlobalChoice
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P} {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation : QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    (globalChoice : ChosenGlobalExtensionData ambient)
    (localData : QOneLocalTransportData localInflation ambient)
    (J : Subgroup ambient.A)
    (global : QOneIntermediateGlobalBlockData
      (characterExtensionsOfGlobal globalChoice localData) J) :
    PrimeRegularClassFunction.pullback
        (intermediateLocalToAmbientLocal (w := w) ambient J)
        (characterExtensionsOfGlobal globalChoice localData).localExtension.1.1 =
      (qOneIntermediateLocalBrauer localData.quotientRadical_eq_bot J
        global.globalRoot global.globalBrauer).1 := by
  apply PrimeRegularClassFunction.ext
  intro x
  let eJ := qOneIntermediateLocalEquiv ambient localData.quotientRadical_eq_bot J
  exact congrArg (fun chi => chi (PrimeRegularElement.map eJ.toMonoidHom x))
    global.globalRestriction

/-- Construct the complete literal intermediate block equality from its
single global catalogue.  The local catalogue and the induction equality are
not source fields.  The local Navarro provenance reuses only the global
coefficient field metadata, which is the sole field of that provenance
record. -/
noncomputable def intermediateBlockEqualityAtOfGlobalChoice
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation :
      QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    (globalChoice : ChosenGlobalExtensionData ambient)
    (localData : QOneLocalTransportData localInflation ambient)
    (J : Subgroup ambient.A)
    (global : QOneIntermediateGlobalBlockData
      (characterExtensionsOfGlobal globalChoice localData) J) :
    IntermediateBlockEqualityAt P reference psi w quotient weight
      localInflation ambient
        (characterExtensionsOfGlobal globalChoice localData) J := by
  let e := qOneIntermediateLocalEquiv ambient
    localData.quotientRadical_eq_bot J
  have he : e.toMonoidHom =
      (IntermediateLocalNormalizer (w := w) ambient J).subtype := by
    ext x
    rfl
  let globalInjective :
      IrreducibleBrauerCharacterInjectivity global.globalRoot :=
    irreducibleBrauerCharacterInjectivity_of_rootEmbedding global.globalRoot
  let localRoot := qOneIntermediateLocalRoot
    localData.quotientRadical_eq_bot J global.globalRoot
  let localBrauer := qOneIntermediateLocalBrauer
    localData.quotientRadical_eq_bot J global.globalRoot global.globalBrauer
  let localInjective : IrreducibleBrauerCharacterInjectivity localRoot :=
    irreducibleBrauerCharacterInjectivity_of_rootEmbedding localRoot
  have hselected :
      irreducibleBrauerCharacterBlock localRoot localInjective
          (global.blocks.alongMulEquiv e.symm) localBrauer =
        irreducibleBrauerCharacterBlock global.globalRoot globalInjective
          global.blocks global.globalBrauer := by
    exact irreducibleBrauerCharacterBlock_alongMulEquiv
      global.globalRoot globalInjective e.symm localInjective
        global.blocks global.globalBrauer
  have hinduction := blockInducesTo_self_of_equiv_subtype
    (k := P.k)
    (H := IntermediateLocalNormalizer (w := w) ambient J)
    global.blocks global.centralCharacters e he
    (irreducibleBrauerCharacterBlock global.globalRoot globalInjective
      global.blocks global.globalBrauer)
  exact {
    globalRoot := global.globalRoot
    globalBrauer := global.globalBrauer
    globalRestriction := global.globalRestriction
    localRoot := localRoot
    localBrauer := localBrauer
    localRestriction := localRestrictionOfGlobalChoice globalChoice localData J global
    GlobalBlock := global.Block
    LocalBlock := global.Block
    globalBlockIdempotent := global.blockIdempotent
    localBlockIdempotent := fun b =>
      MonoidAlgebra.domCongr P.k P.k e.symm (global.blockIdempotent b)
    globalBlocks := global.blocks
    localBlocks := global.blocks.alongMulEquiv e.symm
    globalBrauerInjective := globalInjective
    localBrauerInjective := localInjective
    globalCentralCharacters := global.centralCharacters
    localCentralCharacters := global.centralCharacters.alongMulEquiv e.symm
    globalCentralCharactersNavarro311 :=
      global.centralCharactersNavarro311
    localCentralCharactersNavarro311 :=
      ⟨global.centralCharactersNavarro311.fieldSource⟩
    inductionEquality := by
      simpa only [hselected] using hinduction }


end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQOneBlocks



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
