import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllPairs
import ModularRep.PaperProofs.SpathPositiveQBaseBlockTransport

/-! Specified base blocks in the fixed root convention. The local root
equation is internal retained evidence from the local-extension construction.
No unrestricted root law or selected block equality is a source input. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalBaseBlock

open Formalisation ModularRep
open ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZCentrelessCentralKernel
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SpathPositiveQBaseBlock
open ModularRep.PaperProofs.SpathPositiveQBaseBlockTransport
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24Definition35Operations
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllPairs
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction

universe u
local instance subgroupFintype {G : Type u} [Group G] [Finite G] (H : Subgroup G) :
    Fintype H := Fintype.ofFinite H

theorem selectedBaseLocalBlock_eq_source_of_canonical
    {P : Definition35Problem.{u}} (hcenter : Subgroup.center P.H = ⊥)
    {reference psi : Definition35Brauer P} {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation : QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    (extensions : SpathCharacterExtensions P reference psi w quotient weight localInflation ambient)
    (source : CanonicalRawReduction P.iota (selectedCharacterWeight P.blockSource P.block w))
    (hroot : localInflation.iota.lift = source.toRaw.quotientRoot.lift)
    (compatibility : CanonicalLocalBlockCompatibility P.iota P.blockSource.operations) :
    let W := selectedCharacterWeight P.blockSource P.block w
    let O := P.blockSource.operations
    selectedBaseLocalBlock (baseBlockCatalogueDataOfOperations hcenter extensions) =
      O.inflateToNormalizer W.subgroup
        (O.localCharacterBlock W.subgroup W.localCharacter W.defectZero) := by
  let W := selectedCharacterWeight P.blockSource P.block w
  let O := P.blockSource.operations
  let localData := O.inflatedNormalizerBlockData W.subgroup
  let := localData.fintypeBlock
  let iotaN := positiveQSourceNormalizerRoot P hcenter reference w localInflation
  let phiN := positiveQSourceNormalizerBrauer P hcenter reference w localInflation
  let e := positiveQBaseLocalEquiv P hcenter extensions
  have hphiN : phiN.1 = source.localBrauer.1 := by
    apply PrimeRegularClassFunction.ext
    intro n
    exact (positiveQSourceNormalizerBrauer_isReductionOf_inflatedSelectedLocal
      P hcenter reference w weight localInflation n).symm.trans (source.localBrauer_reduction n)
  have hrootN : iotaN.lift = source.normalizerRoot.lift := by
    funext z
    exact (localInflation.iota.alongMulEquiv_lift
      (positiveQQuotientNormalizerEquiv P hcenter reference w).symm z).trans
      ((congrFun hroot z).trans (source.toRaw.normalizerRoot_lift z).symm)
  have hlift : (baseLocalRoot extensions).lift = source.normalizerRoot.lift :=
    (baseLocalRoot_lift_eq_positiveQSourceNormalizerRoot hcenter extensions).trans hrootN
  have hphi : (baseLocalBrauer extensions).1 =
      PrimeRegularClassFunction.pullback e.symm.toMonoidHom source.localBrauer.1 :=
    (baseLocalBrauer_eq_pullback_positiveQBaseLocalEquiv hcenter extensions).trans
      (congrArg (PrimeRegularClassFunction.pullback e.symm.toMonoidHom) hphiN)
  change irreducibleBrauerCharacterBlock (baseLocalRoot extensions)
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _)
      (localData.blocks.alongMulEquiv e) (baseLocalBrauer extensions) = _
  exact (irreducibleBrauerCharacterBlock_alongMulEquiv_of_lift_eq
    (iotaG := source.normalizerRoot)
    (hinjG := irreducibleBrauerCharacterInjectivity_of_rootEmbedding _)
    (iotaH := baseLocalRoot extensions)
    (hinjH := irreducibleBrauerCharacterInjectivity_of_rootEmbedding _)
    (e := e) (D := localData.blocks) (phiG := source.localBrauer)
    (phiH := baseLocalBrauer extensions) (hlift := hlift) (hphi := hphi)).trans
      (compatibility.normalizerBrauerBlock_eq_inflateToNormalizer W source)

variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

local instance blockStabilizerFinite (b : ActualBlock (k := k) (X := X)) :
    Finite (BlockStabilizer b) :=
  Finite.of_injective (fun a : BlockStabilizer b ↦ (a.1.unop : X → X))
    (fun _ _ h ↦ Subtype.ext
      (MulOpposite.unop_injective (DFunLike.coe_injective h)))

def baseBlockOfCanonicalOperations
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
    (localReduction : ∀ (b : ActualBlock (k := k) (X := X)) (w : LiteralWeightFibre R.1 b),
      SelectedLocalReductionSource R.1 b w)
    (b : ActualBlock (k := k) (X := X))
    (P : Definition35Problem.{u}) (hP : P = blockProblem iota hinj R localReduction b)
    (hcenter : Subgroup.center P.H = ⊥)
    {reference psi : Definition35Brauer P} {w : Definition35Weight P}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation : QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi
      (centerlessCentralQuotientBrauerSourceFromReference P hcenter reference psi)}
    (extensions : SpathCharacterExtensions P reference psi w
      (centerlessCentralQuotientBrauerSourceFromReference P hcenter reference psi)
      weight localInflation ambient)
    (source : CanonicalRawReduction P.iota (selectedCharacterWeight P.blockSource P.block w))
    (hroot : localInflation.iota.lift = source.toRaw.quotientRoot.lift)
    (compatibility : CanonicalLocalBlockCompatibility P.iota P.blockSource.operations)
    (fieldSource : SpathCoefficientField P.p P.k P.iota.prime) :
    BaseBlockInducesFromSelectedWeight extensions := by
  let base := baseBlockCatalogueDataOfOperations hcenter extensions
  refine {
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
    globalCentralCharactersNavarro311 := ⟨fieldSource⟩
    localCentralCharactersNavarro311 := ⟨fieldSource⟩
    inductionEquality := ?_ }
  apply baseBlockInducesTo_of_selectedBlockEqualities hcenter extensions
  constructor
  · subst P
    exact selectedBaseGlobalBlock_eq_block_ofOperations_centerless
      (iota := iota) (hinj := hinj) (blockSource := R.1) (block := b)
      (gamma := blockField b) (gammaBlock_fixed := blockField_fixed b)
      (brauerSupport := literalOperationsBrauerSupport iota hinj R)
      (localReduction := localReduction b) hcenter extensions
  · exact selectedBaseLocalBlock_eq_source_of_canonical hcenter extensions source hroot compatibility

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalBaseBlock


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
