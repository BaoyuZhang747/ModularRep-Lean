import ModularRep.PaperProofs.TypeCOddTwoOriginalChosenExtensions
import ModularRep.CentralCharacterCovering
import ModularRep.IBrBlockEquivTransport

/-!
# Every actual intermediate group from the same original chosen packet

For J containing the original base, H is J intersect the SAME original
ambient normalizer. The already proved Frattini equality identifies base H
with J. The original chosen intermediate packet is transported through
these actual membership coordinates, including its own characters,
complete primitive catalogues and block-induction equality.

No induction theorem, catalogue match, root agreement, or final witness is
an added input. Navarro311 provenance reuses only the original fieldSource.
Finite root-convention binding and the complete target remain separate.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeCOddTwoOriginalIntermediateTransport

open ModularRep CharacterWeight FDRepSimpleClassKZero
open CyclicOuterLemma37Concrete EvenFieldFLZSourceConditions EvenFieldFLZBAWGoodFamily
open OddTwoLiteralSpathTarget TypeCOddTwoOriginalBlockMatching
open TypeCOddTwoOriginalReferenceAmbient TypeCOddTwoOriginalChosenExtensions

universe u

variable {n : ℕ} {F : Type u} [Field F] [Finite F]
variable {P : Problem n F} (D : Definition41 P) (b : P.Block)
variable (reference psi : Definition35Brauer (P.blockProblem b))

local instance intermediateTransportSubgroupFintype {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) : Fintype H := Fintype.ofFinite _

/- The specified transport is checked first on short generic group names.
The actual application below supplies its original packet and proved square. -/
private theorem transportedInduction
    {p : ℕ} {k K G G' B L : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group G] [Fintype G] [Group G'] [Fintype G'] [Fintype B] [Fintype L]
    (H : Subgroup G) (H' : Subgroup G')
    (eG : G ≃* G') (eH : H ≃* H')
    (square : eG.toMonoidHom.comp H.subtype = H'.subtype.comp eH.toMonoidHom)
    (rG : PrimeRegularRootEmbedding p k K G)
    (rH : PrimeRegularRootEmbedding p k K H)
    (injG : IrreducibleBrauerCharacterInjectivity rG)
    (injH : IrreducibleBrauerCharacterInjectivity rH)
    {bG : B → k[G]} {bH : L → k[H]}
    (blocksG : BlockIdempotentDecomposition bG)
    (blocksH : BlockIdempotentDecomposition bH)
    (catG : BlockCentralCharacterCatalogue blocksG)
    (catH : BlockCentralCharacterCatalogue blocksH)
    (chiG : IBr rG) (chiH : IBr rH)
    (induces : BlockInducesTo H catH catG
      (irreducibleBrauerCharacterBlock rH injH blocksH chiH)
      (irreducibleBrauerCharacterBlock rG injG blocksG chiG)) :
    BlockInducesTo H' (catH.alongMulEquiv eH) (catG.alongMulEquiv eG)
      (irreducibleBrauerCharacterBlock (rH.alongMulEquiv eH)
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _)
        (blocksH.alongMulEquiv eH)
        (IrreducibleBrauerCharacter.alongMulEquiv rH eH chiH))
      (irreducibleBrauerCharacterBlock (rG.alongMulEquiv eG)
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _)
        (blocksG.alongMulEquiv eG)
        (IrreducibleBrauerCharacter.alongMulEquiv rG eG chiG)) := by
  rw [irreducibleBrauerCharacterBlock_alongMulEquiv rH injH eH
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) blocksH chiH,
    irreducibleBrauerCharacterBlock_alongMulEquiv rG injG eG
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) blocksG chiG]
  exact blockInducesTo_alongMulEquiv H H' eG eH square catH catG
    (catH.alongMulEquiv eH) (catG.alongMulEquiv eG) rfl rfl induces

private def transportedProvenance
    {p : ℕ} {k G G' B : Type u}
    [Field k] [CharP k p] [IsAlgClosed k]
    [Group G] [Fintype G] [Group G'] [Fintype G'] [Fintype B]
    {hp : p.Prime} {bG : B → k[G]}
    {blocks : BlockIdempotentDecomposition bG}
    (e : G ≃* G') (cat : BlockCentralCharacterCatalogue blocks)
    (provenance : Navarro311CatalogueProvenance p hp blocks cat) :
    Navarro311CatalogueProvenance p hp (blocks.alongMulEquiv e)
      (cat.alongMulEquiv e) :=
  ⟨provenance.fieldSource⟩

variable (J : Subgroup (selectedMatched D b psi).ambient.A)

local instance intermediateTransportReferenceAmbientGroup :
    Group (selectedReferenceAmbient D b reference psi).A :=
  (selectedMatched D b psi).ambient.groupA

local instance intermediateTransportJGroup : Group ↥J :=
  @Subgroup.toGroup (selectedMatched D b psi).ambient.A
    (selectedMatched D b psi).ambient.groupA J

def directH : Subgroup (selectedMatched D b psi).ambient.A :=
  J ⊓ OwnLocalGroup D b psi

theorem directH_le : directH D b psi J ≤ OwnLocalGroup D b psi := inf_le_right

variable (hJ : (selectedMatched D b psi).ambient.base ≤ J)

include hJ in
theorem base_inter_le_directH :
    (selectedMatched D b psi).ambient.base ⊓ OwnLocalGroup D b psi ≤
      directH D b psi J := inf_le_inf hJ le_rfl

include hJ in
theorem global_subgroup_eq :
    (selectedMatched D b psi).ambient.base ⊔ directH D b psi J = J :=
  (TypeCIntermediateNormalizerComparison.intermediate_eq_join_inf
    (selectedMatched D b psi).ambient.base (OwnLocalGroup D b psi)
    J hJ (selectedMatched_frattini D b psi)).symm

/-- The original packet at the computed H, including its own restrictions
and actual block-induction proof. No intermediate packet is a new input. -/
def sourceIntermediate :=
  (selectedMatched D b psi).intermediate (directH D b psi J)
    (directH_le D b psi J) (base_inter_le_directH D b psi J hJ)

def globalEquiv : ↥((selectedMatched D b psi).ambient.base ⊔ directH D b psi J) ≃* J :=
  MulEquiv.subgroupCongr (global_subgroup_eq D b psi J hJ)

abbrev OldLocal := P.IntermediateLocal (selectedMatched D b psi).ambient
  (directH D b psi J)

abbrev NewLocal : Subgroup ↥J :=
  (ReferenceLocalGroup D b reference psi :
    Subgroup (selectedMatched D b psi).ambient.A).comap J.subtype

/-- The direct-H and J-normalizer presentations retain each ambient element. -/
def localEquiv : OldLocal D b psi J ≃* NewLocal D b reference psi J where
  toFun x := ⟨globalEquiv D b psi J hJ x.1, by
    exact (ambientLocalEquiv D b reference psi ⟨x.1.1, x.2.2⟩).2⟩
  invFun x := ⟨(globalEquiv D b psi J hJ).symm x.1, by
    change x.1.1 ∈ J ⊓ OwnLocalGroup D b psi
    refine ⟨x.1.2, ?_⟩
    exact ((ambientLocalEquiv D b reference psi).symm ⟨x.1.1, x.2⟩).2⟩
  left_inv x := Subtype.ext ((globalEquiv D b psi J hJ).symm_apply_apply x.1)
  right_inv x := Subtype.ext ((globalEquiv D b psi J hJ).apply_symm_apply x.1)
  map_mul' x y := Subtype.ext (map_mul (globalEquiv D b psi J hJ) x.1 y.1)

@[simp] theorem globalEquiv_value
    (x : ↥((selectedMatched D b psi).ambient.base ⊔ directH D b psi J)) :
    (globalEquiv D b psi J hJ x).1 = x.1 := rfl

@[simp] theorem localEquiv_value (x : OldLocal D b psi J) :
    (localEquiv D b reference psi J hJ x).1.1 = x.1.1 := rfl

/-- The square used by actual coefficient-restriction block induction. -/
theorem local_global_square :
    (globalEquiv D b psi J hJ).toMonoidHom.comp (OldLocal D b psi J).subtype =
      (NewLocal D b reference psi J).subtype.comp
        (localEquiv D b reference psi J hJ).toMonoidHom := by
  apply MonoidHom.ext
  intro x
  rfl

/-- The square used by the SAME original local extension restriction. -/
theorem local_ambient_square :
    (ambientLocalEquiv D b reference psi).symm.toMonoidHom.comp
        (intermediateLocalToAmbientLocal (w := blockEquiv D b psi)
          (selectedReferenceAmbient D b reference psi) J) =
      (P.intermediateLocalMap (selectedMatched D b psi).ambient
        (TypeCOddTwoOriginalBlockMatching.selectedRadical D b psi)
        (directH D b psi J) (directH_le D b psi J)).comp
          (localEquiv D b reference psi J hJ).symm.toMonoidHom := by
  apply MonoidHom.ext
  intro x
  rfl

/-- The actual original global restriction, transported to J. -/
theorem global_restriction :
    PrimeRegularClassFunction.pullback J.subtype
        (referenceExtensions D b reference psi).globalExtension.1.1 =
      (IrreducibleBrauerCharacter.alongMulEquiv
        (sourceIntermediate D b psi J hJ).globalRoot (globalEquiv D b psi J hJ)
        (sourceIntermediate D b psi J hJ).globalBrauer).1 := by
  apply PrimeRegularClassFunction.ext
  intro x
  exact congrArg
    (fun f : PrimeRegularClassFunction P.K
        ↥((selectedMatched D b psi).ambient.base ⊔ directH D b psi J) 2 =>
      f (PrimeRegularElement.map (globalEquiv D b psi J hJ).symm.toMonoidHom x))
    (sourceIntermediate D b psi J hJ).globalRestriction

/-- The local extension is the chosen one already transported to the SAME
ambient normalizer; the inclusion square transports its own restriction. -/
theorem local_restriction :
    PrimeRegularClassFunction.pullback
        (intermediateLocalToAmbientLocal (w := blockEquiv D b psi)
          (selectedReferenceAmbient D b reference psi) J)
        (referenceExtensions D b reference psi).localExtension.1.1 =
      (IrreducibleBrauerCharacter.alongMulEquiv
        (sourceIntermediate D b psi J hJ).localRoot (localEquiv D b reference psi J hJ)
        (sourceIntermediate D b psi J hJ).localBrauer).1 := by
  apply PrimeRegularClassFunction.ext
  intro x
  exact congrArg
    (fun f : PrimeRegularClassFunction P.K (OldLocal D b psi J) 2 =>
      f (PrimeRegularElement.map (localEquiv D b reference psi J hJ).symm.toMonoidHom x))
    (sourceIntermediate D b psi J hJ).localRestriction

/-- Name the unchanged dependent result type separately from its specified
record construction, so its coordinate indices are elaborated once. -/
abbrev IntermediateOutput := IntermediateBlockEqualityAt (P.blockProblem b) reference psi
    (blockEquiv D b psi) (referenceSource P b reference psi)
    (quotientPacket D b reference psi) (localInflation D b reference psi)
    (selectedReferenceAmbient D b reference psi) (referenceExtensions D b reference psi) J

/-- Complete specified intermediate data, obtained solely from the original
chosen intermediate packet and the proved actual group coordinates. -/
def intermediateAt : IntermediateOutput D b reference psi J := by
  let I := sourceIntermediate D b psi J hJ
  let eG := globalEquiv D b psi J hJ
  let eL := localEquiv D b reference psi J hJ
  letI := I.fintypeGlobalBlock
  letI := I.fintypeLocalBlock
  let rG := I.globalRoot.alongMulEquiv eG
  let rL := I.localRoot.alongMulEquiv eL
  let chiG := IrreducibleBrauerCharacter.alongMulEquiv I.globalRoot eG I.globalBrauer
  let chiL := IrreducibleBrauerCharacter.alongMulEquiv I.localRoot eL I.localBrauer
  let injG : IrreducibleBrauerCharacterInjectivity rG :=
    irreducibleBrauerCharacterInjectivity_of_rootEmbedding rG
  let injL : IrreducibleBrauerCharacterInjectivity rL :=
    irreducibleBrauerCharacterInjectivity_of_rootEmbedding rL
  refine
    { globalRoot := rG
      globalBrauer := chiG
      globalRestriction := global_restriction D b reference psi J hJ
      localRoot := rL
      localBrauer := chiL
      localRestriction := local_restriction D b reference psi J hJ
      GlobalBlock := I.GlobalBlock
      LocalBlock := I.LocalBlock
      fintypeGlobalBlock := I.fintypeGlobalBlock
      fintypeLocalBlock := I.fintypeLocalBlock
      globalBlockIdempotent := fun x => MonoidAlgebra.domCongr P.k P.k eG (I.globalBlockIdempotent x)
      localBlockIdempotent := fun x => MonoidAlgebra.domCongr P.k P.k eL (I.localBlockIdempotent x)
      globalBlocks := I.globalBlocks.alongMulEquiv eG
      localBlocks := I.localBlocks.alongMulEquiv eL
      globalBrauerInjective := injG
      localBrauerInjective := injL
      globalCentralCharacters := I.globalCentralCharacters.alongMulEquiv eG
      localCentralCharacters := I.localCentralCharacters.alongMulEquiv eL
      globalCentralCharactersNavarro311 := transportedProvenance eG
        I.globalCentralCharacters I.globalCentralCharactersNavarro311
      localCentralCharactersNavarro311 := transportedProvenance eL
        I.localCentralCharacters I.localCentralCharactersNavarro311
      inductionEquality := ?_ }
  exact transportedInduction (OldLocal D b psi J) (NewLocal D b reference psi J) eG eL
    (local_global_square D b reference psi J hJ)
    I.globalRoot I.localRoot I.globalBrauerInjective I.localBrauerInjective
    I.globalBlocks I.localBlocks I.globalCentralCharacters I.localCentralCharacters
    I.globalBrauer I.localBrauer I.inductionEquality

/-- Every actual J containing the unchanged base is covered. -/
def intermediateSource : IntermediateBlockSource (P.blockProblem b) reference psi
    (blockEquiv D b psi) (referenceSource P b reference psi)
    (quotientPacket D b reference psi) (localInflation D b reference psi)
    (selectedReferenceAmbient D b reference psi) (referenceExtensions D b reference psi) where
  equalityAt J hJ := intermediateAt D b reference psi J hJ

end ModularRep.PaperProofs.TypeCOddTwoOriginalIntermediateTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
