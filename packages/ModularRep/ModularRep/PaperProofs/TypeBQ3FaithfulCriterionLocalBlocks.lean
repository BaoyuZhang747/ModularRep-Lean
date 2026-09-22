import ModularRep.PaperProofs.TypeBQ3PrincipalPairBlockChoice
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
import ModularRep.SemisimpleBlockSimpleClass

/-! Local block induction for an arbitrary supported block and the identity
ambient. The specified equality is needed only at the selected block index. -/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBQ3FaithfulCriterionLocalBlocks

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open TypeBQ3PrincipalPairBlockChoice
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction

universe u

variable {k K X Block NamedBlock : Type u}
variable [Field k] [Field K] [Group X] [Fintype X]
variable [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [MulAction (MulAut X)ᵐᵒᵖ Block] [Fintype NamedBlock]

local instance subgroupFintype (Q : Subgroup X) : Fintype Q := Fintype.ofFinite Q
local instance twoPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable (O : LocalBlockInductionOperations
  (p := 2) (k := k) (K := K) (G := X) (Block := Block))
variable (root : PrimeRegularRootEmbedding 2 k K X)
  (hinj : IrreducibleBrauerCharacterInjectivity root)
  {namedIdempotent : NamedBlock → k[X]}
  (namedBlocks : BlockIdempotentDecomposition namedIdempotent)
  (i : NamedBlock) (b : Block)
  (literalAt : O.ambientBlockData.blockIdempotent b = namedIdempotent i)
  (phi : IBrBlock root hinj namedBlocks i)

include literalAt in
/-- Support in the named decomposition identifies the same character's block
in the operations catalogue using one specified idempotent equality. -/
theorem ambientCharacterBlock :
    letI := O.ambientBlockData.fintypeBlock
    irreducibleBrauerCharacterBlock root hinj O.ambientBlockData.blocks phi.val = b := by
  letI := O.ambientBlockData.fintypeBlock
  let C := (simpleModuleClassEquivIBr root hinj).symm phi.val
  apply irreducibleBrauerCharacterBlock_eq_of_smul_eq_self
    root hinj O.ambientBlockData.blocks phi.val
  intro v
  rw [literalAt]
  have hi : simpleModuleClassBlock namedBlocks C = i := phi.property
  have acts := simpleModuleClassBlock_smul namedBlocks C v
  rw [hi] at acts
  exact acts

variable (W : CharacterWeight 2 K X)
  (supported : O.rawWeightBlock W = b)
  (reduction : CanonicalRawReduction root W)
  (compatibility :
    NavarroLocalReductionInflationBlockCompatibility.normalizerBrauerBlock
        O W.subgroup reduction.normalizerRoot reduction.localBrauer =
      O.inflateToNormalizer W.subgroup
        (O.localCharacterBlock W.subgroup W.localCharacter W.defectZero))

include literalAt supported compatibility in
/-- The local-to-global block equation is derived from the supported raw
weight and its selected specified normalizer reduction. -/
theorem localBlockInduces :
    letI := O.ambientBlockData.fintypeBlock
    letI := (O.inflatedNormalizerBlockData W.subgroup).fintypeBlock
    BlockInducesTo (Subgroup.normalizer (W.subgroup : Set X))
      (O.inflatedNormalizerBlockData W.subgroup).catalogue O.ambientBlockData.catalogue
      (irreducibleBrauerCharacterBlock reduction.normalizerRoot
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding reduction.normalizerRoot)
        (O.inflatedNormalizerBlockData W.subgroup).blocks reduction.localBrauer)
      (irreducibleBrauerCharacterBlock root hinj O.ambientBlockData.blocks phi.val) := by
  letI := O.ambientBlockData.fintypeBlock
  letI := (O.inflatedNormalizerBlockData W.subgroup).fintypeBlock
  rw [ambientCharacterBlock O root hinj namedBlocks i b literalAt phi]
  change BlockInducesTo (Subgroup.normalizer (W.subgroup : Set X))
    (O.inflatedNormalizerBlockData W.subgroup).catalogue O.ambientBlockData.catalogue
    (NavarroLocalReductionInflationBlockCompatibility.normalizerBrauerBlock
      O W.subgroup reduction.normalizerRoot reduction.localBrauer) b
  rw [compatibility]
  have assigned : O.induceToAmbient W = b := supported
  rw [← assigned]
  exact inducedBlock_spec (Subgroup.normalizer (W.subgroup : Set X))
    (O.inflatedNormalizerBlockData W.subgroup).catalogue O.ambientBlockData.catalogue _
    (O.blockInductionDefined W)

include literalAt supported compatibility in
/-- All specified data at the sole intermediate subgroup of the identity
ambient, using the same global character and local reduction. -/
def intermediateAtTop
    (fieldSource : SpathCoefficientField 2 k Nat.prime_two) :
    IntermediateBlockData 2 k K (Subgroup.normalizer (W.subgroup : Set X))
      phi.val.val reduction.localBrauer.val (⊤ : Subgroup X) := by
  letI := O.ambientBlockData.fintypeBlock
  letI := (O.inflatedNormalizerBlockData W.subgroup).fintypeBlock
  exact topBlockData (Subgroup.normalizer (W.subgroup : Set X))
    root reduction.normalizerRoot hinj
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding reduction.normalizerRoot)
    O.ambientBlockData.blocks (O.inflatedNormalizerBlockData W.subgroup).blocks
    O.ambientBlockData.catalogue (O.inflatedNormalizerBlockData W.subgroup).catalogue
    phi.val reduction.localBrauer fieldSource
    (localBlockInduces O root hinj namedBlocks i b literalAt phi W supported reduction compatibility)

end ModularRep.PaperProofs.TypeBQ3FaithfulCriterionLocalBlocks


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
