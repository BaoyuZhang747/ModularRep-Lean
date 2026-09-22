import ModularRep.PaperProofs.OddTwoGroupEquivOwnReduction
import ModularRep.PaperProofs.OddTwoGroupEquivWeightBlocks
import ModularRep.PaperProofs.TypeBCentralKernelTripleRootFamily
import ModularRep.PaperProofs.TypeBCentralKernelSpinWeightFibreIdentification

/-!
# Transport of the specified guard through the actual normalizer maps

An arbitrary supplied own-normalizer reduction is pulled back to the
original group. The original guard identifies its supporting primitive.
Character transport and the prescribed backward operation equation give
the target guard. No existence of a new reduction is required.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBGroupEquivPhysicalGuard

open ModularRep CharacterWeight
open TypeBFixedRootDefinitionFamily
open OddTwoActualStabilizerTriple OddTwoDefinition35OwnReduction
open TypeBCentralKernelSpinFibreIdentification

variable {p : ℕ} {k K G H B C : Type}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
  [Group G] [Fintype G] [Group H] [Fintype H]

/-- The target guard follows from the original guard and the exact
backward primitive formula of the transported operations. -/
theorem guardedBlockCompatibility
    (OG : LocalBlockInductionOperations
      (p := p) (k := k) (K := K) (G := G) (Block := B))
    (OH : LocalBlockInductionOperations
      (p := p) (k := k) (K := K) (G := H) (Block := C))
    (e : G ≃* H)
    (rootG : PrimeRegularRootEmbedding p k K G)
    (rootH : PrimeRegularRootEmbedding p k K H)
    (lifts : rootH.lift = rootG.lift)
    (guardG : GuardedBlockCompatibility rootG OG)
    (backward : ∀ V : CharacterWeight p K H,
      primitiveBlockEquiv (ModularRep.normalizerEquiv e.symm V.subgroup)
          (OddTwoGroupEquivWeightBlocks.ownNormalizerBlock OH V) =
        OddTwoGroupEquivWeightBlocks.ownNormalizerBlock OG
          (V.mapGroupEquiv e.symm)) :
    GuardedBlockCompatibility rootH OH := by
  constructor
  intro V rootN phiN agree reduction
  let n : Subgroup.normalizer (V.subgroup : Set H) ≃*
      Subgroup.normalizer ((V.mapGroupEquiv e.symm).subgroup : Set G) :=
    ModularRep.normalizerEquiv e.symm V.subgroup
  let R : OwnNormalizerReduction (k := k) V :=
    { root := rootN, brauer := phiN, own_reduction := reduction }
  let rootN' := OddTwoGroupEquivOwnReduction.mappedNormalizerRoot V e.symm R
  let phiN' := OddTwoGroupEquivOwnReduction.mappedNormalizerBrauer V e.symm R
  have agree' : NormalizerRootAgreement rootG
      (V.mapGroupEquiv e.symm).subgroup rootN' := by
    intro zeta
    have h := TypeBCentralKernelTripleRootFamily.alongMulEquiv_agrees
      rootH rootN n agree zeta
    exact h.trans (congrFun lifts _)
  have original := guardG.normalizer_block_of_reduction
    (V.mapGroupEquiv e.symm) rootN' phiN' agree'
    (OddTwoGroupEquivOwnReduction.mappedNormalizerBrauer_ownReduction V e.symm R)
  letI : Fintype (InflatedNormalizerBlock (k := k) V.subgroup) :=
    (OH.inflatedNormalizerBlockData V.subgroup).fintypeBlock
  letI : Fintype (InflatedNormalizerBlock (k := k)
      (V.mapGroupEquiv e.symm).subgroup) :=
    (OG.inflatedNormalizerBlockData (V.mapGroupEquiv e.symm).subgroup).fintypeBlock
  change TypeBCentralKernelBrauerBlocks.block rootN'
      (OG.inflatedNormalizerBlockData (V.mapGroupEquiv e.symm).subgroup).blocks
      phiN' = OddTwoGroupEquivWeightBlocks.ownNormalizerBlock OG
        (V.mapGroupEquiv e.symm) at original
  change TypeBCentralKernelBrauerBlocks.block rootN
      (OH.inflatedNormalizerBlockData V.subgroup).blocks phiN =
    OddTwoGroupEquivWeightBlocks.ownNormalizerBlock OH V
  apply (primitiveBlockEquiv n).injective
  have physical := TypeBCentralKernelSpinWeightFibreIdentification.selectedBlock_along
    n rootN rootN'
    (OH.inflatedNormalizerBlockData V.subgroup).blocks
    (OG.inflatedNormalizerBlockData (V.mapGroupEquiv e.symm).subgroup).blocks
    phiN phiN' (funext (rootN.alongMulEquiv_lift n)) rfl
  exact physical.trans (original.trans (backward V).symm)

end ModularRep.PaperProofs.TypeBGroupEquivPhysicalGuard




/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
