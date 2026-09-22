import ModularRep.PaperProofs.TypeBQ3B45DefectZeroMatching
import ModularRep.PaperProofs.TypeBQ3FaithfulLocalReduction

/-!
Construct the fixed-block defect-zero matching source from the SAME calibrated
modular system and specified local selectors. Navarro 3.18 is instantiated only
on the local quotients of the selected atOne row and raw weights assigned the
selected block. The normalizer selector guard is restricted to those same rows
and to root-compatible inflated reductions. Canonical reductions, normalizer
root agreement and the selector equalities used by matching are deductions.

The block's unique supported Brauer character comes from the separate actual
central-descent construction. The selected ordinary defect-zero reduction and
ordinary regular-restriction uniqueness, specified selected ambient idempotent,
and the standard weight-support consequence Q=1 remain subordinate inputs.
There is no matching, extension, final block-induction equality or criterion
premise. This helper has no standalone manuscript-window acceptance credit.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBQ3B45PhysicalInputs

open ModularRep CharacterWeight
open TypeBQ3TripleCoverCarrier TypeBRankThreePrincipalCountBinding
open TypeBCentralKernelBlockSource
open TypeBLocalReductionInstantiation TypeBFixedRootDefinitionFamily
open TypeBQ3FaithfulLocalReduction TypeBQ3B45DefectZeroMatching
open SporadicCompleteCollapseLemma52Actual (GlobalDefectZeroCharacter)
open SporadicCompleteCollapseLemma52ConcreteLocal (IsBrauerReduction)
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction

variable {k K O : Type} [Field k] [Field K] [CommRing O] [IsDomain O]
  [Algebra O K] [CharP k 2] [IsAlgClosed k] [CharZero K]

local instance groupFintype (Y : Type) [Group Y] [Finite Y] : Fintype Y :=
  Fintype.ofFinite Y

/-- The seed row is included before its induced block has been proved. -/
def Eligible (matrixSource : MatrixExceptionalSource)
    (R : OmegaWeightSource (k := k) (K := K) (ZMod 3))
    (b : LiteralPrimitiveBlock k G3)
    (d : GlobalDefectZeroCharacter (p := 2) (K := K) (X := G3))
    (W : CharacterWeight 2 K G3) : Prop :=
  W = (trivialSource matrixSource).rawAtOne d ∨ R.operations.rawWeightBlock W = b

variable (Msys : ModularSystem 2 K O k)
  (root : PrimeRegularRootEmbedding 2 k K G3)
  (calibration : RootResidueCompatible Msys root)
  [HasEnoughRootsOfUnity K (Nat.card G3)]
  (matrixSource : MatrixExceptionalSource)
  (R : OmegaWeightSource (k := k) (K := K) (ZMod 3))
  (b : LiteralPrimitiveBlock k G3)
  (d : GlobalDefectZeroCharacter (p := 2) (K := K) (X := G3))

/-- The specified source is scoped to the selected row and this one block.
Its root guard is the existing standard guard with an additional row guard. -/
structure ScopedInputs : Prop where
  navarro : ∀ (W : CharacterWeight 2 K G3), Eligible matrixSource R b d W →
    letI := localOrdinaryRoots (K := K) W.subgroup
    ScopedDefectZeroReductionSource Msys (localQuotientRoot root W.subgroup)
      (localRoot_residueCanonical Msys root calibration W.subgroup)
  normalizer_block_of_reduction : ∀ (W : CharacterWeight 2 K G3),
    Eligible matrixSource R b d W →
    ∀ (rootN : PrimeRegularRootEmbedding 2 k K
        (Subgroup.normalizer (W.subgroup : Set G3))) (phiN : IBr rootN),
      NormalizerRootAgreement root W.subgroup rootN →
      NormalizerInflatedReduction W.subgroup W.localCharacter rootN phiN →
      NavarroLocalReductionInflationBlockCompatibility.normalizerBrauerBlock
          R.operations W.subgroup rootN phiN =
        R.operations.inflateToNormalizer W.subgroup
          (R.operations.localCharacterBlock W.subgroup W.localCharacter W.defectZero)

variable {Msys root calibration matrixSource R b d}
  (physical : ScopedInputs Msys root calibration matrixSource R b d)

/-- The actual canonical raw reduction is chosen by the scoped Navarro fact. -/
def rowReduction (W : CharacterWeight 2 K G3) (hW : Eligible matrixSource R b d W) :
    CanonicalRawReduction root W :=
  of_scoped Msys root calibration W (physical.navarro W hW)

/-- Root agreement is proved, so the specified guard determines this selector. -/
theorem rowSelector (W : CharacterWeight 2 K G3) (hW : Eligible matrixSource R b d W) :
    NavarroLocalReductionInflationBlockCompatibility.normalizerBrauerBlock
      R.operations W.subgroup (rowReduction physical W hW).normalizerRoot
        (rowReduction physical W hW).localBrauer =
      R.operations.inflateToNormalizer W.subgroup
        (R.operations.localCharacterBlock W.subgroup W.localCharacter W.defectZero) := by
  apply physical.normalizer_block_of_reduction W hW
    (rowReduction physical W hW).normalizerRoot (rowReduction physical W hW).localBrauer
  · exact normalizerRootAt_agrees root W
  · exact (rowReduction physical W hW).localBrauer_reduction

/-- Every canonical source field of the fixed-block matching is discharged
by the calibrated row source; its supported singleton is supplied by descent. -/
def fixedBlockSource (phi : IBr root)
    (reduction : IsBrauerReduction root d.val phi)
    (regular_unique : ∀ d' : GlobalDefectZeroCharacter (p := 2) (K := K) (X := G3),
      (∀ g : PrimeRegularElement (G := G3) 2, d'.val g.val = d.val g.val) → d' = d)
    (support : Supported root b phi)
    (unique : ∀ psi : IBr root, Supported root b psi → psi = phi)
    (ambientAt : R.operations.ambientBlockData.blockIdempotent b = b.val)
    (rawTrivial : ∀ W : CharacterWeight 2 K G3,
      R.operations.rawWeightBlock W = b → W.subgroup = ⊥) :
    FixedBlockSource root R matrixSource b phi where
  d := d
  reduction := reduction
  regular_unique := regular_unique
  support := support
  unique := unique
  ambientAt := ambientAt
  atOneReduction := rowReduction physical ((trivialSource matrixSource).rawAtOne d)
    (Or.inl rfl)
  atOneSelector := rowSelector physical ((trivialSource matrixSource).rawAtOne d)
    (Or.inl rfl)
  rawTrivial := rawTrivial
  rawReduction := fun W hW => rowReduction physical W (Or.inr hW)
  rawSelector := fun W hW => rowSelector physical W (Or.inr hW)

/-- The construction retains the selected ordinary character literally. -/
@[simp] theorem fixedBlockSource_d (phi : IBr root)
    (reduction : IsBrauerReduction root d.val phi)
    (regular_unique : ∀ d' : GlobalDefectZeroCharacter (p := 2) (K := K) (X := G3),
      (∀ g : PrimeRegularElement (G := G3) 2, d'.val g.val = d.val g.val) → d' = d)
    (support : Supported root b phi)
    (unique : ∀ psi : IBr root, Supported root b psi → psi = phi)
    (ambientAt : R.operations.ambientBlockData.blockIdempotent b = b.val)
    (rawTrivial : ∀ W : CharacterWeight 2 K G3,
      R.operations.rawWeightBlock W = b → W.subgroup = ⊥) :
    (fixedBlockSource physical phi reduction regular_unique support unique ambientAt rawTrivial).d =
      d := rfl

end ModularRep.PaperProofs.TypeBQ3B45PhysicalInputs


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
