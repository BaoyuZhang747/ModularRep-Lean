import ModularRep.PaperProofs.TypeBCentralKernelPairSplittingBinding
import ModularRep.PaperProofs.TypeBCentralKernelSpinWeightFibreIdentification
import ModularRep.PaperProofs.TypeBLocalPhysicalBlockBinding
import ModularRep.PaperProofs.OddTwoGroupEquivWeightBlocks

/-!
# Own local blocks under the computed group equivalence

Each local character is reduced in the same modular system. The two specified
guards identify its supporting primitive normalizer block, so transport of
the simple character proves the normalizer idempotent equation. The existing
generic provider then supplies block induction, the transported source and
both weight-fibre inverse laws.

The target operations are a fixed specified catalogue. Their guard is derived
from their own ordinary sources and ordinary inflation membership. Their
ambient labels are the actual group algebra images of the original labels.
No normalizer dictionary or weight-block membership is an input.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBCentrelessSelectedWeightBlockTransport

open ModularRep CharacterWeight
open TypeBLocalReductionInstantiation TypeBModularGroupRootBinding
open TypeBFixedRootDefinitionFamily TypeBCentralKernelLocalReduction

section RawCoordinates

variable {p : ℕ} {K G H : Type} [Field K] [CharZero K]
  [Group G] [Finite G] [Group H] [Finite H]

/-- The generic image pair is exactly the existing central-kernel image pair. -/
theorem mapGroupEquiv_eq_rawWeightEquiv (e : G ≃* H)
    (W : CharacterWeight p K G) :
    W.mapGroupEquiv e = TypeBCentralKernelSpinFibreIdentification.rawWeightEquiv e W := by
  apply mapGroupEquiv_eq_of_normalizer_coordinates W e
    (TypeBCentralKernelSpinFibreIdentification.rawWeightEquiv e W) rfl
    (ModularRep.normalizerEquiv e W.subgroup)
  · intro x
    rfl
  · intro x
    exact TypeBCentralKernelSpinFibreIdentification.rawWeightEquiv_localCharacter
      e W x (ModularRep.normalizerEquiv e W.subgroup x) rfl

/-- Both existing quotient maps retain the same actual raw representatives. -/
theorem conjugacyClassGroupEquiv_eq_weightClassEquiv (e : G ≃* H)
    (w : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G)) :
    CharacterWeight.conjugacyClassGroupEquiv e w =
      TypeBCentralKernelSpinFibreIdentification.weightClassEquiv e w := by
  refine Quotient.inductionOn w ?_
  intro x
  refine Quotient.inductionOn x ?_
  intro W
  exact congrArg TypeBCentralKernelInertia.classOf (mapGroupEquiv_eq_rawWeightEquiv e W)

end RawCoordinates

variable {p : ℕ} {K O k : Type}
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharZero K] [CharP k p] [IsAlgClosed k]
  (Msys : ModularSystem p K O k)

section OwnNormalizer

variable {G H B C : Type} [Group G] [Fintype G] [Group H] [Fintype H]

/-- The canonical quotient reduction uses the original calibrated root on
every root of unity needed by this weight's own normalizer. -/
theorem normalizerRoot_agrees
    (root : PrimeRegularRootEmbedding p k K G)
    (calibration : RootResidueCompatible Msys root)
    (W : CharacterWeight p K G) :
    NormalizerRootAgreement root W.subgroup
      (normalizerRoot W (TypeBCentralKernelPairSplittingBinding.quotientRoot Msys W)) := by
  rw [eq_groupRoot_of_residue Msys _ _
    (TypeBCentralKernelPairSplittingBinding.normalizerRoot_residue Msys W),
    eq_groupRoot_of_residue Msys G root calibration]
  exact groupRoot_agrees_of_dvd Msys G
    (Subgroup.normalizer (W.subgroup : Set G))
    (Nat.ordCompl_dvd_ordCompl_of_dvd
      (Subgroup.card_subgroup_dvd_card (Subgroup.normalizer (W.subgroup : Set G))) p)

variable [HasEnoughRootsOfUnity K (Nat.card G)]
  [HasEnoughRootsOfUnity K (Nat.card H)]

/-- The specified own-normalizer identity is a consequence of the two own
scoped reductions and specified guards in one modular system. -/
theorem ownNormalizerBlock_along
    (e : G ≃* H)
    (rootG : PrimeRegularRootEmbedding p k K G)
    (rootH : PrimeRegularRootEmbedding p k K H)
    (calibrationG : RootResidueCompatible Msys rootG)
    (calibrationH : RootResidueCompatible Msys rootH)
    (OG : LocalBlockInductionOperations
      (p := p) (k := k) (K := K) (G := G) (Block := B))
    (OH : LocalBlockInductionOperations
      (p := p) (k := k) (K := K) (G := H) (Block := C))
    (navarro : ∀ (X : Type) [Group X] [Finite X]
      [HasEnoughRootsOfUnity K (Nat.card X)]
      (iota : PrimeRegularRootEmbedding p k K X)
      (calibration : RootResidueCompatible Msys iota),
        ScopedDefectZeroReductionSource Msys iota calibration)
    (guardG : GuardedBlockCompatibility rootG OG)
    (guardH : GuardedBlockCompatibility rootH OH)
    (W : CharacterWeight p K G) :
    MonoidAlgebra.domCongr k k (ModularRep.normalizerEquiv e W.subgroup)
        (OddTwoGroupEquivWeightBlocks.ownNormalizerBlock OG W).val =
      (OddTwoGroupEquivWeightBlocks.ownNormalizerBlock OH (W.mapGroupEquiv e)).val := by
  let V : CharacterWeight p K H := W.mapGroupEquiv e
  let n : Subgroup.normalizer (W.subgroup : Set G) ≃*
      Subgroup.normalizer (V.subgroup : Set H) :=
    ModularRep.normalizerEquiv e W.subgroup
  let qG : PrimeRegularRootEmbedding p k K (NormalizerQuotient W.subgroup) :=
    TypeBCentralKernelPairSplittingBinding.quotientRoot Msys W
  let qH : PrimeRegularRootEmbedding p k K (NormalizerQuotient V.subgroup) :=
    TypeBCentralKernelPairSplittingBinding.quotientRoot Msys V
  let phiG : IBr (normalizerRoot W qG) := inflatedReduction W qG
    (TypeBCentralKernelPairSplittingBinding.quotientReduction Msys W navarro)
  let phiH : IBr (normalizerRoot V qH) := inflatedReduction V qH
    (TypeBCentralKernelPairSplittingBinding.quotientReduction Msys V navarro)
  have reduceG : NormalizerInflatedReduction W.subgroup W.localCharacter
      (normalizerRoot W qG) phiG :=
    inflatedReduction_value W qG _
      (TypeBCentralKernelPairSplittingBinding.quotientReduction_value Msys W navarro)
  have reduceH : NormalizerInflatedReduction V.subgroup V.localCharacter
      (normalizerRoot V qH) phiH :=
    inflatedReduction_value V qH _
      (TypeBCentralKernelPairSplittingBinding.quotientReduction_value Msys V navarro)
  have lifts : (normalizerRoot V qH).lift = (normalizerRoot W qG).lift :=
    TypeBPrincipalRootLiftBinding.lift_eq_of_residue Msys
      (congrArg (fun d : ℕ => ordCompl[p] d) (Nat.card_congr n.symm.toEquiv))
      (normalizerRoot V qH) (normalizerRoot W qG)
      (TypeBCentralKernelPairSplittingBinding.normalizerRoot_residue Msys V)
      (TypeBCentralKernelPairSplittingBinding.normalizerRoot_residue Msys W)
  have values : phiH.val =
      PrimeRegularClassFunction.pullback n.symm.toMonoidHom phiG.val := by
    apply PrimeRegularClassFunction.ext
    intro y
    let x : PrimeRegularElement (G := Subgroup.normalizer (W.subgroup : Set G)) p :=
      PrimeRegularElement.map n.symm.toMonoidHom y
    have image : PrimeRegularElement.map n.toMonoidHom x = y :=
      Subtype.ext (n.apply_symm_apply y.val)
    change phiH.val y = phiG.val x
    calc
      phiH.val y = phiH.val (PrimeRegularElement.map n.toMonoidHom x) :=
        congrArg (fun z => phiH.val z) image.symm
      _ = V.localCharacter (QuotientGroup.mk (n x.val)) :=
        (reduceH (PrimeRegularElement.map n.toMonoidHom x)).symm
      _ = W.localCharacter (QuotientGroup.mk x.val) :=
        mapGroupEquiv_normalizer_values W e x.val
      _ = phiG.val x := reduceG x
  letI : Fintype (InflatedNormalizerBlock (k := k) W.subgroup) :=
    (OG.inflatedNormalizerBlockData W.subgroup).fintypeBlock
  letI : Fintype (InflatedNormalizerBlock (k := k) V.subgroup) :=
    (OH.inflatedNormalizerBlockData V.subgroup).fintypeBlock
  have blockG := guardG.normalizer_block_of_reduction W
    (normalizerRoot W qG) phiG (normalizerRoot_agrees Msys rootG calibrationG W) reduceG
  have blockH := guardH.normalizer_block_of_reduction V
    (normalizerRoot V qH) phiH (normalizerRoot_agrees Msys rootH calibrationH V) reduceH
  change TypeBCentralKernelBrauerBlocks.block (normalizerRoot W qG)
      (OG.inflatedNormalizerBlockData W.subgroup).blocks phiG =
    OddTwoGroupEquivWeightBlocks.ownNormalizerBlock OG W at blockG
  change TypeBCentralKernelBrauerBlocks.block (normalizerRoot V qH)
      (OH.inflatedNormalizerBlockData V.subgroup).blocks phiH =
    OddTwoGroupEquivWeightBlocks.ownNormalizerBlock OH V at blockH
  have physical := TypeBCentralKernelSpinWeightFibreIdentification.selectedBlock_along
    n (normalizerRoot W qG) (normalizerRoot V qH)
    (OG.inflatedNormalizerBlockData W.subgroup).blocks
    (OH.inflatedNormalizerBlockData V.subgroup).blocks phiG phiH lifts values
  rw [blockG, blockH] at physical
  exact congrArg Subtype.val physical

end OwnNormalizer

section TransportedSource

variable {G H : Type} [Group G] [Fintype G] [Group H] [Fintype H]
  [HasEnoughRootsOfUnity K (Nat.card G)]
  [HasEnoughRootsOfUnity K (Nat.card H)]
  (e : G ≃* H)
  (rootG : PrimeRegularRootEmbedding p k K G)
  (rootH : PrimeRegularRootEmbedding p k K H)
  (calibrationG : RootResidueCompatible Msys rootG)
  (calibrationH : RootResidueCompatible Msys rootH)
  (S : LocalBlockInductionSource
    (p := p) (k := k) (K := K) (G := G) (Block := LiteralPrimitiveBlock k G))
  (OH : LocalBlockInductionOperations
    (p := p) (k := k) (K := K) (G := H) (Block := LiteralPrimitiveBlock k G))
  (literalG : ∀ b : LiteralPrimitiveBlock k G,
    S.operations.ambientBlockData.blockIdempotent b = b.val)
  (literalH : ∀ b : LiteralPrimitiveBlock k G, OH.ambientBlockData.blockIdempotent b =
    MonoidAlgebra.domCongr k k e b.val)
  (navarro : ∀ (X : Type) [Group X] [Finite X]
    [HasEnoughRootsOfUnity K (Nat.card X)]
    (iota : PrimeRegularRootEmbedding p k K X)
    (calibration : RootResidueCompatible Msys iota),
      ScopedDefectZeroReductionSource Msys iota calibration)
  (guardG : GuardedBlockCompatibility rootG S.operations)
  (expansion : ∀ (X : Type) [Group X] [Finite X]
    [HasEnoughRootsOfUnity K (Nat.card X)],
      TypeBLocalPhysicalBlockBinding.ScopedDecompositionExpansionSource (H := X) Msys)
  (ordinaryH : ∀ Q : Subgroup H,
    TypeBLocalPhysicalBlockBinding.NormalizerOrdinarySource Msys OH Q)
  (membershipH : TypeBLocalPhysicalBlockBinding.OrdinaryInflationMembership
    Msys OH ordinaryH)

/-- The target guard is derived from the target operations' own ordinary
inflation source before the normalizer dictionary is constructed. -/
def primitiveDictionary : OddTwoGroupEquivWeightBlocks.PrimitiveDictionary
    S.operations OH e := by
  letI : MulAction (MulAut H)ᵐᵒᵖ (LiteralPrimitiveBlock k G) :=
    OddTwoGroupEquivWeightBlocks.transportedBlockAction
      (Block := LiteralPrimitiveBlock k G) e
  refine ⟨?_, ?_⟩
  · intro b
    rw [literalG, literalH]
  · intro W
    exact ownNormalizerBlock_along Msys e rootG rootH calibrationG calibrationH
      S.operations OH navarro guardG
      (TypeBLocalPhysicalBlockBinding.guardedBlockCompatibility Msys OH
        rootH calibrationH expansion ordinaryH membershipH) W

local notation "dictionary" => primitiveDictionary Msys e rootG rootH
  calibrationG calibrationH S OH literalG literalH navarro guardG
  expansion ordinaryH membershipH

/-- The existing generic source constructor derives both target action laws. -/
def transportedSource :
    letI := OddTwoGroupEquivWeightBlocks.transportedBlockAction
      (Block := LiteralPrimitiveBlock k G) e
    LocalBlockInductionSource
      (p := p) (k := k) (K := K) (G := H) (Block := LiteralPrimitiveBlock k G) :=
  OddTwoGroupEquivWeightBlocks.transportedSource OH e S dictionary

local notation "targetSource" => transportedSource Msys e rootG rootH
  calibrationG calibrationH S OH literalG literalH navarro guardG
  expansion ordinaryH membershipH

@[simp] theorem transportedSource_operations :
    letI : MulAction (MulAut H)ᵐᵒᵖ (LiteralPrimitiveBlock k G) :=
      OddTwoGroupEquivWeightBlocks.transportedBlockAction
        (Block := LiteralPrimitiveBlock k G) e
    (targetSource).operations = OH := by
  letI : MulAction (MulAut H)ᵐᵒᵖ (LiteralPrimitiveBlock k G) :=
    OddTwoGroupEquivWeightBlocks.transportedBlockAction
      (Block := LiteralPrimitiveBlock k G) e
  rfl

/-- The specified guard belongs to these exact target operations. -/
theorem transportedSource_guard :
    letI : MulAction (MulAut H)ᵐᵒᵖ (LiteralPrimitiveBlock k G) :=
      OddTwoGroupEquivWeightBlocks.transportedBlockAction
        (Block := LiteralPrimitiveBlock k G) e
    GuardedBlockCompatibility rootH (targetSource).operations := by
  letI : MulAction (MulAut H)ᵐᵒᵖ (LiteralPrimitiveBlock k G) :=
    OddTwoGroupEquivWeightBlocks.transportedBlockAction
      (Block := LiteralPrimitiveBlock k G) e
  exact TypeBLocalPhysicalBlockBinding.guardedBlockCompatibility Msys OH
    rootH calibrationH expansion ordinaryH membershipH

include calibrationG calibrationH literalG literalH navarro guardG
  expansion ordinaryH membershipH in
/-- The selected raw image has the same ambient label by actual block induction. -/
theorem rawWeightBlock_eq (W : CharacterWeight p K G) :
    OH.rawWeightBlock (TypeBCentralKernelSpinFibreIdentification.rawWeightEquiv e W) =
      S.operations.rawWeightBlock W := by
  rw [← mapGroupEquiv_eq_rawWeightEquiv e W]
  exact OddTwoGroupEquivWeightBlocks.rawWeightBlock_eq S.operations OH e dictionary W

/-- The existing full weight fibres are restricted along the actual image map. -/
def weightFibreEquiv (b : LiteralPrimitiveBlock k G) :
    letI : MulAction (MulAut H)ᵐᵒᵖ (LiteralPrimitiveBlock k G) :=
      OddTwoGroupEquivWeightBlocks.transportedBlockAction
        (Block := LiteralPrimitiveBlock k G) e
    S.Fibre b ≃ (targetSource).Fibre b := by
  letI : MulAction (MulAut H)ᵐᵒᵖ (LiteralPrimitiveBlock k G) :=
    OddTwoGroupEquivWeightBlocks.transportedBlockAction
      (Block := LiteralPrimitiveBlock k G) e
  exact OddTwoGroupEquivWeightBlocks.fibreEquiv OH e S dictionary b

@[simp] theorem weightFibreEquiv_val (b : LiteralPrimitiveBlock k G) (w : S.Fibre b) :
    letI : MulAction (MulAut H)ᵐᵒᵖ (LiteralPrimitiveBlock k G) :=
      OddTwoGroupEquivWeightBlocks.transportedBlockAction
        (Block := LiteralPrimitiveBlock k G) e
    (weightFibreEquiv Msys e rootG rootH calibrationG calibrationH
      S OH literalG literalH navarro guardG expansion ordinaryH membershipH b w).val =
      TypeBCentralKernelSpinFibreIdentification.weightClassEquiv e w.val := by
  letI : MulAction (MulAut H)ᵐᵒᵖ (LiteralPrimitiveBlock k G) :=
    OddTwoGroupEquivWeightBlocks.transportedBlockAction
      (Block := LiteralPrimitiveBlock k G) e
  exact conjugacyClassGroupEquiv_eq_weightClassEquiv e w.val

end TransportedSource

end ModularRep.PaperProofs.TypeBCentrelessSelectedWeightBlockTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
