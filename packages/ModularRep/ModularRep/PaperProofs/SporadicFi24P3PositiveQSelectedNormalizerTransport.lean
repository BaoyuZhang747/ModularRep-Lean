import ModularRep.BrauerLocalExtensionInnerTransport
import ModularRep.LocalNormalizerBlockNaturality
import ModularRep.PaperProofs.SporadicFi24P3PositiveQBaseInductionTransport

/-!
# Moving a positive-radical table block to the selected normaliser

The named `Fi'_{24}` table is stated at one literal radical `Q`, whereas the
representative hidden by `selectedCharacterWeight` need only have a conjugate
radical.  The conjugator retained by
`NamedTableRowSelectedWeightAlignment` gives the required equivalence of
normalisers and a commuting square with the ambient inner automorphism.

The first transport theorem below keeps the transported table catalogue on
the selected normaliser.  To compare it with the independently supplied
all-radicals operations, we use the generic source law that taking the local
character block and then inflating it commutes with canonical automorphism
transport.  Equality of weight isomorphism classes supplies the transported
ordinary character, so the selected idempotent equality, central character
equality, and block-induction relation are all theorems.

The only table/fusion input is the existing one-field
`Fi24P3NamedTableIntervalCentralCharacterMatch`.  No literal equality of raw
weight representatives and no second `BlockInducesTo` premise is introduced.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3PositiveQSelectedNormalizerTransport

open ModularRep
open ModularRep.CharacterWeight
open ModularRep.InnerNormalizerTransport
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24P3NamedTableCentralCharacterAdapter
open ModularRep.PaperProofs.SporadicFi24P3NamedTableLiteralWeightRows
open ModularRep.PaperProofs.SporadicFi24P3PositiveQBaseInductionTransport
open ModularRep.PaperProofs.SporadicFi24P3QSquaredLocalTableSource

universe u

noncomputable local instance subgroupFintype
    {G : Type u} [Group G] [Finite G] (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

variable {k K X : Type u}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

variable
  {R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := X)}
  {B : ActualBlock (k := k) (X := X)}
  {w : LiteralWeightFibre R.1 B}
  {Q : Subgroup X}
  {table : SporadicFi24P3QSquaredLocalTableSource.Source Q
    (R.1.operations.toLocalNormalizerBlockOperations Q)}
  {r : P3QSquaredTableRow}

/-- The normaliser equivalence determined by the retained table-row
conjugator.  Its target is the radical of the exact selected representative,
not a reselected representative. -/
def selectedNormalizerEquiv
    (alignment : NamedTableRowSelectedWeightAlignment R B w Q table r) :
    defectNormalizer Q ≃*
      defectNormalizer (selectedCharacterWeight R.1 B w).subgroup :=
  normalizerEquivOfConjEq Q
    (selectedCharacterWeight R.1 B w).subgroup alignment.conjugator
    alignment.selectedRadical_eq_conjugate.symm

@[simp]
theorem selectedNormalizerEquiv_coe
    (alignment : NamedTableRowSelectedWeightAlignment R B w Q table r)
    (n : defectNormalizer Q) :
    (selectedNormalizerEquiv alignment n : X) =
      alignment.conjugator * (n : X) * alignment.conjugator⁻¹ :=
  rfl

/-- Conjugation on the ambient group and the induced equivalence of the two
normalisers form the square needed by block-induction transport. -/
theorem selectedNormalizerEquiv_square
    (alignment : NamedTableRowSelectedWeightAlignment R B w Q table r) :
    (MulAut.conj alignment.conjugator).toMonoidHom.comp
        (defectNormalizer Q).subtype =
      (defectNormalizer
          (selectedCharacterWeight R.1 B w).subgroup).subtype.comp
        (selectedNormalizerEquiv alignment).toMonoidHom := by
  ext n
  rfl

/-- Inner conjugation fixes the central character indexed by a literal
ambient block.  The proof uses literal-idempotent coherence of the carrier;
it is not an extra source field. -/
theorem literalAmbientCentralCharacter_conj
    (R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := X))
    (B : ActualBlock (k := k) (X := X)) (a : X) :
    let O := R.1.operations
    letI : Fintype (ActualBlock (k := k) (X := X)) :=
      O.ambientBlockData.fintypeBlock
    centralCharacterAlongMulEquiv (MulAut.conj a)
        (O.ambientBlockData.catalogue.centralCharacter B) =
      O.ambientBlockData.catalogue.centralCharacter B := by
  let O := R.1.operations
  letI : Fintype (ActualBlock (k := k) (X := X)) :=
    O.ambientBlockData.fintypeBlock
  apply centralCharacterAlongMulEquiv_eq_of_blockIdempotent
    (MulAut.conj a) O.ambientBlockData.catalogue
      O.ambientBlockData.catalogue
  apply Subtype.ext
  change MonoidAlgebra.domCongr k k (MulAut.conj a)
      (O.ambientBlockData.blockIdempotent B) =
    O.ambientBlockData.blockIdempotent B
  rw [R.2 B]
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro x
  rw [MonoidAlgebra.coeff_domCongr]
  have hinv : (MulAut.conj a).symm = MulAut.conj a⁻¹ :=
    (map_inv (MulAut.conj : X →* MulAut X) a).symm
  rw [hinv]
  exact LiteralPrimitiveBlock.central_coeff_conjugate
    B.2.central a⁻¹ x

/-- The fixed-`Q` named-table induction relation transported to the actual
radical of the selected representative.

The local catalogue in the conclusion is exactly the table catalogue
transported along `selectedNormalizerEquiv`.  Thus no comparison with the
independently indexed selected-radical catalogue is hidden here. -/
theorem tableBlock_inducesTo_selectedRadical_transported
    (alignment : NamedTableRowSelectedWeightAlignment R B w Q table r)
    (S414 : PhaseASource R Q table)
    (tableFusion : Fi24P3NamedTableIntervalCentralCharacterMatch
      R B Q table) :
    let W := selectedCharacterWeight R.1 B w
    let O := R.1.operations
    let sourceLocalData := O.inflatedNormalizerBlockData Q
    let eN := selectedNormalizerEquiv alignment
    letI : Fintype (ActualBlock (k := k) (X := X)) :=
      O.ambientBlockData.fintypeBlock
    letI : Fintype (InflatedNormalizerBlock (k := k) Q) :=
      sourceLocalData.fintypeBlock
    BlockInducesTo (defectNormalizer W.subgroup)
      (sourceLocalData.catalogue.alongMulEquiv eN)
      O.ambientBlockData.catalogue table.normalizerBlock B := by
  let W := selectedCharacterWeight R.1 B w
  let O := R.1.operations
  let sourceLocalData := O.inflatedNormalizerBlockData Q
  let eN := selectedNormalizerEquiv alignment
  letI : Fintype (ActualBlock (k := k) (X := X)) :=
    O.ambientBlockData.fintypeBlock
  letI : Fintype (InflatedNormalizerBlock (k := k) Q) :=
    sourceLocalData.fintypeBlock
  exact blockInducesTo_alongMulEquiv
    (defectNormalizer Q) (defectNormalizer W.subgroup)
    (MulAut.conj alignment.conjugator) eN
    (selectedNormalizerEquiv_square alignment)
    sourceLocalData.catalogue O.ambientBlockData.catalogue
    (sourceLocalData.catalogue.alongMulEquiv eN)
    O.ambientBlockData.catalogue
    (b := table.normalizerBlock) (B := B)
    (b' := table.normalizerBlock) (B' := B)
    rfl (literalAmbientCentralCharacter_conj R B alignment.conjugator)
    (tableNormalizerBlock_inducesTo_target
      R B Q table S414 tableFusion)

/-- The local block attached by the operations to the exact selected raw
weight. -/
abbrev selectedAttachedNormalizerBlock
    (alignment : NamedTableRowSelectedWeightAlignment R B w Q table r) :
    InflatedNormalizerBlock (k := k)
      (selectedCharacterWeight R.1 B w).subgroup :=
  let W := selectedCharacterWeight R.1 B w
  let O := R.1.operations
  O.inflateToNormalizer W.subgroup
    (O.localCharacterBlock W.subgroup W.localCharacter W.defectZero)

/-! ## Naturality closes the selected-idempotent comparison -/

/-- The representative selected from the global weight class is the canonical
right twist of the named table representative.  This retains both the
transported radical and the transported local ordinary character. -/
theorem selectedCharacterWeight_eq_namedTableRow_rightTwist
    (alignment : NamedTableRowSelectedWeightAlignment R B w Q table r) :
    selectedCharacterWeight R.1 B w =
      (namedTableRowRepresentative R Q table r).rightTwist
        (MulAut.conj alignment.conjugator⁻¹) := by
  apply CharacterWeight.eq_of_isomorphic
  have hquot := alignment.selectedIsoClass_eq
  change
    Quotient.mk'' (selectedCharacterWeight R.1 B w) =
      Quotient.mk''
        ((namedTableRowRepresentative R Q table r).rightTwist
          (MulAut.conj alignment.conjugator⁻¹)) at hquot
  exact Quotient.exact hquot

/-- Naturality of the two local block operations implies the formerly
external selected-idempotent match.

The source law is uniform in every subgroup, defect-zero character, and
automorphism.  This theorem is its specialisation to the retained conjugator
and named table row; no second block-induction relation is used. -/
theorem selectedAttachedIdempotent_eq_of_naturality
    (alignment : NamedTableRowSelectedWeightAlignment R B w Q table r)
    (naturality : LocalNormalizerBlockOperations.RightTwistNaturality
      (fun S : Subgroup X ↦
        R.1.operations.toLocalNormalizerBlockOperations S)) :
    MonoidAlgebra.domCongr k k (selectedNormalizerEquiv alignment)
        (inflatedNormalizerBlockIdempotent
          (k := k) Q table.normalizerBlock) =
      inflatedNormalizerBlockIdempotent
        (k := k) (selectedCharacterWeight R.1 B w).subgroup
        (selectedAttachedNormalizerBlock alignment) := by
  let O := R.1.operations
  let selectedW := selectedCharacterWeight R.1 B w
  let rowW := namedTableRowRepresentative R Q table r
  let alpha := MulAut.conj alignment.conjugator⁻¹
  have hW : selectedW = rowW.rightTwist alpha :=
    selectedCharacterWeight_eq_namedTableRow_rightTwist alignment
  have hquot :
      (Quotient.mk'' selectedW :
          CharacterWeight.IsoClass (p := 3) (K := K) (G := X)) =
        Quotient.mk'' (rowW.rightTwist alpha) :=
    congrArg Quotient.mk'' hW
  have hiso : CharacterWeight.Isomorphic selectedW
      (rowW.rightTwist alpha) := Quotient.exact hquot
  have hQ : selectedW.subgroup = Q.comap alpha.toMonoidHom := by
    simpa [rowW, namedTableRowRepresentative, tableRadical,
      CharacterWeight.characterWeightAt] using hiso.choose
  let transportedChi := OrdinaryIrreducibleCharacter.mapEquiv
    (table.ordinary r) (rightNormalizerQuotientEquiv alpha Q).symm
  have hchiForward :
      CharacterWeight.castLocalCharacter hQ selectedW.localCharacter =
        transportedChi := by
    have hspec := hiso.choose_spec
    change
      CharacterWeight.castLocalCharacter _ selectedW.localCharacter =
        transportedChi at hspec
    convert hspec using 1
  have hchiBack :
      CharacterWeight.castLocalCharacter hQ.symm transportedChi =
        selectedW.localCharacter := by
    calc
      CharacterWeight.castLocalCharacter hQ.symm transportedChi =
          CharacterWeight.castLocalCharacter hQ.symm
            (CharacterWeight.castLocalCharacter hQ
              selectedW.localCharacter) := by rw [hchiForward]
      _ = selectedW.localCharacter :=
        CharacterWeight.castLocalCharacter_symm hQ selectedW.localCharacter
  have htable :
      (O.toLocalNormalizerBlockOperations Q).attachedNormalizerBlock
          (table.ordinary r) (table.ordinary_defectZero r) =
        table.normalizerBlock := by
    change O.inflateToNormalizer Q
        (O.localCharacterBlock Q (table.ordinary r)
          (table.ordinary_defectZero r)) = table.normalizerBlock
    calc
      O.inflateToNormalizer Q
          (O.localCharacterBlock Q (table.ordinary r)
            (table.ordinary_defectZero r)) =
          O.inflateToNormalizer Q (table.quotientBlock r) := by
        apply congrArg (O.inflateToNormalizer Q)
        simpa [O,
          CharacterWeight.LocalBlockInductionOperations.toLocalNormalizerBlockOperations] using
          table.quotientBlock_of_ordinary r
      _ = table.normalizerBlock := by
        simpa [O,
          CharacterWeight.LocalBlockInductionOperations.toLocalNormalizerBlockOperations] using
          table.inflated_quotientBlock r
  have hnatural :=
    naturality.attachedNormalizerBlock_rightTwist Q
      (table.ordinary r) (table.ordinary_defectZero r) alpha
  let castNormalizer :
      defectNormalizer (Q.comap alpha.toMonoidHom) ≃*
        defectNormalizer selectedW.subgroup :=
    MulEquiv.cast
      (M := fun S : Subgroup X ↦ defectNormalizer S) hQ.symm
  have hcast :
      inflatedNormalizerBlockAlongMulEquiv castNormalizer
          ((O.toLocalNormalizerBlockOperations
            (Q.comap alpha.toMonoidHom)).attachedNormalizerBlock
              transportedChi
              ((table.ordinary_defectZero r).mapEquiv
                (rightNormalizerQuotientEquiv alpha Q).symm)) =
        (O.toLocalNormalizerBlockOperations selectedW.subgroup).attachedNormalizerBlock
          selectedW.localCharacter
            selectedW.defectZero := by
    exact
      LocalNormalizerBlockOperations.attachedNormalizerBlock_along_subgroup_eq
        (operations := fun S : Subgroup X ↦
          O.toLocalNormalizerBlockOperations S)
        hQ.symm transportedChi selectedW.localCharacter hchiBack
        ((table.ordinary_defectZero r).mapEquiv
          (rightNormalizerQuotientEquiv alpha Q).symm)
        selectedW.defectZero
  let rightNormalizer := (rightNormalizerEquiv alpha Q).symm
  have hcomposite :
      inflatedNormalizerBlockAlongMulEquiv
          (rightNormalizer.trans castNormalizer)
          ((O.toLocalNormalizerBlockOperations Q).attachedNormalizerBlock
            (table.ordinary r) (table.ordinary_defectZero r)) =
        (O.toLocalNormalizerBlockOperations selectedW.subgroup).attachedNormalizerBlock
          selectedW.localCharacter
            selectedW.defectZero := by
    calc
      inflatedNormalizerBlockAlongMulEquiv
          (rightNormalizer.trans castNormalizer)
          ((O.toLocalNormalizerBlockOperations Q).attachedNormalizerBlock
            (table.ordinary r) (table.ordinary_defectZero r)) =
          inflatedNormalizerBlockAlongMulEquiv castNormalizer
            (inflatedNormalizerBlockAlongMulEquiv rightNormalizer
              ((O.toLocalNormalizerBlockOperations Q).attachedNormalizerBlock
                (table.ordinary r) (table.ordinary_defectZero r))) :=
        (inflatedNormalizerBlockAlongMulEquiv_trans rightNormalizer
          castNormalizer _).symm
      _ = inflatedNormalizerBlockAlongMulEquiv castNormalizer
          ((O.toLocalNormalizerBlockOperations
            (Q.comap alpha.toMonoidHom)).attachedNormalizerBlock
              transportedChi
              ((table.ordinary_defectZero r).mapEquiv
                (rightNormalizerQuotientEquiv alpha Q).symm)) := by
        exact congrArg
          (inflatedNormalizerBlockAlongMulEquiv castNormalizer) hnatural
      _ = (O.toLocalNormalizerBlockOperations selectedW.subgroup).attachedNormalizerBlock
          selectedW.localCharacter
            selectedW.defectZero := hcast
  have he : rightNormalizer.trans castNormalizer =
      selectedNormalizerEquiv alignment := by
    ext n
    calc
      ((rightNormalizer.trans castNormalizer n :
          defectNormalizer selectedW.subgroup) : X) =
          ((rightNormalizer n :
            defectNormalizer (Q.comap alpha.toMonoidHom)) : X) := by
        exact CyclicOuterLemma37Concrete.normalizerCast_coe
          hQ.symm (rightNormalizer n)
      _ = alpha.symm (n : X) := rfl
      _ = alignment.conjugator * (n : X) * alignment.conjugator⁻¹ := by
        simp [alpha, mul_assoc]
      _ = (selectedNormalizerEquiv alignment n : X) :=
        (selectedNormalizerEquiv_coe alignment n).symm
  rw [he, htable] at hcomposite
  exact congrArg Subtype.val hcomposite

/-- The derived idempotent comparison implies the corresponding equality of
the transported table central character and the selected operations central
character. -/
theorem selectedLocalCentralCharacter_eq
    (alignment : NamedTableRowSelectedWeightAlignment R B w Q table r)
    (naturality : LocalNormalizerBlockOperations.RightTwistNaturality
      (fun S : Subgroup X ↦
        R.1.operations.toLocalNormalizerBlockOperations S)) :
    let W := selectedCharacterWeight R.1 B w
    let O := R.1.operations
    let sourceLocalData := O.inflatedNormalizerBlockData Q
    let selectedLocalData := O.inflatedNormalizerBlockData W.subgroup
    let eN := selectedNormalizerEquiv alignment
    letI : Fintype (InflatedNormalizerBlock (k := k) Q) :=
      sourceLocalData.fintypeBlock
    letI : Fintype (InflatedNormalizerBlock (k := k) W.subgroup) :=
      selectedLocalData.fintypeBlock
    centralCharacterAlongMulEquiv eN
        (sourceLocalData.catalogue.centralCharacter table.normalizerBlock) =
      selectedLocalData.catalogue.centralCharacter
        (selectedAttachedNormalizerBlock alignment) := by
  let W := selectedCharacterWeight R.1 B w
  let O := R.1.operations
  let sourceLocalData := O.inflatedNormalizerBlockData Q
  let selectedLocalData := O.inflatedNormalizerBlockData W.subgroup
  let eN := selectedNormalizerEquiv alignment
  letI : Fintype (InflatedNormalizerBlock (k := k) Q) :=
    sourceLocalData.fintypeBlock
  letI : Fintype (InflatedNormalizerBlock (k := k) W.subgroup) :=
    selectedLocalData.fintypeBlock
  apply centralCharacterAlongMulEquiv_eq_of_blockIdempotent
    eN sourceLocalData.catalogue selectedLocalData.catalogue
  apply Subtype.ext
  change MonoidAlgebra.domCongr k k eN
      (inflatedNormalizerBlockIdempotent
        (k := k) Q table.normalizerBlock) =
    inflatedNormalizerBlockIdempotent
      (k := k) W.subgroup (selectedAttachedNormalizerBlock alignment)
  exact selectedAttachedIdempotent_eq_of_naturality alignment naturality

/-- Strong operations-facing form: the block attached to the exact selected
raw weight induces to the same literal ambient block as the named table row.

This is obtained by transporting the fixed-table theorem; it is not a second
block-induction hypothesis. -/
theorem selectedAttachedBlock_inducesTo_of_table
    (alignment : NamedTableRowSelectedWeightAlignment R B w Q table r)
    (S414 : PhaseASource R Q table)
    (tableFusion : Fi24P3NamedTableIntervalCentralCharacterMatch
      R B Q table)
    (naturality : LocalNormalizerBlockOperations.RightTwistNaturality
      (fun S : Subgroup X ↦
        R.1.operations.toLocalNormalizerBlockOperations S)) :
    let W := selectedCharacterWeight R.1 B w
    let O := R.1.operations
    let selectedLocalData := O.inflatedNormalizerBlockData W.subgroup
    letI : Fintype (ActualBlock (k := k) (X := X)) :=
      O.ambientBlockData.fintypeBlock
    letI : Fintype (InflatedNormalizerBlock (k := k) W.subgroup) :=
      selectedLocalData.fintypeBlock
    BlockInducesTo (defectNormalizer W.subgroup)
      selectedLocalData.catalogue O.ambientBlockData.catalogue
      (selectedAttachedNormalizerBlock alignment) B := by
  let W := selectedCharacterWeight R.1 B w
  let O := R.1.operations
  let sourceLocalData := O.inflatedNormalizerBlockData Q
  let selectedLocalData := O.inflatedNormalizerBlockData W.subgroup
  let eN := selectedNormalizerEquiv alignment
  letI : Fintype (ActualBlock (k := k) (X := X)) :=
    O.ambientBlockData.fintypeBlock
  letI : Fintype (InflatedNormalizerBlock (k := k) Q) :=
    sourceLocalData.fintypeBlock
  letI : Fintype (InflatedNormalizerBlock (k := k) W.subgroup) :=
    selectedLocalData.fintypeBlock
  exact blockInducesTo_alongMulEquiv
    (defectNormalizer Q) (defectNormalizer W.subgroup)
    (MulAut.conj alignment.conjugator) eN
    (selectedNormalizerEquiv_square alignment)
    sourceLocalData.catalogue O.ambientBlockData.catalogue
    selectedLocalData.catalogue O.ambientBlockData.catalogue
    (b := table.normalizerBlock) (B := B)
    (b' := selectedAttachedNormalizerBlock alignment) (B' := B)
    (selectedLocalCentralCharacter_eq alignment naturality)
    (literalAmbientCentralCharacter_conj R B alignment.conjugator)
    (tableNormalizerBlock_inducesTo_target
      R B Q table S414 tableFusion)

end ModularRep.PaperProofs.SporadicFi24P3PositiveQSelectedNormalizerTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
