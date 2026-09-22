import ManuscriptIBAW.TypeB.OddTensorBound
import ModularRep.PaperProofs.TypeBOddPrimeConlonDecomposition
import ModularRep.PaperProofs.TypeBOddPrimeConlonWindow

/-!
# Lemma 4.2 on the special Clifford group

The specified rational series and integral representations determine the
decomposition lattice. The tensor stabiliser bound supplies the central
character proof of hypoelementarity. Conlon's theorem and Burnside mark
injectivity then give the block bijection. The Spin theorem uses the
specified action of Aut(Spin) on blocks modulo inner automorphisms.
-/

noncomputable section
open scoped MonoidAlgebra
namespace ManuscriptIBAW.TypeB.OddConlon
open ModularRep ModularRep.PaperProofs
open BlockFibreRestriction DecompositionBasicSetBridge
open FDRepSimpleClassKZero IntegralBasicSetBridge ConlonBasicSet
open TypeBCliffordCarriers TypeBCliffordCentreSource
open TypeBRationalSeriesBasicSet TypeBIntegralSeriesSplitting
open TypeBSpecialCliffordActionAdapter TypeBSpecialCliffordActionSplitting
open TypeBFLZLabelSource TypeBFLZLabelSplittingSource
open TypeBOddPrimeConlonDecomposition OddTensorBound

variable {p ell f n : ℕ} {F K O k : Type}
  [Field F] [Finite F] [CharP F p] [NeZero f] [Finite (Clifford n F)]
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharZero K] [CharP k ell] [IsAlgClosed k]
  {N : NormSource n F} {parameters : OddFieldParameters F p f}
  (fs : FieldActionSource n F p f parameters N)
  (D : OrdinaryReductionEquiv (k := k) (K := K) (SpinSubgroup n F N)
    fs.action (field_spinSubgroup_map n F fs))
  [Fintype (SourceIndex F p ell n)]
  [Fintype (LiteralPrimitiveBlock k (SpecialClifford n F))]
  (Msys : ModularSystem ell K O k)
  (iota : PrimeRegularRootEmbedding ell k K (SpecialClifford n F))
  (hinj : IrreducibleBrauerCharacterInjectivity iota)
  (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
  {unipotent : UnipotentPredicate F K p n}
  [MulAction (TypeBConformalDualCarriers.CSp F n)
    (FullCharacterPair F K p n unipotent)]
  (S : TypeBFLZLabelSplittingSource.Equation34Source (ell := ell) unipotent)
  (blocks : BlockIdempotentDecomposition
    (fun b : LiteralPrimitiveBlock k (SpecialClifford n F) => b.val))
  (ordinary : TypeBOrdinaryBlockSplitting.OrdinaryBlockSource
    Msys iota hinj blocks (ordinaryRoots := S.ordinary_roots))
  (union : TypeBSpecialCliffordBroueMichelSource.BlockUnionCertificate
    Msys iota hinj S blocks ordinary)
  (literal23 : TypeBFLZLiteralIntegralSeries.LiteralTheorem23Certificate
    Msys iota hinj S blocks ordinary hcompat)
  (productFormula : BrauerLinearTensorProductFormula iota)
  (hseries : TypeCConformalActionAdapter.OrdinarySeriesStable
    (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D
    S.rationalSeriesSource.selectedSeries)
  (liftCompatible : OrdinaryLiftReductionCompatible (SpinSubgroup n F N)
    fs.action (field_spinSubgroup_map n F fs) D iota)

variable [Finite S.rationalSeriesSource.Basic]
  [Finite (TensorCharacters (k := k) (SpinSubgroup n F N))]
  (centre : CentreSource n F parameters (Nat.le_trans (by decide : 1 ≤ 3) S.hypotheses.rank))

/-- The restricted decomposition map and its equation on generators follow from
the integral series argument. -/
def decompositionWitness (b : LiteralPrimitiveBlock k (SpecialClifford n F)) :=
  specialClifford_decomposition_lattice fs D Msys iota hinj hcompat S blocks ordinary
    union literal23 productFormula hseries liftCompatible b

include centre union literal23 in
/-- Lemma 4.2 from the central character bound and the same decomposition
lattice. No assumption on scalar translates of Jordan labels is needed. -/
theorem block_bijection (b : LiteralPrimitiveBlock k (SpecialClifford n F)) :
    let _ : HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F)) := S.ordinary_roots
    let _ := TypeBConlonPhysicalActionInstantiation.actualBlockAction (k := k)
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
    let _ := ordinarySeriesCarrierAction (SpinSubgroup n F N) fs.action
      (field_spinSubgroup_map n F fs) D S.rationalSeriesSource.selectedSeries hseries
    let _ := brauerCharacterAction (SpinSubgroup n F N) fs.action
      (field_spinSubgroup_map n F fs) iota productFormula
    let hBr := TypeBPhysicalBlockAction.brauerBlockEquivariant
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
      iota productFormula hinj blocks
    let hOrd := TypeBPhysicalDecompositionAction.ordinaryBlock_equivariant_of_brauer
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
      D Msys iota hcompat hinj productFormula liftCompatible blocks ordinary hBr
    let J := MulAction.stabilizer (ActingGroup (k := k) (SpinSubgroup n F N)
      fs.action (field_spinSubgroup_map n F fs)) b
    let blockOf := ordinarySeriesBlockMap S.rationalSeriesSource.selectedSeries
      (ordinary.physical (ordinaryRoots := S.ordinary_roots)).ordinaryBlock
    let _ : MulAction J (BlockFibre blockOf b) :=
      TypeBSpecialCliffordActionSplitting.ordinaryBlockFibreAction
        (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D
        S.rationalSeriesSource.selectedSeries
        (ordinary.physical (ordinaryRoots := S.ordinary_roots)).ordinaryBlock b hseries hOrd
    let _ : MulAction J (BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b) :=
      brauerBlockFibreAction (SpinSubgroup n F N) fs.action
        (field_spinSubgroup_map n F fs) iota productFormula
        (irreducibleBrauerCharacterBlock iota hinj blocks) b hBr
    ∀ (conlon : PadicConlonMarkDetection.{0, 0} (p := 2) (A := J))
      (burnside : PublishedBurnsideMarkInjectivity.{0, 0} (A := J)),
    IsPHypoelementary 2 J ∧
      ∃ e : BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b ≃
          BlockFibre blockOf b, IsEquivariantSetEquiv (A := J) e := by
  classical
  dsimp only
  letI : HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F)) := S.ordinary_roots
  letI := TypeBConlonPhysicalActionInstantiation.actualBlockAction (k := k)
    (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
  letI := ordinarySeriesCarrierAction (SpinSubgroup n F N) fs.action
    (field_spinSubgroup_map n F fs) D S.rationalSeriesSource.selectedSeries hseries
  letI := brauerCharacterAction (SpinSubgroup n F N) fs.action
    (field_spinSubgroup_map n F fs) iota productFormula
  let hBr := TypeBPhysicalBlockAction.brauerBlockEquivariant
    (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
    iota productFormula hinj blocks
  let hOrd := TypeBPhysicalDecompositionAction.ordinaryBlock_equivariant_of_brauer
    (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
    D Msys iota hcompat hinj productFormula liftCompatible blocks ordinary hBr
  let J := MulAction.stabilizer (ActingGroup (k := k) (SpinSubgroup n F N)
    fs.action (field_spinSubgroup_map n F fs)) b
  let blockOf := ordinarySeriesBlockMap S.rationalSeriesSource.selectedSeries
    (ordinary.physical (ordinaryRoots := S.ordinary_roots)).ordinaryBlock
  letI : MulAction J (BlockFibre blockOf b) :=
    TypeBSpecialCliffordActionSplitting.ordinaryBlockFibreAction
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D
      S.rationalSeriesSource.selectedSeries
      (ordinary.physical (ordinaryRoots := S.ordinary_roots)).ordinaryBlock b hseries hOrd
  letI : MulAction J (BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b) :=
    brauerBlockFibreAction (SpinSubgroup n F N) fs.action
      (field_spinSubgroup_map n F fs) iota productFormula
      (irreducibleBrauerCharacterBlock iota hinj blocks) b hBr
  intro conlon burnside
  have hstructure := OddTensorBound.stabilizer_structure parameters
    (Nat.le_trans (by decide : 1 ≤ 3) S.hypotheses.rank) N centre fs
    Msys iota hinj blocks S.ordinary_roots ordinary b
  have hypo := TypeCExactStabilizerLemma310Relative.exactStabilizer_isTwoHypoelementary
    (LinearCharactersTrivialOn.fieldAction (k := k) fs.action
      (TypeCConformalActionAdapter.FieldInvariantSubgroup.isFieldStable
        (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs))) J hstructure.1
  obtain ⟨d, _, _, _⟩ := decompositionWitness fs D Msys iota hinj hcompat S blocks ordinary
    union literal23 productFormula hseries liftCompatible b
  obtain ⟨e, he⟩ := (lemma_2_5_basicSetBridge d.toLinearEquiv
    d.toIntertwiningMap.isIntertwining' conlon burnside).2 hypo
  exact ⟨hypo, e.symm, isEquivariantSetEquiv_symm e he⟩

end ManuscriptIBAW.TypeB.OddConlon

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
