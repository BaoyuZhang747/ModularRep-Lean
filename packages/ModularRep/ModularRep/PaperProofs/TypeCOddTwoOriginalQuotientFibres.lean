import ModularRep.PaperProofs.TypeCOddTwoOriginalBlockMatching
import ModularRep.PaperProofs.OddTwoGroupEquivBrauerBlocks
import ModularRep.PaperProofs.OddTwoGroupEquivWeightBlocks

/-!
# Complete specified fibres at the original reference quotient

The quotient is the actual central character quotient of an original block
reference. Its root and complete specified primitives are transported by the
canonical quotient equivalence. The only external dictionary is the existing
individual ambient/OWN-normalizer primitive dictionary for the actual
quotient operations. K derives both complete fibres, their reverse maps and
the equivariance of the SAME original matching's quotient graph.

No BlockWitness, reverse-fibre source, selected-pair equation or unrelated
root agreement is an input. The chosen local packet remains the accepted
OriginalBlockMatching packet, hence retains P.localReduction exactly. The
original chosen ambient/extensions and both Q=1 clauses are not changed.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeCOddTwoOriginalQuotientFibres

open ModularRep CharacterWeight FDRepSimpleClassKZero
open CyclicOuterLemma37ActualBlockFibres CyclicOuterLemma37Concrete
open EvenFieldFLZSourceConditions EvenFieldFLZBAWGoodFamily
open OddTwoLiteralSpathTarget OddTwoSelectedWeightAutomorphismCoordinates
open OddTwoGroupEquivWeightBlocks TypeCOddTwoOriginalBlockMatching

universe u

variable {n : ℕ} {F : Type u} [Field F] [Finite F]
variable (P : Problem n F) (b : P.Block)
variable (reference : Definition35Brauer (P.blockProblem b))

local instance originalQuotientFintype :
    Fintype (CentralCharacterQuotient (P.blockProblem b) reference) :=
  Fintype.ofFinite _

/-- One fixed root on the actual reference quotient. -/
def quotientRoot : PrimeRegularRootEmbedding 2 P.k P.K
    (CentralCharacterQuotient (P.blockProblem b) reference) :=
  P.iota.alongMulEquiv (referenceQuotientEquiv b reference)

theorem quotientInjective :
    IrreducibleBrauerCharacterInjectivity (quotientRoot P b reference) :=
  irreducibleBrauerCharacterInjectivity_of_rootEmbedding _

/-- These are the actual images of the original complete primitives. -/
def quotientIdempotent (c : P.Block) :
    P.k[CentralCharacterQuotient (P.blockProblem b) reference] :=
  MonoidAlgebra.domCongr P.k P.k (referenceQuotientEquiv b reference)
    (P.blockSource.operations.ambientBlockData.blockIdempotent c)

theorem quotientIdempotent_physical (c : P.Block) :
    quotientIdempotent P b reference c =
      MonoidAlgebra.domCongr P.k P.k (referenceQuotientEquiv b reference) c.1 :=
  congrArg (MonoidAlgebra.domCongr P.k P.k (referenceQuotientEquiv b reference))
    (P.catalogue_idempotent c)

/-- Completeness and primitivity are transported, not assumed anew. -/
def quotientBlocks :
    letI := P.blockSource.operations.ambientBlockData.fintypeBlock
    BlockIdempotentDecomposition (quotientIdempotent P b reference) := by
  letI := P.blockSource.operations.ambientBlockData.fintypeBlock
  exact P.blockSource.operations.ambientBlockData.blocks.alongMulEquiv
    (referenceQuotientEquiv b reference)

/-- This equality is only for the explicitly computed root. -/
theorem quotientRoot_lift (z : P.k) :
    (quotientRoot P b reference).lift z = P.iota.lift z :=
  P.iota.alongMulEquiv_lift (referenceQuotientEquiv b reference) z

/-- The actual whole-character transport on the single fixed quotient. -/
def descendedBrauer (psi : IBr P.iota) : IBr (quotientRoot P b reference) :=
  IrreducibleBrauerCharacter.equivAlongMulEquiv P.iota
    (referenceQuotientEquiv b reference) psi

theorem descendedBrauer_values (psi : IBr P.iota)
    (x : PrimeRegularElement (G := CentralCharacterQuotient
      (P.blockProblem b) reference) 2) :
    (descendedBrauer P b reference psi).1 x =
      psi.1 (PrimeRegularElement.map
        (referenceQuotientEquiv b reference).symm.toMonoidHom x) := rfl

/-- Literal inflation through the original canonical quotient projection. -/
theorem descendedBrauer_inflation (psi : IBr P.iota) :
    PrimeRegularClassFunction.pullback
      (centralCharacterQuotientMap (P.blockProblem b) reference)
      (descendedBrauer P b reference psi).1 = psi.1 := by
  apply PrimeRegularClassFunction.ext
  intro x
  change psi.1 (PrimeRegularElement.map
    (referenceQuotientEquiv b reference).symm.toMonoidHom
    (PrimeRegularElement.map (referenceQuotientEquiv b reference).toMonoidHom x)) = _
  apply congrArg psi.1
  apply Subtype.ext
  exact (referenceQuotientEquiv b reference).symm_apply_apply x.1

variable (OH : LocalBlockInductionOperations
  (p := 2) (k := P.k) (K := P.K)
  (G := CentralCharacterQuotient (P.blockProblem b) reference) (Block := P.Block))
variable (dictionary : PrimitiveDictionary P.blockSource.operations OH
  (referenceQuotientEquiv b reference))

include dictionary in
/-- The actual operation catalogue is the computed specified catalogue. -/
theorem quotientOperation_idempotent (c : P.Block) :
    OH.ambientBlockData.blockIdempotent c = quotientIdempotent P b reference c :=
  (dictionary.ambient_primitive c).symm

def quotientBrauerBlock (phi : IBr (quotientRoot P b reference)) : P.Block :=
  letI := OH.ambientBlockData.fintypeBlock
  irreducibleBrauerCharacterBlock (quotientRoot P b reference)
    (quotientInjective P b reference) OH.ambientBlockData.blocks phi

include dictionary in
/-- Different stored finite indexing proofs add no new specified block. -/
theorem quotientBrauerBlock_eq_computed (phi : IBr (quotientRoot P b reference)) :
    letI := P.blockSource.operations.ambientBlockData.fintypeBlock
    quotientBrauerBlock P b reference OH phi =
      irreducibleBrauerCharacterBlock (quotientRoot P b reference)
        (quotientInjective P b reference) (quotientBlocks P b reference) phi := by
  letI := P.blockSource.operations.ambientBlockData.fintypeBlock
  exact OddTwoGroupEquivBrauerBlocks.block_eq_of_ambient_idempotent
    (quotientRoot P b reference) (quotientInjective P b reference)
    OH.ambientBlockData (quotientBlocks P b reference)
    (quotientOperation_idempotent P b reference OH dictionary) phi

include dictionary in
theorem quotientBrauerBlock_map (psi : IBr P.iota) :
    quotientBrauerBlock P b reference OH (descendedBrauer P b reference psi) =
      P.brauerBlock psi := by
  letI := P.blockSource.operations.ambientBlockData.fintypeBlock
  exact OddTwoGroupEquivBrauerBlocks.block_alongMulEquiv P.iota P.injective
    (referenceQuotientEquiv b reference) (quotientInjective P b reference)
    P.blockSource.operations.ambientBlockData.blocks OH.ambientBlockData
    (quotientOperation_idempotent P b reference OH dictionary) psi

/-- Actual quotient operations, with their source laws derived by transport. -/
def quotientSource :
    letI := transportedBlockAction (G := X n F) (Block := P.Block) (referenceQuotientEquiv b reference)
    LocalBlockInductionSource (p := 2) (k := P.k) (K := P.K)
      (G := CentralCharacterQuotient (P.blockProblem b) reference) (Block := P.Block) :=
  transportedSource (G := X n F) OH (referenceQuotientEquiv b reference) P.blockSource dictionary

abbrev QuotientBrauerFibre :=
  {phi : IBr (quotientRoot P b reference) // quotientBrauerBlock P b reference OH phi = b}

abbrev QuotientWeightFibre :=
  letI := transportedBlockAction (G := X n F) (Block := P.Block) (referenceQuotientEquiv b reference)
  (quotientSource P b reference OH dictionary).Fibre b

/-- Both Brauer fibre directions restrict the actual character equivalence. -/
def brauerEquiv : Definition35Brauer (P.blockProblem b) ≃
    QuotientBrauerFibre P b reference OH := by
  letI := P.blockSource.operations.ambientBlockData.fintypeBlock
  exact OddTwoGroupEquivBrauerBlocks.brauerFibreEquiv P.iota P.injective
    (referenceQuotientEquiv b reference) (quotientInjective P b reference)
    P.blockSource.operations.ambientBlockData.blocks OH.ambientBlockData
    (quotientOperation_idempotent P b reference OH dictionary) b

@[simp] theorem brauerEquiv_val (psi : Definition35Brauer (P.blockProblem b)) :
    (brauerEquiv P b reference OH dictionary psi).1 =
      descendedBrauer P b reference psi.1 := rfl

include dictionary in
theorem brauer_reverse (phi : QuotientBrauerFibre P b reference OH) :
    ∃ psi : Definition35Brauer (P.blockProblem b),
      descendedBrauer P b reference psi.1 = phi.1 :=
  ⟨(brauerEquiv P b reference OH dictionary).symm phi,
    congrArg Subtype.val ((brauerEquiv P b reference OH dictionary).apply_symm_apply phi)⟩

/-- The target fibre uses the actual OH operations, not a free weight map. -/
def weightEquiv : Definition35Weight (P.blockProblem b) ≃
    QuotientWeightFibre P b reference OH dictionary := by
  letI := transportedBlockAction (G := X n F) (Block := P.Block) (referenceQuotientEquiv b reference)
  exact fibreEquiv (G := X n F) OH (referenceQuotientEquiv b reference) P.blockSource dictionary b

@[simp] theorem weightEquiv_val (w : Definition35Weight (P.blockProblem b)) :
    (weightEquiv P b reference OH dictionary w).1 =
      conjugacyClassGroupEquiv (referenceQuotientEquiv b reference) w.1 := rfl

variable (D : Definition41 P)

/-- Compose the SAME original block map with the actual quotient fibre map. -/
def originalEquivQuotientWeight : Definition35Brauer (P.blockProblem b) ≃
    QuotientWeightFibre P b reference OH dictionary :=
  (blockEquiv D b).trans (weightEquiv P b reference OH dictionary)

/-- Its raw image is the accepted packet retaining P.localReduction. -/
theorem originalEquivQuotientWeight_val (psi : Definition35Brauer (P.blockProblem b)) :
    (originalEquivQuotientWeight P b reference OH dictionary D psi).1 =
      weightClass (quotientPair D b reference psi) :=
  (quotientPair_class D b reference psi).symm

theorem quotientPair_liesInBlock (psi : Definition35Brauer (P.blockProblem b)) :
    letI := transportedBlockAction (G := X n F) (Block := P.Block) (referenceQuotientEquiv b reference)
    (quotientSource P b reference OH dictionary).weightBlock
      (weightClass (quotientPair D b reference psi)) = b := by
  letI := transportedBlockAction (G := X n F) (Block := P.Block) (referenceQuotientEquiv b reference)
  exact (congrArg (quotientSource P b reference OH dictionary).weightBlock
    (originalEquivQuotientWeight_val P b reference OH dictionary D psi).symm).trans
      (originalEquivQuotientWeight P b reference OH dictionary D psi).2

/-- Reverse weight fibre derived from actual equivalence surjectivity. -/
theorem weight_reverse (w : QuotientWeightFibre P b reference OH dictionary) :
    ∃ psi : Definition35Brauer (P.blockProblem b),
      weightClass (quotientPair D b reference psi) = w.1 := by
  let psi := (originalEquivQuotientWeight P b reference OH dictionary D).symm w
  refine ⟨psi, ?_⟩
  exact (originalEquivQuotientWeight_val P b reference OH dictionary D psi).symm.trans
    (congrArg Subtype.val
      ((originalEquivQuotientWeight P b reference OH dictionary D).apply_symm_apply w))

/-- Complete quotient matching on the SAME specified block and fixed root. -/
def quotientMatching : QuotientBrauerFibre P b reference OH ≃
    QuotientWeightFibre P b reference OH dictionary :=
  (brauerEquiv P b reference OH dictionary).symm.trans
    (originalEquivQuotientWeight P b reference OH dictionary D)

theorem quotientMatching_original (psi : Definition35Brauer (P.blockProblem b)) :
    quotientMatching P b reference OH dictionary D
        (brauerEquiv P b reference OH dictionary psi) =
      originalEquivQuotientWeight P b reference OH dictionary D psi :=
  congrArg (originalEquivQuotientWeight P b reference OH dictionary D)
    ((brauerEquiv P b reference OH dictionary).symm_apply_apply psi)

/-- Quotient graph equivariance is inherited from the actual original map.
No invariant representative or extra equivariance source is assumed. -/
theorem quotient_graph_equivariant
    (alpha : (MulAut (CentralCharacterQuotient (P.blockProblem b) reference))ᵐᵒᵖ)
    (psi chi : Definition35Brauer (P.blockProblem b))
    (h : descendedBrauer P b reference chi.1 =
      alpha • descendedBrauer P b reference psi.1) :
    weightClass (quotientPair D b reference chi) =
      alpha • weightClass (quotientPair D b reference psi) := by
  let a : (MulAut (X n F))ᵐᵒᵖ :=
    MulOpposite.op (MulAut.congr (referenceQuotientEquiv b reference).symm alpha.unop)
  have ha : MulOpposite.op (MulAut.congr (referenceQuotientEquiv b reference) a.unop) =
      alpha := by
    change MulOpposite.op (MulAut.congr (referenceQuotientEquiv b reference)
      (MulAut.congr (referenceQuotientEquiv b reference).symm alpha.unop)) = alpha
    exact (congrArg MulOpposite.op
      (congr_symm_congr (referenceQuotientEquiv b reference) alpha.unop)).trans
        (MulOpposite.op_unop alpha)
  have action := (IrreducibleBrauerCharacter.equivAlongMulEquiv_op_smul
    (G := X n F) P.iota (referenceQuotientEquiv b reference) psi.1 a).trans
      (congrArg (fun c : (MulAut (CentralCharacterQuotient
        (P.blockProblem b) reference))ᵐᵒᵖ =>
          c • descendedBrauer P b reference psi.1) ha)
  have own : (chi.1 : IBr P.iota) =
      @HSMul.hSMul (MulAut (X n F))ᵐᵒᵖ (IBr P.iota) (IBr P.iota)
        inferInstance a psi.1 :=
    (IrreducibleBrauerCharacter.equivAlongMulEquiv P.iota
      (referenceQuotientEquiv b reference)).injective (h.trans action.symm)
  have weights := (conjugacyClassGroupEquiv_op_smul
    (G := X n F) (referenceQuotientEquiv b reference) a (D.map.equiv psi.1)).trans
      (congrArg (fun c : (MulAut (CentralCharacterQuotient
        (P.blockProblem b) reference))ᵐᵒᵖ =>
          c • conjugacyClassGroupEquiv (referenceQuotientEquiv b reference)
            (D.map.equiv psi.1)) ha)
  exact (quotientPair_class D b reference chi).trans
    ((congrArg (conjugacyClassGroupEquiv (referenceQuotientEquiv b reference))
      ((congrArg D.map.equiv own).trans (D.map.equivariant a psi.1))).trans
        (weights.trans
          (congrArg (fun w => alpha • w) (quotientPair_class D b reference psi).symm)))

include dictionary in
/-- Every quotient character has the canonical transported block action. -/
theorem quotientBrauerBlock_transport :
    letI := transportedBlockAction (G := X n F) (Block := P.Block) (referenceQuotientEquiv b reference)
    ∀ (alpha : (MulAut (CentralCharacterQuotient (P.blockProblem b) reference))ᵐᵒᵖ)
      (phi : IBr (quotientRoot P b reference)),
      quotientBrauerBlock P b reference OH (alpha • phi) =
        alpha • quotientBrauerBlock P b reference OH phi := by
  letI := transportedBlockAction (G := X n F) (Block := P.Block) (referenceQuotientEquiv b reference)
  intro alpha phi
  obtain ⟨psi, rfl⟩ := (IrreducibleBrauerCharacter.equivAlongMulEquiv P.iota
    (referenceQuotientEquiv b reference)).surjective phi
  let a : (MulAut (X n F))ᵐᵒᵖ :=
    MulOpposite.op (MulAut.congr (referenceQuotientEquiv b reference).symm alpha.unop)
  have ha : MulOpposite.op (MulAut.congr (referenceQuotientEquiv b reference) a.unop) =
      alpha := by
    change MulOpposite.op (MulAut.congr (referenceQuotientEquiv b reference)
      (MulAut.congr (referenceQuotientEquiv b reference).symm alpha.unop)) = alpha
    exact (congrArg MulOpposite.op
      (congr_symm_congr (referenceQuotientEquiv b reference) alpha.unop)).trans
        (MulOpposite.op_unop alpha)
  have action := (IrreducibleBrauerCharacter.equivAlongMulEquiv_op_smul
    (G := X n F) P.iota (referenceQuotientEquiv b reference) psi a).trans
      (congrArg (fun c : (MulAut (CentralCharacterQuotient
        (P.blockProblem b) reference))ᵐᵒᵖ =>
          c • descendedBrauer P b reference psi) ha)
  change quotientBrauerBlock P b reference OH
      (alpha • descendedBrauer P b reference psi) =
    alpha • quotientBrauerBlock P b reference OH (descendedBrauer P b reference psi)
  calc
    quotientBrauerBlock P b reference OH (alpha • descendedBrauer P b reference psi) =
        quotientBrauerBlock P b reference OH (descendedBrauer P b reference (a • psi)) :=
      (congrArg (quotientBrauerBlock P b reference OH) action).symm
    _ = P.brauerBlock (a • psi) :=
      quotientBrauerBlock_map P b reference OH dictionary _
    _ = a • P.brauerBlock psi := P.support_transport a psi
    _ = alpha • quotientBrauerBlock P b reference OH (descendedBrauer P b reference psi) := by
      change alpha • P.brauerBlock psi =
        alpha • quotientBrauerBlock P b reference OH (descendedBrauer P b reference psi)
      exact congrArg (fun c : P.Block => alpha • c)
        (quotientBrauerBlock_map P b reference OH dictionary psi).symm

end ModularRep.PaperProofs.TypeCOddTwoOriginalQuotientFibres


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
