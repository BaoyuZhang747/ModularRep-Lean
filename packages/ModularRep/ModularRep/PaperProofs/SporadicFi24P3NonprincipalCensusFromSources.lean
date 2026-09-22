import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic
import ModularRep.PaperProofs.ComputationTranscriptAdditionalBindings
import ModularRep.PaperProofs.SporadicFi24KnownFibreBridgeActual
import ModularRep.PaperProofs.SporadicFi24P3LiteralSpanBindingConstruction
import ModularRep.PaperProofs.SporadicFi24P3NamedTableLiteralWeightRows
import ModularRep.PaperProofs.SporadicTranscriptConsequences

/-!
# The `Fi'_{24}` nonprincipal census from independent prime-three sources

This file replaces the two literal signatures in
`Fi24NonprincipalCensusSource` by a narrower source boundary.

On the Brauer side, the six-row restriction span is first identified with the
literal nonprincipal Brauer span by `BrauerRestrictionSpaceBinding`.  The only
new computation alignment then says that the row-span dimension is the `l`
entry in the second `P3` row of `fi24blocks.out`, and that the range rank of
`id + T` is GAP's intermediate `plusRank`.  Lean constructs the Brauer basis,
proves that its permutation trace counts literal fixed Brauer characters, and
derives that trace from the two ranks and involutivity.

On the weight side, `fi24p3.out` is tied to the four typed table-row labels.
The existing local-table construction gives four distinct literal weights in
the named nonprincipal block.  Exact coverage of that fibre remains a separate
external source fact; from it Lean constructs, rather than assumes, an
equivalence between the four row labels and the literal weight fibre.  Lean
also transports the literal outer action back to the row labels.  The sole
An--Dietrich action input identifies the fixed-point count of this transported
action with the `fixed` coordinate of the corrected Table 8 entry `2/2`.

Thus no Brauer--weight equivalence, nonprincipal signature, principal-block
statement, defect-zero statement, or cancellation conclusion is an input.
The remaining external bindings are deliberately visible: the restriction
span/computation alignment, literal four-row coverage, and identification of
the corrected Table 8 entry with the transported literal row action.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3NonprincipalCensusFromSources

open Formalisation.BlockCancellation
open ModularRep.PaperProofs.ComputationTranscriptAdditionalBindings
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24KnownFibreBridgeActual
open ModularRep.PaperProofs.SporadicFi24P3LiteralSpanBindingConstruction
open ModularRep.PaperProofs.SporadicFi24P3NamedTableCentralCharacterAdapter
open ModularRep.PaperProofs.SporadicFi24P3NamedTableLiteralWeightRows
open ModularRep.PaperProofs.SporadicFi24P3QSquaredLocalTableSource
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual
open ModularRep.PaperProofs.SporadicTranscriptConsequences
open ModularRep.PaperProofs.SporadicProposition57ComputationRelative

universe u

variable {k K X BlockIndex : Type u}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X] [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}

noncomputable local instance centerFintype :
    Fintype (Subgroup.center X) :=
  Fintype.ofFinite _

variable (iota : PrimeRegularRootEmbedding 3 k K X)
variable (hinj :
  FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable [Invertible (Fintype.card (Subgroup.center X) : k)]
variable {R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := X)}
variable (E1 : RoutineTransportInput iota hinj blocks R)

/-! ## Literal transcript rows -/

/-- The second printed `P3` row, retained as parser output rather than copied
as the already interpreted signature `(4,2)`. -/
def fi24P3NonprincipalBrauerTranscriptRow : Nat × Nat × Nat :=
  fi24ThreePrintedRowsFromTranscript.getD 1 (0, 0, 0)

theorem fi24P3NonprincipalBrauerTranscriptRow_exact :
    fi24P3NonprincipalBrauerTranscriptRow = (4, 2, 1) := by
  simp [fi24P3NonprincipalBrauerTranscriptRow, fi24ThreePrintedRows_exact]

/-- The unprinted intermediate `plusRank` in `fi24blocks.g` for the second
`P3` row.  The program computes this rank before forming
`fixed := 2 * plusRank - n`; unlike the three transcript coordinates, this
value is an E3 computation-source datum rather than parser output. -/
def fi24P3NonprincipalBrauerPlusRank : Nat := 3

/-- The internal `plusRank` and the printed row obey the exact arithmetic used
by `fi24blocks.g`. -/
theorem fi24P3NonprincipalBrauerPlusRank_recovers_printedFixed :
    2 * fi24P3NonprincipalBrauerPlusRank -
        fi24P3NonprincipalBrauerTranscriptRow.1 =
      fi24P3NonprincipalBrauerTranscriptRow.2.1 := by
  simp [fi24P3NonprincipalBrauerPlusRank,
    fi24P3NonprincipalBrauerTranscriptRow_exact]

/-- The third prime-three entry of the corrected An--Dietrich Table 8.  Its
coordinates mean `(fixed, nonfixed)`, not `(total, fixed)`. -/
def fi24P3NonprincipalTable8Entry : TableSignatureEntry :=
  fi24Table8AtThree.getD 2 ⟨0, 0⟩

theorem fi24P3NonprincipalTable8Entry_exact :
    fi24P3NonprincipalTable8Entry = ⟨2, 2⟩ := by
  decide

/-- The four typed local rows carry exactly the six numerical coordinates
printed by `fi24p3.out`, in transcript order.  This is a kernel check of
labels; the interpretation of the corresponding typed characters remains in
the external `Source` value. -/
theorem typedLocalRows_are_the_transcript_rows :
    [printedRow .r23, printedRow .r24, printedRow .r51, printedRow .r52] =
      fi24ThreeLocalTableCertificateFromTranscript := by
  rw [fi24ThreeLocalTableCertificate_exact]
  decide

/-! ## A generic trace calculation for a basis permutation -/

omit [CharZero K] in
/-- If a linear operator permutes a finite basis by `sigma`, then its trace is
the cardinality of the fixed-point set of `sigma`. -/
private theorem trace_eq_cast_natCard_fixedPoints_of_basis_action
    {I V : Type u} [Fintype I] [DecidableEq I]
    [AddCommGroup V] [Module K V]
    (b : Module.Basis I K V) (T : V →ₗ[K] V) (σ : Equiv.Perm I)
    (hT : ∀ i, T (b i) = b (σ i)) :
    LinearMap.trace K V T =
      (Nat.card (Function.fixedPoints σ) : K) := by
  have hmatrix :
      LinearMap.toMatrix b b T = (σ.permMatrix K).transpose := by
    ext i j
    rw [LinearMap.toMatrix_apply, hT j]
    simp [Matrix.transpose_apply, Equiv.Perm.permMatrix,
      PEquiv.toMatrix_apply, Finsupp.single_apply, eq_comm]
  rw [LinearMap.trace_eq_matrix_trace K b T, hmatrix,
    Matrix.trace_transpose, Matrix.trace_permutation, Nat.card_coe_set_eq]

/-- For an involutive basis permutation, the trace is recovered from the rank
of `id + T`.  This is the linear-algebra identity used to keep the source field
in the same form as GAP's `RankMat(plusRows)` calculation. -/
private theorem trace_eq_two_mul_finrank_range_id_add_sub_finrank
    {I V : Type u} [Fintype I] [DecidableEq I]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (b : Module.Basis I K V) (T : V →ₗ[K] V) (σ : Equiv.Perm I)
    (hT : ∀ i, T (b i) = b (σ i)) (hσ : Function.Involutive σ) :
    LinearMap.trace K V T =
      (2 : K) *
          (Module.finrank K (LinearMap.range (LinearMap.id + T)) : K) -
        (Module.finrank K V : K) := by
  have hT_sq : T * T = 1 := by
    apply b.ext
    intro i
    change T (T (b i)) = b i
    rw [hT i, hT (σ i), hσ i]
  let A : V →ₗ[K] V := LinearMap.id + T
  let P : V →ₗ[K] V := (2 : K)⁻¹ • A
  have htwo : (2 : K) ≠ 0 := by norm_num
  have hP : IsIdempotentElem P := by
    rw [IsIdempotentElem]
    ext x
    have hT_sq_x := LinearMap.congr_fun hT_sq x
    simp only [Module.End.mul_apply] at hT_sq_x
    simp only [P, A, Module.End.mul_apply, LinearMap.smul_apply,
      LinearMap.add_apply, LinearMap.id_coe, id_eq, map_smul, map_add,
      hT_sq_x]
    module
  have hrange : LinearMap.range P = LinearMap.range A := by
    exact LinearMap.range_smul A (2 : K)⁻¹ (inv_ne_zero htwo)
  have htraceP :
      LinearMap.trace K V P =
        (Module.finrank K (LinearMap.range P) : K) :=
    ((LinearMap.isProj_range_iff_isIdempotentElem P).2 hP).trace
  have htraceExpand :
      LinearMap.trace K V P =
        (2 : K)⁻¹ *
          ((Module.finrank K V : K) + LinearMap.trace K V T) := by
    simp [P, A, LinearMap.trace_id, smul_eq_mul]
    ring
  have heq :
      (Module.finrank K (LinearMap.range A) : K) =
        (2 : K)⁻¹ *
          ((Module.finrank K V : K) + LinearMap.trace K V T) := by
    rw [← hrange, ← htraceP]
    exact htraceExpand
  rw [show LinearMap.id + T = A from rfl]
  calc
    LinearMap.trace K V T =
        (2 : K) *
            ((2 : K)⁻¹ *
              ((Module.finrank K V : K) + LinearMap.trace K V T)) -
          (Module.finrank K V : K) := by
      field_simp
      ring
    _ = (2 : K) * (Module.finrank K (LinearMap.range A) : K) -
          (Module.finrank K V : K) := by rw [← heq]

/-! ## Brauer census from the restriction computation -/

/-- The exact semantic alignment still needed between `fi24blocks` and the
literal restriction space.  The first field identifies the computed row rank;
the second identifies GAP's intermediate `RankMat(plusRows)` with the range
rank of `id + T` for the canonical pullback on that same literal span.  Neither
field mentions a trace, a Brauer fixed-point set, or a Brauer--weight
equivalence. -/
structure Fi24P3NonprincipalBrauerComputationAlignment
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (D : BrauerRestrictionSpaceBinding iota hinj blocks S) : Prop where
  restrictionSpan_finrank :
    Module.finrank K (ordinaryRestrictionSpan iota hinj blocks D) =
      fi24P3NonprincipalBrauerTranscriptRow.1
  plusAction_finrank :
    Module.finrank K
        (LinearMap.range
          (LinearMap.id +
            BrauerRestrictionSpaceBinding.outerAction iota hinj blocks D)) =
      fi24P3NonprincipalBrauerPlusRank

omit [Invertible (Fintype.card (Subgroup.center X) : k)] in
/-- The literal nonprincipal Brauer signature follows from the transcript
alignment.  Finiteness, the basis, and the identification of the linear
permutation with the canonical fibre action are all constructed in Lean. -/
theorem nonprincipalBrauer_signature
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (D : BrauerRestrictionSpaceBinding iota hinj blocks S)
    (A : Fi24P3NonprincipalBrauerComputationAlignment iota hinj blocks S D) :
    (Nat.card (BrauerFibre iota hinj blocks S.nonprincipalBlock),
      Nat.card (Function.fixedPoints
        (nonprincipalBrauerPerm iota hinj blocks E1 S))) = (4, 2) := by
  let V := ordinaryRestrictionSpan iota hinj blocks D
  let b := BrauerRestrictionSpaceBinding.brauerBasis iota hinj blocks D
  let σ := nonprincipalBrauerPerm iota hinj blocks E1 S
  let _ : FiniteDimensional K V :=
    FiniteDimensional.span_of_finite K (Set.finite_range D.rows)
  let _ : Fintype (BrauerFibre iota hinj blocks S.nonprincipalBlock) :=
    FiniteDimensional.fintypeBasisIndex b
  let _ : DecidableEq (BrauerFibre iota hinj blocks S.nonprincipalBlock) :=
    Classical.decEq _
  have hrow := fi24P3NonprincipalBrauerTranscriptRow_exact
  have hfinrank : Module.finrank K V = 4 := by
    exact A.restrictionSpan_finrank.trans (congrArg Prod.fst hrow)
  have hcard :
      Nat.card (BrauerFibre iota hinj blocks S.nonprincipalBlock) = 4 := by
    rw [Nat.card_eq_fintype_card]
    exact (Module.finrank_eq_card_basis b).symm.trans hfinrank
  have htrace :
      LinearMap.trace K V
          (BrauerRestrictionSpaceBinding.outerAction iota hinj blocks D) =
        (Nat.card (Function.fixedPoints σ) : K) :=
    trace_eq_cast_natCard_fixedPoints_of_basis_action
      (K := K) b
      (BrauerRestrictionSpaceBinding.outerAction iota hinj blocks D) σ
      (BrauerRestrictionSpaceBinding.basis_action
        iota hinj blocks E1 D)
  have hσ : Function.Involutive σ :=
    brauerFibrePerm_involutive iota hinj blocks E1 S
      S.nonprincipalBlock S.nonprincipal_fixed
  have htraceRank :
      LinearMap.trace K V
          (BrauerRestrictionSpaceBinding.outerAction iota hinj blocks D) =
        (2 : K) *
            (Module.finrank K
              (LinearMap.range
                (LinearMap.id +
                  BrauerRestrictionSpaceBinding.outerAction
                    iota hinj blocks D)) : K) -
          (Module.finrank K V : K) :=
    trace_eq_two_mul_finrank_range_id_add_sub_finrank
      (K := K) b
      (BrauerRestrictionSpaceBinding.outerAction iota hinj blocks D) σ
      (BrauerRestrictionSpaceBinding.basis_action
        iota hinj blocks E1 D) hσ
  have htraceTwo :
      LinearMap.trace K V
          (BrauerRestrictionSpaceBinding.outerAction iota hinj blocks D) =
        (2 : K) := by
    rw [htraceRank, A.plusAction_finrank,
      fi24P3NonprincipalBrauerPlusRank, hfinrank]
    norm_num
  have hfixedCast :
      (Nat.card (Function.fixedPoints σ) : K) = (2 : K) :=
    htrace.symm.trans htraceTwo
  have hfixed : Nat.card (Function.fixedPoints σ) = 2 := by
    exact_mod_cast hfixedCast
  exact Prod.ext hcard hfixed

/-! ## Weight census from four named rows and corrected Table 8 -/

local instance : Fintype P3QSquaredTableRow :=
  ⟨{.r23, .r24, .r51, .r52}, by
    intro r
    cases r <;> simp⟩

theorem natCard_p3QSquaredTableRow : Nat.card P3QSquaredTableRow = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- One typed local row, regarded as a point of the literal nonprincipal
weight fibre.  Block membership is a theorem from the interval
central character source, not a field of the coverage source below. -/
def tableRowWeightFibre
    (R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := X))
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (Q : Subgroup X)
    (table : Source Q
      (R.1.operations.toLocalNormalizerBlockOperations Q))
    (S414 : PhaseASource R Q table)
    (M : Fi24P3NamedTableIntervalCentralCharacterMatch
      R S.nonprincipalBlock Q table)
    (r : P3QSquaredTableRow) :
    WeightFibre (R := R) S.nonprincipalBlock :=
  ⟨tableRowWeight R Q table r,
    tableRowWeight_block R S.nonprincipalBlock Q table S414 M r⟩

/-- The missing completeness statement for `fi24p3`: every literal weight in
the nonprincipal block is represented by one of the four named rows.  It is
stated as elementwise coverage, not as a cardinality or equivalence. -/
structure Fi24P3NonprincipalWeightCoverage
    (R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := X))
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (Q : Subgroup X)
    (table : Source Q
      (R.1.operations.toLocalNormalizerBlockOperations Q)) : Prop where
  covers :
    ∀ w : WeightFibre (R := R) S.nonprincipalBlock,
      ∃ r : P3QSquaredTableRow, tableRowWeight R Q table r = w.1

/-- Lean constructs the named-row-to-literal-weight equivalence from the
existing injectivity theorem and the external elementwise coverage fact. -/
noncomputable def weightRowEquiv
    (R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := X))
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (Q : Subgroup X)
    (table : Source Q
      (R.1.operations.toLocalNormalizerBlockOperations Q))
    (S414 : PhaseASource R Q table)
    (M : Fi24P3NamedTableIntervalCentralCharacterMatch
      R S.nonprincipalBlock Q table)
    (C : Fi24P3NonprincipalWeightCoverage R S Q table) :
    P3QSquaredTableRow ≃ WeightFibre (R := R) S.nonprincipalBlock :=
  Equiv.ofBijective (tableRowWeightFibre R S Q table S414 M) ⟨by
    intro r s hrs
    apply tableRowWeight_injective R Q table
    simpa only [tableRowWeightFibre] using
      congrArg
        (fun w : WeightFibre (R := R) S.nonprincipalBlock => w.1) hrs, by
    intro w
    obtain ⟨r, hr⟩ := C.covers w
    refine ⟨r, ?_⟩
    apply Subtype.ext
    exact hr⟩

/-- Pull the literal outer permutation back to the four named row labels.
This action is constructed by conjugation; it is not supplied by a source. -/
noncomputable def weightTableRowOuter
    (R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := X))
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (Q : Subgroup X)
    (table : Source Q
      (R.1.operations.toLocalNormalizerBlockOperations Q))
    (S414 : PhaseASource R Q table)
    (M : Fi24P3NamedTableIntervalCentralCharacterMatch
      R S.nonprincipalBlock Q table)
    (C : Fi24P3NonprincipalWeightCoverage R S Q table) :
    Equiv.Perm P3QSquaredTableRow :=
  (weightRowEquiv R S Q table S414 M C).trans
    ((nonprincipalWeightPerm (R := R) S).trans
      (weightRowEquiv R S Q table S414 M C).symm)

omit [Invertible (Fintype.card (Subgroup.center X) : k)] in
theorem weightRowEquiv_intertwines
    (R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := X))
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (Q : Subgroup X)
    (table : Source Q
      (R.1.operations.toLocalNormalizerBlockOperations Q))
    (S414 : PhaseASource R Q table)
    (M : Fi24P3NamedTableIntervalCentralCharacterMatch
      R S.nonprincipalBlock Q table)
    (C : Fi24P3NonprincipalWeightCoverage R S Q table) :
    Intertwines (weightRowEquiv R S Q table S414 M C)
      (weightTableRowOuter R S Q table S414 M C)
      (nonprincipalWeightPerm (R := R) S) := by
  intro r
  simp [weightTableRowOuter]

/-- The sole corrected-table action binding.  It identifies the `fixed`
coordinate of the third prime-three Table 8 entry with the fixed points of the
exact row action transported from the literal weight fibre.  It supplies no
row-to-weight map and no weight-fibre signature. -/
structure Fi24P3NonprincipalTable8ActionAlignment
    (R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := X))
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (Q : Subgroup X)
    (table : Source Q
      (R.1.operations.toLocalNormalizerBlockOperations Q))
    (S414 : PhaseASource R Q table)
    (M : Fi24P3NamedTableIntervalCentralCharacterMatch
      R S.nonprincipalBlock Q table)
    (C : Fi24P3NonprincipalWeightCoverage R S Q table) : Prop where
  fixedPoints_eq_correctedTable8 :
    Nat.card (Function.fixedPoints
      (weightTableRowOuter R S Q table S414 M C)) =
        fi24P3NonprincipalTable8Entry.fixed

omit [Invertible (Fintype.card (Subgroup.center X) : k)] in
/-- The four-row table, coverage, and corrected Table 8 action binding imply
the literal nonprincipal weight signature. -/
theorem nonprincipalWeight_signature
    (R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := X))
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (Q : Subgroup X)
    (table : Source Q
      (R.1.operations.toLocalNormalizerBlockOperations Q))
    (S414 : PhaseASource R Q table)
    (M : Fi24P3NamedTableIntervalCentralCharacterMatch
      R S.nonprincipalBlock Q table)
    (C : Fi24P3NonprincipalWeightCoverage R S Q table)
    (A : Fi24P3NonprincipalTable8ActionAlignment
      R S Q table S414 M C) :
    (Nat.card (WeightFibre (R := R) S.nonprincipalBlock),
      Nat.card (Function.fixedPoints
        (nonprincipalWeightPerm (R := R) S))) = (4, 2) := by
  let e := weightRowEquiv R S Q table S414 M C
  let σ := weightTableRowOuter R S Q table S414 M C
  let τ := nonprincipalWeightPerm (R := R) S
  have hcard : Nat.card (WeightFibre (R := R) S.nonprincipalBlock) = 4 := by
    exact (Nat.card_congr e).symm.trans natCard_p3QSquaredTableRow
  have hfixedCongr :
      Nat.card (Function.fixedPoints σ) =
        Nat.card (Function.fixedPoints τ) :=
    Nat.card_congr
      (fixedPointsEquivOfIntertwines e σ τ
        (weightRowEquiv_intertwines R S Q table S414 M C))
  have hentry := fi24P3NonprincipalTable8Entry_exact
  have hfixed : Nat.card (Function.fixedPoints τ) = 2 := by
    calc
      Nat.card (Function.fixedPoints τ) =
          Nat.card (Function.fixedPoints σ) := hfixedCongr.symm
      _ = fi24P3NonprincipalTable8Entry.fixed :=
        A.fixedPoints_eq_correctedTable8
      _ = 2 := congrArg TableSignatureEntry.fixed hentry
  exact Prod.ext hcard hfixed

/-! ## The existing census interface -/

omit [Invertible (Fintype.card (Subgroup.center X) : k)] in
/-- Combine the old source interface from the independent computation,
coverage, and corrected-table inputs.  The resulting record is a conclusion;
it is never used to construct any of its own premises. -/
theorem fi24NonprincipalCensusSourceOfIndependentSources
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (D : BrauerRestrictionSpaceBinding iota hinj blocks S)
    (BA : Fi24P3NonprincipalBrauerComputationAlignment iota hinj blocks S D)
    (Q : Subgroup X)
    (table : Source Q
      (R.1.operations.toLocalNormalizerBlockOperations Q))
    (S414 : PhaseASource R Q table)
    (M : Fi24P3NamedTableIntervalCentralCharacterMatch
      R S.nonprincipalBlock Q table)
    (C : Fi24P3NonprincipalWeightCoverage R S Q table)
    (WA : Fi24P3NonprincipalTable8ActionAlignment
      R S Q table S414 M C) :
    Fi24NonprincipalCensusSource iota hinj blocks E1 S where
  brauer_signature :=
    nonprincipalBrauer_signature iota hinj blocks E1 S D BA
  weight_signature :=
    nonprincipalWeight_signature R S Q table S414 M C WA

end ModularRep.PaperProofs.SporadicFi24P3NonprincipalCensusFromSources


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
