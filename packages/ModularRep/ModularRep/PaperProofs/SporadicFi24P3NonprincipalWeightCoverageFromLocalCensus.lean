import ModularRep.PaperProofs.SporadicFi24P3NonprincipalCensusFromSources

/-!
# The `Fi'_{24}` nonprincipal weight coverage from local sources

The four row coverage used in the prime three nonprincipal census is not
accepted here as a source fact.  It is derived from two narrower bindings.

* The exhaustive defect zero filter in `fi24p3.g` is identified with the
  cardinality of the literal local defect zero character set at the chosen
  radical subgroup.
* The radical classification of An--Cannon--O'Brien--Unger is identified
  with the assertion that every weight in the chosen nonprincipal block has
  radical class represented by that subgroup.

The existing local table source already supplies four distinct literal
defect zero characters.  Lean proves that they exhaust the local set and then
uses the representative fibre equivalence to prove that the corresponding
four weights exhaust the literal nonprincipal weight fibre.  Neither a global
weight cardinality, a fixed point count, a character--weight equivalence, nor
the desired four row coverage is a premise.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3NonprincipalWeightCoverageFromLocalCensus

open ModularRep.CharacterWeight
open ModularRep.PaperProofs.ComputationTranscriptAdditionalBindings
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24P3NamedTableLiteralWeightRows
open ModularRep.PaperProofs.SporadicFi24P3NonprincipalCensusFromSources
open ModularRep.PaperProofs.SporadicFi24P3QSquaredLocalTableSource
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual

universe u

variable {k K X : Type u}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

variable
  (R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := X))

local instance : Fintype P3QSquaredTableRow :=
  ⟨{.r23, .r24, .r51, .r52}, by
    intro r
    cases r <;> simp⟩

/-- The number of rows returned by the exhaustive local defect zero filter in
the checked `fi24p3` transcript. -/
def fi24P3LocalDefectZeroTranscriptCount : Nat :=
  fi24ThreeLocalTableCertificateFromTranscript.length

theorem fi24P3LocalDefectZeroTranscriptCount_exact :
    fi24P3LocalDefectZeroTranscriptCount = 4 := by
  rw [fi24P3LocalDefectZeroTranscriptCount,
    fi24ThreeLocalTableCertificate_exact]
  decide

/-- The semantic binding between the complete table calculation and the
literal local set of characters.  This is a local cardinality statement.  It
does not mention the ambient block, global weights, or an automorphism. -/
structure Fi24P3LocalDefectZeroCensusBinding
    (Q : Subgroup X)
    (table : Source Q
      (R.1.operations.toLocalNormalizerBlockOperations Q)) : Prop where
  card_eq_transcriptCount :
    Nat.card (LocalDefectZeroCharacter
      (K := K) (tableRadical R Q table)) =
        fi24P3LocalDefectZeroTranscriptCount

/-- The source level radical support for the selected nonprincipal block.
It is the literal carrier form of the relevant consequence of the radical
classification and block defect calculation.  It contains no row, count, or
equivalence assertion. -/
structure Fi24P3NonprincipalRadicalSupportSource
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (Q : Subgroup X)
    (table : Source Q
      (R.1.operations.toLocalNormalizerBlockOperations Q)) : Prop where
  radicalClass_eq :
    ∀ w : WeightFibre (R := R) S.nonprincipalBlock,
      radicalClass w.1 =
        (Quotient.mk'' (tableRadical R Q table) :
          RadicalConjugacyClass (p := 3) (G := X))

/-- The four named rows exhaust the literal local defect zero character set.
The proof uses only row injectivity and the independently bound local count. -/
theorem tableLocalDZ_surjective
    (Q : Subgroup X)
    (table : Source Q
      (R.1.operations.toLocalNormalizerBlockOperations Q))
    (C : Fi24P3LocalDefectZeroCensusBinding R Q table) :
    Function.Surjective (tableLocalDZ R Q table) := by
  classical
  have hLocalCard :
      Nat.card (LocalDefectZeroCharacter
        (K := K) (tableRadical R Q table)) = 4 :=
    C.card_eq_transcriptCount.trans
      fi24P3LocalDefectZeroTranscriptCount_exact
  letI : Finite (LocalDefectZeroCharacter
      (K := K) (tableRadical R Q table)) :=
    Nat.finite_of_card_ne_zero (by rw [hLocalCard]; decide)
  letI : Fintype (LocalDefectZeroCharacter
      (K := K) (tableRadical R Q table)) :=
    Fintype.ofFinite _
  have hinjective : Function.Injective (tableLocalDZ R Q table) := by
    intro r s hrs
    exact table.ordinary_injective (congrArg Subtype.val hrs)
  have hcard :
      Fintype.card P3QSquaredTableRow =
        Fintype.card (LocalDefectZeroCharacter
          (K := K) (tableRadical R Q table)) := by
    rw [show Fintype.card P3QSquaredTableRow = 4 by decide,
      ← Nat.card_eq_fintype_card, hLocalCard]
  exact ((Fintype.bijective_iff_injective_and_card
    (tableLocalDZ R Q table)).2 ⟨hinjective, hcard⟩).2

/-- Construct the formerly external four row coverage from the local census
and radical support. -/
theorem nonprincipalWeightCoverage_of_localCensus_and_radicalSupport
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (Q : Subgroup X)
    (table : Source Q
      (R.1.operations.toLocalNormalizerBlockOperations Q))
    (C : Fi24P3LocalDefectZeroCensusBinding R Q table)
    (A : Fi24P3NonprincipalRadicalSupportSource R S Q table) :
    Fi24P3NonprincipalWeightCoverage R S Q table where
  covers w := by
    let E := localDefectZeroEquivWeightRadicalFibre
      (K := K) Nat.prime_three (tableRadical R Q table)
    let supportedWeight : WeightRadicalFibre
        (K := K) (tableRadical R Q table) :=
      ⟨w.1, A.radicalClass_eq w⟩
    let theta : LocalDefectZeroCharacter
        (K := K) (tableRadical R Q table) :=
      E.symm supportedWeight
    obtain ⟨r, hr⟩ := tableLocalDZ_surjective R Q table C theta
    refine ⟨r, ?_⟩
    change (E (tableLocalDZ R Q table r)).1 = w.1
    rw [hr]
    exact congrArg Subtype.val (E.apply_symm_apply supportedWeight)

end ModularRep.PaperProofs.SporadicFi24P3NonprincipalWeightCoverageFromLocalCensus


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
