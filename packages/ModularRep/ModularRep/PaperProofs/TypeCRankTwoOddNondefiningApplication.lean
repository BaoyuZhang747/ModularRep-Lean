import ModularRep.PaperProofs.TypeCRankTwoCyclicSourceApplication

/-!
# Rank-two odd-field nondefining-prime dispatch

Both existing branches have literally the same complete canonical family
and the same actual Sp4(F)-to-PSp4(F) prime-to-ell cover. This K join splits
on ell dividing q^2-1. The positive branch applies Brough--Schaeffer Fry;
the negative branch applies the computed cyclic-subgroup argument followed
by the existing general cyclic-defect certificate.

No new source record, independently chosen family, target predicate, or
cross-branch root/character identification is introduced. The original
simple-order divisor and nondefining condition remain explicit.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeCRankTwoOddNondefiningApplication

open ModularRep FDRepSimpleClassKZero
open OddTwoConformalProjectiveRealisation (Sp PSp)
open OddTwoUniversalPrimeToTwoSelfCover
open EvenFieldFLZSourceConditions
open TypeBFixedRootDefinitionFamily TypeBFullBlockCondition

variable (ell : ℕ) (F k K : Type)
variable [Field F] [Finite F]
variable [Field k] [Field K] [CharP k ell] [IsAlgClosed k] [CharZero K]

local instance applicationSpFintype : Fintype (Sp 2 F) := Fintype.ofFinite _

variable [Fintype (LiteralPrimitiveBlock k (Sp 2 F))]
variable (prime : Nat.Prime ell) (hell : ell ≠ 2)
variable (coverSource : OddSymplecticFullCoverSource 2 F)
variable (perfect : commutator (Sp 2 F) = ⊤)
variable (structural : TypeCRankTwoCyclicSourceApplication.OrderAndTorusSource F)
variable (iota : PrimeRegularRootEmbedding ell k K (Sp 2 F))
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition
  (fun b : LiteralPrimitiveBlock k (Sp 2 F) => b.1))
variable (localSource : PrimitiveLocalSource iota)
variable (coefficient : SpathCoefficientField ell k prime)

include structural coefficient in
/-- Actual odd-field rank-two nondefining applicability. Only the two
previously licensed certificates and actual group-only structural inputs
are consumed; both branches return this identical complete target. -/
theorem full_block_condition_source_instantiated
    (divides_simple_order : ell ∣ Nat.card (PSp 2 F))
    (nondefining : ¬ ell ∣ Nat.card F)
    (oddDivisorSource : TypeCRankTwoOddSourceApplication.Theorem11Certificate)
    (cyclicSource : TypeBCyclicDefectSource.CyclicDefectCertificate) :
    Nonempty (FamilyWitness
      (primitiveFamily iota hinj blocks prime localSource)
      (TypeCRankTwoOddSourceApplication.actualCover F coverSource perfect ell prime hell)) := by
  by_cases hdiv : ell ∣ (Nat.card F) ^ 2 - 1
  · exact TypeCRankTwoOddSourceApplication.full_block_condition_source_instantiated
      ell F k K prime hell coverSource perfect iota hinj blocks localSource
      coefficient hdiv oddDivisorSource
  · exact TypeCRankTwoCyclicSourceApplication.full_block_condition_source_instantiated
      ell F k K prime hell coverSource perfect structural iota hinj blocks localSource
      coefficient divides_simple_order nondefining hdiv cyclicSource

/-- Choose an inhabitant of the one fixed complete family after the
arithmetic dispatch; no new family or source conclusion is selected. -/
def witness
    (divides_simple_order : ell ∣ Nat.card (PSp 2 F))
    (nondefining : ¬ ell ∣ Nat.card F)
    (oddDivisorSource : TypeCRankTwoOddSourceApplication.Theorem11Certificate)
    (cyclicSource : TypeBCyclicDefectSource.CyclicDefectCertificate) :
    FamilyWitness
      (primitiveFamily iota hinj blocks prime localSource)
      (TypeCRankTwoOddSourceApplication.actualCover F coverSource perfect ell prime hell) :=
  Classical.choice (full_block_condition_source_instantiated ell F k K prime hell
    coverSource perfect structural iota hinj blocks localSource coefficient
    divides_simple_order nondefining oddDivisorSource cyclicSource)

end ModularRep.PaperProofs.TypeCRankTwoOddNondefiningApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
