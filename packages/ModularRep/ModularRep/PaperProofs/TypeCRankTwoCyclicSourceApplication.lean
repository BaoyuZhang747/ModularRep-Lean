import ModularRep.PaperProofs.TypeCRankTwoOddSourceApplication
import ModularRep.PaperProofs.TypeBCyclicDefectSource
import ModularRep.RankTwoSymplectic

/-!
# The remaining rank-two odd-field cyclic branch

The only new structural source contains the order of the ACTUAL Sp4(F)
and an existential cyclic subgroup of order q^2+1. The existing arithmetic
and Sylow argument derives cyclicity of every relevant ell-subgroup.
The existing GENERAL cyclic-defect certificate then supplies the fixed
complete family on the SAME actual Sp4-to-PSp4 prime-to-ell cover.

The original simple-order divisibility remains explicit. In particular
q=3, ell=5 is included. No new block-result, subgroup-cyclicity, torus
equivariance, or independent family assumption is introduced.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeCRankTwoCyclicSourceApplication

open ModularRep FDRepSimpleClassKZero
open OddTwoConformalProjectiveRealisation (Sp PSp spProjection)
open OddTwoUniversalPrimeToTwoSelfCover
open EvenFieldFLZSourceConditions
open TypeBFixedRootDefinitionFamily TypeBFullBlockCondition
open ManuscriptVerification.RankTwoSymplectic

/-- Standard E1 order and torus data, on the literal matrix group.
The torus is existential and carries no choice or action condition. -/
structure OrderAndTorusSource (F : Type) [Field F] [Finite F] : Prop where
  order : Nat.card (Sp 2 F) =
    (Nat.card F) ^ 4 * ((Nat.card F) ^ 2 - 1) * ((Nat.card F) ^ 4 - 1)
  torus : ∃ T : Subgroup (Sp 2 F),
    IsCyclic T ∧ Nat.card T = (Nat.card F) ^ 2 + 1

section Groups

variable (F : Type) [Field F] [Finite F]
variable (coverSource : OddSymplecticFullCoverSource 2 F)
variable (structural : OrderAndTorusSource F)

include coverSource in
theorem two_lt_card : 2 < Nat.card F := by
  have hcard : 1 < Nat.card F := Finite.one_lt_card
  obtain ⟨a, ha⟩ := coverSource.field_odd
  omega

include structural in
theorem factored_order : Nat.card (Sp 2 F) =
    (Nat.card F) ^ 4 * ((Nat.card F) ^ 2 - 1) ^ 2 * ((Nat.card F) ^ 2 + 1) := by
  rw [structural.order]
  exact sp4_order_formula_factorization (Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne')

include structural in
/-- The simple-order divisor is transported through the actual quotient,
then the existing arithmetic exposes the q^2+1 branch. -/
theorem divides_torus_order (ell : ℕ) (prime : Nat.Prime ell)
    (divides_simple_order : ell ∣ Nat.card (PSp 2 F))
    (nondefining : ¬ ell ∣ Nat.card F)
    (remaining : ¬ ell ∣ (Nat.card F) ^ 2 - 1) :
    ell ∣ (Nat.card F) ^ 2 + 1 := by
  have hSp : ell ∣ Nat.card (Sp 2 F) := divides_simple_order.trans
    (Subgroup.card_dvd_of_surjective (spProjection 2 F)
      (QuotientGroup.mk'_surjective _))
  rw [factored_order F structural] at hSp
  exact prime_dvd_q_sq_add_one_of_dvd_sp4_factored_order prime hSp nondefining remaining

include coverSource structural in
/-- Cyclicity is proved for EVERY actual ell-subgroup, using one actual
cyclic torus and the already checked full-prime-part/Sylow argument. -/
theorem every_ell_subgroup_cyclic (ell : ℕ) (prime : Nat.Prime ell)
    (nondefining : ¬ ell ∣ Nat.card F)
    (remaining : ¬ ell ∣ (Nat.card F) ^ 2 - 1)
    (D : Subgroup (Sp 2 F)) (hD : IsPGroup ell D) : IsCyclic D := by
  obtain ⟨T, hcyclic, hcard⟩ := structural.torus
  letI : IsCyclic T := hcyclic
  exact order_and_cyclic_torus_force_cyclic_ell_subgroups prime
    (two_lt_card F coverSource) nondefining remaining
    (factored_order F structural) T hcard D hD

end Groups

section Apply

variable (ell : ℕ) (F k K : Type)
variable [Field F] [Finite F]
variable [Field k] [Field K] [CharP k ell] [IsAlgClosed k] [CharZero K]

local instance applicationSpFintype : Fintype (Sp 2 F) := Fintype.ofFinite _

variable [Fintype (LiteralPrimitiveBlock k (Sp 2 F))]
variable (prime : Nat.Prime ell) (hell : ell ≠ 2)
variable (coverSource : OddSymplecticFullCoverSource 2 F)
variable (perfect : commutator (Sp 2 F) = ⊤)
variable (structural : OrderAndTorusSource F)
variable (iota : PrimeRegularRootEmbedding ell k K (Sp 2 F))
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition
  (fun b : LiteralPrimitiveBlock k (Sp 2 F) => b.1))
variable (localSource : PrimitiveLocalSource iota)
variable (coefficient : SpathCoefficientField ell k prime)

include structural coefficient in
/-- The inherited generic source is applied only AFTER K cyclicity, with
the original simple-order divisor and the same complete canonical family. -/
theorem full_block_condition_source_instantiated
    (divides_simple_order : ell ∣ Nat.card (PSp 2 F))
    (nondefining : ¬ ell ∣ Nat.card F)
    (remaining : ¬ ell ∣ (Nat.card F) ^ 2 - 1)
    (source : TypeBCyclicDefectSource.CyclicDefectCertificate) :
    Nonempty (FamilyWitness
      (primitiveFamily iota hinj blocks prime localSource)
      (TypeCRankTwoOddSourceApplication.actualCover F coverSource perfect ell prime hell)) :=
  source.allBlocks prime (prime.odd_of_ne_two hell) iota hinj blocks localSource coefficient
    (TypeCRankTwoOddSourceApplication.actualCover F coverSource perfect ell prime hell)
    divides_simple_order
    (every_ell_subgroup_cyclic F coverSource structural ell prime nondefining remaining)

/-- Choose only the inhabitant supplied for this exact complete target. -/
def witness
    (divides_simple_order : ell ∣ Nat.card (PSp 2 F))
    (nondefining : ¬ ell ∣ Nat.card F)
    (remaining : ¬ ell ∣ (Nat.card F) ^ 2 - 1)
    (source : TypeBCyclicDefectSource.CyclicDefectCertificate) :
    FamilyWitness
      (primitiveFamily iota hinj blocks prime localSource)
      (TypeCRankTwoOddSourceApplication.actualCover F coverSource perfect ell prime hell) :=
  Classical.choice (full_block_condition_source_instantiated ell F k K prime hell
    coverSource perfect structural iota hinj blocks localSource coefficient
    divides_simple_order nondefining remaining source)

end Apply

end ModularRep.PaperProofs.TypeCRankTwoCyclicSourceApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
