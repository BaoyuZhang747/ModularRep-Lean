import Mathlib.FieldTheory.Finite.Basic
import ModularRep.PaperProofs.TypeBFullBlockCondition
import ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation

/-!
# Defining characteristic on the literal Type C cover and complete family

Späth (2013), Theorem C, p. 161, with its proof on pp. 215--217, supplies
the complete Definition 4.1 condition in defining characteristic. The
uniform source below is its Type C specialization on actual matrix groups,
one fixed modular-system realization and the independently defined complete
primitive family. There is no arbitrary family, result predicate, matching
or relation among its inputs.

K derives the characteristic prime and prime-to-characteristic centre,
constructs the exact Sp-to-PSp cover from standard structural facts, and
applies the uniform source. No certificate inhabitant, Lie classification,
Schur multiplier computation or unconditional Type C result is constructed.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeCDefiningCharacteristicSourceApplication

open ModularRep FDRepSimpleClassKZero
open OddTwoConformalProjectiveRealisation (Sp PSp spProjection)
open EvenFieldFLZSourceConditions
open TypeBFixedRootDefinitionFamily TypeBFullBlockCondition

section FieldArithmetic

variable (F : Type) [Field F] [Finite F] (p : ℕ) [CharP F p]

include F in
/-- The defining prime is determined by the actual finite field. -/
theorem defining_prime : Nat.Prime p := CharP.char_is_prime F p

/-- The actual characteristic divides the actual field cardinality. -/
theorem defining_dvd_card : p ∣ Nat.card F := by
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨a, _, ha⟩ := FiniteField.card F p
  rw [Nat.card_eq_fintype_card, ha]
  exact dvd_pow_self p a.ne_zero

/-- The scalar centre order is prime to the defining characteristic,
including characteristic two. No odd-field guard is introduced. -/
theorem defining_not_dvd_scalar_center :
    ¬ p ∣ Nat.gcd 2 (Nat.card F - 1) := by
  intro h
  have hpred : p ∣ Nat.card F - 1 := h.trans (Nat.gcd_dvd_right 2 _)
  have hcard : 1 ≤ Nat.card F := Nat.succ_le_of_lt Nat.card_pos
  have hdifference := Nat.dvd_sub (defining_dvd_card F p) hpred
  have hdifference_eq : Nat.card F - (Nat.card F - 1) = 1 := by omega
  rw [hdifference_eq] at hdifference
  exact (defining_prime F p).ne_one (Nat.dvd_one.mp hdifference)

end FieldArithmetic

section ActualCover

variable (p n : ℕ) (F : Type) [Field F] [Finite F]

local instance definingSpFintype : Fintype (Sp n F) := Fintype.ofFinite _
local instance definingPSpFintype : Fintype (PSp n F) := Fintype.ofFinite _

/-- Standard E1 structural facts on the literal matrix quotient. The final
field is only the actual prime-to-p universal-cover property. Simplicity
excludes the nonsimple `(n,q)=(2,2)` case; no Type B exception is used. -/
structure CoverFacts : Prop where
  rank : 2 ≤ n
  perfect : commutator (Sp n F) = ⊤
  simple : IsSimpleGroup (PSp n F)
  nonabelian : ¬ IsMulCommutative (PSp n F)
  center_order : Nat.card (Subgroup.center (Sp n F)) =
    Nat.gcd 2 (Nat.card F - 1)
  maximal : ∀ (D : Type) [Group D] [Fintype D] (f : D →* PSp n F),
    Function.Surjective f → f.ker ≤ Subgroup.center D →
      commutator D = ⊤ → ¬ p ∣ Nat.card f.ker →
      ∃ lift : Sp n F →* D,
        Function.Surjective lift ∧ f.comp lift = spProjection n F

variable [CharP F p] (facts : CoverFacts p n F)

include facts in
/-- Only the scalar-centre order is external; its prime-to-p consequence
comes from the actual field arithmetic. -/
theorem center_primeTo : ¬ p ∣ Nat.card (Subgroup.center (Sp n F)) := by
  rw [facts.center_order]
  exact defining_not_dvd_scalar_center F p

/-- The carrier and projection are literal and fixed before any character
data or published block-condition theorem is selected. -/
def actualCover : EllPrimeCoverSource p (Sp n F) where
  S := PSp n F
  quotient := spProjection n F
  quotient_surjective := QuotientGroup.mk'_surjective _
  quotient_kernel := QuotientGroup.ker_mk' _
  perfect := facts.perfect
  simple := facts.simple
  nonabelian := facts.nonabelian
  centerPrimeTo := center_primeTo p n F facts
  maximal := facts.maximal

@[simp] theorem actualCover_quotient :
    (actualCover p n F facts).quotient = spProjection n F := rfl

end ActualCover

/-- Uniform E2 Theorem C on actual Type C groups. The coefficient hypothesis,
specified local source and root guards have their fixed standard meanings.
The simple quotient and its projection are explicitly bound to PSp; an
unrelated simple quotient cannot be substituted. The source's conclusion
is the canonical COMPLETE family, never a caller-selected target.

The full output's standard interpretation is the existing authenticated
Späth 4.1 / block-formulation dictionary. This record asserts no inhabitant
and supplies no desired conclusion as a hypothesis to an application. -/
structure TheoremCCertificate : Prop where
  allBlocks : ∀ (p n : ℕ) (F k K : Type)
      [Field F] [Finite F] [CharP F p]
      [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
      [Fintype (Sp n F)] [Fintype (LiteralPrimitiveBlock k (Sp n F))]
      (prime : Nat.Prime p)
      (iota : PrimeRegularRootEmbedding p k K (Sp n F))
      (hinj : IrreducibleBrauerCharacterInjectivity iota)
      (blocks : BlockIdempotentDecomposition
        (fun b : LiteralPrimitiveBlock k (Sp n F) => b.1))
      (localSource : PrimitiveLocalSource iota)
      (coefficient : SpathCoefficientField p k prime)
      (cover : EllPrimeCoverSource p (Sp n F))
      (simpleEquiv : cover.S ≃* PSp n F),
    2 ≤ n →
    simpleEquiv.toMonoidHom.comp cover.quotient = spProjection n F →
    Nonempty (FamilyWitness
      (primitiveFamily iota hinj blocks prime localSource) cover)

section Apply

variable (p n : ℕ) (F k K : Type)
variable [Field F] [Finite F] [CharP F p]
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]

local instance applicationSpFintype : Fintype (Sp n F) := Fintype.ofFinite _

variable [Fintype (LiteralPrimitiveBlock k (Sp n F))]
variable (facts : CoverFacts p n F)
variable (iota : PrimeRegularRootEmbedding p k K (Sp n F))
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition
  (fun b : LiteralPrimitiveBlock k (Sp n F) => b.1))
variable (localSource : PrimitiveLocalSource iota)
variable (coefficient : SpathCoefficientField p k (defining_prime F p))

include coefficient in
/-- Apply the general published theorem only after the literal cover and
its characteristic applicability have been constructed in K. -/
theorem full_block_condition_source_instantiated (source : TheoremCCertificate) :
    Nonempty (FamilyWitness
      (primitiveFamily iota hinj blocks (defining_prime F p) localSource)
      (actualCover p n F facts)) := by
  exact source.allBlocks p n F k K (defining_prime F p) iota hinj blocks
    localSource coefficient (actualCover p n F facts) (MulEquiv.refl _)
    facts.rank rfl

/-- A chosen complete witness on the SAME actual family and cover. -/
def witness (source : TheoremCCertificate) :
    FamilyWitness
      (primitiveFamily iota hinj blocks (defining_prime F p) localSource)
      (actualCover p n F facts) :=
  Classical.choice (full_block_condition_source_instantiated
    p n F k K facts iota hinj blocks localSource coefficient source)

end Apply

end ModularRep.PaperProofs.TypeCDefiningCharacteristicSourceApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
