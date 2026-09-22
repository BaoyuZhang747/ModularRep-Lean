import Mathlib.FieldTheory.Finite.Basic
import ModularRep.PaperProofs.TypeBFullBlockCondition
import ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation
import ModularRep.PaperProofs.EvenFieldUniversalCentralCoverSource

/-!
# The complete low-rank even-field Type C source application

Schaeffer Fry (2014), Theorem 5.5, pp. 41--42, proves the blockwise
Alperin weight condition for Sp4(2^a), a >= 2, and Sp6(2^a), a >= 1,
at every prime other than two. The uniform source below uses the common
range a >= 2. Thus the exceptional odd-prime cover of Sp6(2) is absent.

The fixed complete family retains the full actual automorphism group,
including the exceptional graph automorphism of Sp4 in characteristic two.
No field-only substitute, freely chosen family or conclusion predicate is
used. E1 structural facts and the E2 theorem remain explicitly external.

K constructs the literal Sp-to-PSp prime-to-ell cover from the actual own
universal-cover property and derives the source exponent from the actual
finite field. This module contains no certificate inhabitant or overall
Type C/manuscript verification claim.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeCLowRankEvenSourceApplication

open ModularRep FDRepSimpleClassKZero
open OddTwoConformalProjectiveRealisation (Sp PSp spProjection)
open EvenFieldFLZSourceConditions EvenFieldFLZ318FixedTheoremGate
open TypeBFixedRootDefinitionFamily TypeBFullBlockCondition

/-- Actual characteristic two and actual cardinality greater than two imply
the precise exponent range in Theorem 5.5. -/
theorem even_field_exponent (F : Type) [Field F] [Finite F] [CharP F 2]
    (hcard : 2 < Nat.card F) :
    ∃ a : ℕ, 2 ≤ a ∧ Nat.card F = 2 ^ a := by
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨a, _, ha⟩ := FiniteField.card F 2
  have hactual : Nat.card F = 2 ^ (a : ℕ) := by
    simpa only [Nat.card_eq_fintype_card] using ha
  refine ⟨a, ?_, hactual⟩
  have hpos : 0 < (a : ℕ) := a.pos
  by_contra h
  have ha_one : (a : ℕ) = 1 := by omega
  rw [ha_one, pow_one] at hactual
  omega

section ActualCover

variable (r : ℕ) (F : Type) [Field F] [Finite F]

local instance lowRankSpFintype : Fintype (Sp r F) := Fintype.ofFinite _
local instance lowRankPSpFintype : Fintype (PSp r F) := Fintype.ofFinite _

/-- Standard E1 facts on the literal matrix groups. In the source lane
these are licensed for r = 2 or 3 and |F| = 2^a with a >= 2. The full
universal-cover assertion is a group fact, independent of ell and of any
character, block, correspondence or target witness. -/
structure CentrelessOwnCoverFacts : Prop where
  perfect : commutator (Sp r F) = ⊤
  simple : IsSimpleGroup (PSp r F)
  nonabelian : ¬ IsMulCommutative (PSp r F)
  center_eq_bot : Subgroup.center (Sp r F) = ⊥
  ownUniversalCover : IsOwnUniversalCover (Sp r F)

variable (facts : CentrelessOwnCoverFacts r F)

/-- The actual centre quotient is an equivalence when its actual kernel is
trivial; its forward map is still exactly spProjection. -/
def projectiveEquiv : Sp r F ≃* PSp r F :=
  MulEquiv.ofBijective (spProjection r F) ⟨by
    apply (MonoidHom.ker_eq_bot_iff (spProjection r F)).mp
    change (QuotientGroup.mk' (Subgroup.center (Sp r F))).ker = ⊥
    rw [QuotientGroup.ker_mk', facts.center_eq_bot],
    QuotientGroup.mk'_surjective _⟩

@[simp] theorem projectiveEquiv_apply (g : Sp r F) :
    projectiveEquiv r F facts g = spProjection r F g := rfl

include facts in
/-- The full universal property gives the precise maximality statement
over the SAME projective quotient. Its section is surjective because the
extension's total group is perfect, by the existing neutral K lemma. -/
theorem projective_maximal
    (D : Type) [Group D] [Fintype D] (f : D →* PSp r F)
    (hsurjective : Function.Surjective f)
    (hcentral : f.ker ≤ Subgroup.center D)
    (hperfect : commutator D = ⊤) :
    ∃ lift : Sp r F →* D,
      Function.Surjective lift ∧ f.comp lift = spProjection r F := by
  let e := projectiveEquiv r F facts
  let fUp : D →* Sp r F := e.symm.toMonoidHom.comp f
  have hcentralUp : fUp.ker ≤ Subgroup.center D := by
    intro d hd
    apply hcentral
    change f d = 1
    change e.symm (f d) = 1 at hd
    exact e.symm.map_eq_one_iff.mp hd
  obtain ⟨lift, hlift, _⟩ := facts.ownUniversalCover.2 D fUp
    ⟨e.symm.surjective.comp hsurjective, hcentralUp⟩
  refine ⟨lift,
    centralExtension_section_surjective fUp hcentralUp lift hlift hperfect, ?_⟩
  apply MonoidHom.ext
  intro g
  have h := congrArg (fun f : Sp r F →* Sp r F => f g) hlift
  change e.symm (f (lift g)) = g at h
  change f (lift g) = spProjection r F g
  calc
    f (lift g) = e (e.symm (f (lift g))) := (e.apply_symm_apply _).symm
    _ = e g := congrArg e h
    _ = spProjection r F g := rfl

/-- The canonical prime-to-ell cover uses literal Sp, literal PSp and the
literal centre projection, for every prime ell. -/
def actualCover (ell : ℕ) (prime : Nat.Prime ell) :
    EllPrimeCoverSource ell (Sp r F) where
  S := PSp r F
  quotient := spProjection r F
  quotient_surjective := QuotientGroup.mk'_surjective _
  quotient_kernel := QuotientGroup.ker_mk' _
  perfect := facts.perfect
  simple := facts.simple
  nonabelian := facts.nonabelian
  centerPrimeTo := by
    simpa [facts.center_eq_bot] using prime.not_dvd_one
  maximal := by
    intro D _ _ f hsurjective hcentral hperfect _
    exact projective_maximal r F facts D f hsurjective hcentral hperfect

@[simp] theorem actualCover_quotient (ell : ℕ) (prime : Nat.Prime ell) :
    (actualCover r F facts ell prime).quotient = spProjection r F := rfl

end ActualCover

/-- Uniform E2 Theorem 5.5 in its common centreless range. All character and
specified block data belong to the same authenticated standard modular
system. The output is the independently fixed COMPLETE family, including
full automorphism equivariance; neither a family nor a target predicate is
an arbitrary parameter. No inhabitant of this published certificate is
asserted here. -/
structure Theorem55Certificate : Prop where
  allBlocks : ∀ (ell r a : ℕ) (F k K : Type)
      [Field F] [Finite F] [CharP F 2]
      [Field k] [Field K] [CharP k ell] [IsAlgClosed k] [CharZero K]
      [Fintype (Sp r F)] [Fintype (LiteralPrimitiveBlock k (Sp r F))]
      (prime : Nat.Prime ell)
      (iota : PrimeRegularRootEmbedding ell k K (Sp r F))
      (hinj : IrreducibleBrauerCharacterInjectivity iota)
      (blocks : BlockIdempotentDecomposition
        (fun b : LiteralPrimitiveBlock k (Sp r F) => b.1))
      (localSource : PrimitiveLocalSource iota)
      (coefficient : SpathCoefficientField ell k prime)
      (cover : EllPrimeCoverSource ell (Sp r F))
      (simpleEquiv : cover.S ≃* PSp r F),
    (r = 2 ∨ r = 3) → 2 ≤ a → Nat.card F = 2 ^ a → ell ≠ 2 →
    simpleEquiv.toMonoidHom.comp cover.quotient = spProjection r F →
    Nonempty (FamilyWitness
      (primitiveFamily iota hinj blocks prime localSource) cover)

section Apply

variable (ell r : ℕ) (F k K : Type)
variable [Field F] [Finite F] [CharP F 2]
variable [Field k] [Field K] [CharP k ell] [IsAlgClosed k] [CharZero K]

local instance applicationSpFintype : Fintype (Sp r F) := Fintype.ofFinite _

variable [Fintype (LiteralPrimitiveBlock k (Sp r F))]
variable (prime : Nat.Prime ell) (facts : CentrelessOwnCoverFacts r F)
variable (iota : PrimeRegularRootEmbedding ell k K (Sp r F))
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition
  (fun b : LiteralPrimitiveBlock k (Sp r F) => b.1))
variable (localSource : PrimitiveLocalSource iota)
variable (coefficient : SpathCoefficientField ell k prime)

include coefficient in
/-- Source application after K derives the actual exponent and constructs
the exact prime-to-ell cover. The q=2 and defining-prime cases are outside
this particular application. -/
theorem full_block_condition_source_instantiated
    (hrank : r = 2 ∨ r = 3) (hcard : 2 < Nat.card F) (hell : ell ≠ 2)
    (source : Theorem55Certificate) :
    Nonempty (FamilyWitness
      (primitiveFamily iota hinj blocks prime localSource)
      (actualCover r F facts ell prime)) := by
  obtain ⟨a, ha, hfield⟩ := even_field_exponent F hcard
  exact source.allBlocks ell r a F k K prime iota hinj blocks localSource
    coefficient (actualCover r F facts ell prime) (MulEquiv.refl _)
    hrank ha hfield hell rfl

end Apply

section RankTwo

variable (ell : ℕ) (F k K : Type)
variable [Field F] [Finite F] [CharP F 2]
variable [Field k] [Field K] [CharP k ell] [IsAlgClosed k] [CharZero K]

local instance rankTwoSpFintype : Fintype (Sp 2 F) := Fintype.ofFinite _

variable [Fintype (LiteralPrimitiveBlock k (Sp 2 F))]
variable (prime : Nat.Prime ell) (facts : CentrelessOwnCoverFacts 2 F)
variable (iota : PrimeRegularRootEmbedding ell k K (Sp 2 F))
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition
  (fun b : LiteralPrimitiveBlock k (Sp 2 F) => b.1))
variable (localSource : PrimitiveLocalSource iota)
variable (coefficient : SpathCoefficientField ell k prime)

include coefficient in
/-- The requested rank-two branch on literal Sp4(F), with the same complete
family and full actual automorphism group as the uniform source. -/
theorem rank_two_full_block_condition
    (hcard : 2 < Nat.card F) (hell : ell ≠ 2) (source : Theorem55Certificate) :
    Nonempty (FamilyWitness
      (primitiveFamily iota hinj blocks prime localSource)
      (actualCover 2 F facts ell prime)) :=
  full_block_condition_source_instantiated ell 2 F k K prime facts iota hinj
    blocks localSource coefficient (Or.inl rfl) hcard hell source

/-- A chosen complete witness on exactly that rank-two family and cover. -/
def rankTwoWitness
    (hcard : 2 < Nat.card F) (hell : ell ≠ 2) (source : Theorem55Certificate) :
    FamilyWitness
      (primitiveFamily iota hinj blocks prime localSource)
      (actualCover 2 F facts ell prime) :=
  Classical.choice (rank_two_full_block_condition ell F k K prime facts iota
    hinj blocks localSource coefficient hcard hell source)

end RankTwo

end ModularRep.PaperProofs.TypeCLowRankEvenSourceApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
