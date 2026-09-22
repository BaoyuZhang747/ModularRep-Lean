import Mathlib.FieldTheory.Finite.Basic
import ModularRep.PaperProofs.TypeBFullBlockCondition
import ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation
import ModularRep.PaperProofs.OddTwoUniversalPrimeToTwoSelfCover

/-!
# Rank-two odd-field odd-divisor source application

Brough--Schaeffer Fry (2020), Theorem 1.1, p. 1182, proves the complete
inductive blockwise Alperin weight condition for PSp4(q), q an odd prime
power, at primes dividing q^2 - 1. This module specializes to odd ell.
Its fixed complete family is on the literal Sp4(F) prime-to-ell cover.

The actual full-cover source, including q = 3, is reused. K obtains
surjectivity of its lifts into perfect central extensions and therefore
constructs the required prime-to-ell cover on the actual projection.
No characteristic-ell hypothesis is placed on F. The coefficient field k
has characteristic ell, as required by the character theory.

The q = 3 odd-divisor case is explicitly shown empty by arithmetic; it is
not removed by a q >= 5 source premise. No certificate inhabitant, final
result premise, independently chosen family, or overall verification is
asserted here.
-/

noncomputable section

open scoped MonoidAlgebra commutatorElement

namespace ModularRep.PaperProofs.TypeCRankTwoOddSourceApplication

open ModularRep FDRepSimpleClassKZero
open OddTwoConformalProjectiveRealisation (Sp PSp spProjection)
open OddTwoUniversalPrimeToTwoSelfCover
open EvenFieldFLZSourceConditions EvenFieldFLZ318FixedTheoremGate
open TypeBFixedRootDefinitionFamily TypeBFullBlockCondition

universe u

/-- A subgroup mapping onto a central quotient of a perfect group is the
whole group. This is the same elementary commutator cancellation as the
existing section-surjectivity lemma, without requiring an identity base map. -/
theorem lift_surjective_of_central_comp
    {U D S : Type u} [Group U] [Group D] [Group S]
    (f : D →* S) (lift : U →* D)
    (hcomp : Function.Surjective (f.comp lift))
    (hcentral : f.ker ≤ Subgroup.center D)
    (hperfect : commutator D = ⊤) : Function.Surjective lift := by
  rw [← MonoidHom.range_eq_top]
  apply top_unique
  rw [← hperfect, commutator_def, Subgroup.commutator_le]
  intro x _ y _
  obtain ⟨ux, hux⟩ := hcomp (f x)
  obtain ⟨uy, huy⟩ := hcomp (f y)
  change f (lift ux) = f x at hux
  change f (lift uy) = f y at huy
  have hx : (lift ux)⁻¹ * x ∈ Subgroup.center D :=
    hcentral ((MonoidHom.eq_iff f).mp hux.symm)
  have hy : (lift uy)⁻¹ * y ∈ Subgroup.center D :=
    hcentral ((MonoidHom.eq_iff f).mp huy.symm)
  have hxcomm : Commute ((lift ux)⁻¹ * x) y :=
    (Subgroup.mem_center_iff.mp hx y).symm
  have hycomm : Commute (lift ux) ((lift uy)⁻¹ * y) :=
    Subgroup.mem_center_iff.mp hy (lift ux)
  refine ⟨⁅ux, uy⁆, ?_⟩
  rw [map_commutatorElement]
  symm
  calc
    ⁅x, y⁆ = ⁅lift ux * ((lift ux)⁻¹ * x), y⁆ := by
      rw [mul_inv_cancel_left]
    _ = ⁅lift ux, y⁆ := by
      rw [commutatorElement_mul_left_eq_conj_mul, hxcomm.commutator_eq]
      simp
    _ = ⁅lift ux, lift uy * ((lift uy)⁻¹ * y)⁆ := by
      rw [mul_inv_cancel_left]
    _ = ⁅lift ux, lift uy⁆ := by
      rw [commutatorElement_mul_right_eq_mul_conj, hycomm.commutator_eq]
      simp

section Arithmetic

variable (ell : ℕ) (F : Type) [Field F] [Finite F]
variable (prime : Nat.Prime ell)

include prime

/-- Divisibility by q^2-1 forces the coefficient prime to be nondefining.
The conclusion uses only the actual field cardinality. -/
theorem not_dvd_card (hdiv : ell ∣ (Nat.card F) ^ 2 - 1) :
    ¬ ell ∣ Nat.card F := by
  intro h
  have hsq : ell ∣ (Nat.card F) ^ 2 :=
    h.trans (dvd_pow_self (Nat.card F) (by decide : 2 ≠ 0))
  have hpositive : 0 < (Nat.card F) ^ 2 := pow_pos Nat.card_pos _
  have hdifference := Nat.dvd_sub hsq hdiv
  have hone : (Nat.card F) ^ 2 - ((Nat.card F) ^ 2 - 1) = 1 := by omega
  rw [hone] at hdifference
  exact prime.not_dvd_one hdifference

/-- If p is the actual defining characteristic, it is not ell. There is
no `[CharP F ell]` assumption in this nondefining lane. -/
theorem nondefining (p : ℕ) [CharP F p]
    (hdiv : ell ∣ (Nat.card F) ^ 2 - 1) : ell ≠ p := by
  intro h
  have hdefining : p ∣ Nat.card F := by
    letI : Fintype F := Fintype.ofFinite F
    obtain ⟨a, _, ha⟩ := FiniteField.card F p
    rw [Nat.card_eq_fintype_card, ha]
    exact dvd_pow_self p a.ne_zero
  exact not_dvd_card ell F prime hdiv (h.symm ▸ hdefining)

/-- q=3 is retained in the odd-field structural source. No odd prime
divides its q^2-1, so this particular branch has no such input at q=3. -/
theorem card_ne_three (hell : ell ≠ 2)
    (hdiv : ell ∣ (Nat.card F) ^ 2 - 1) : Nat.card F ≠ 3 := by
  intro hcard
  have height : ell ∣ 8 := by
    norm_num [hcard] at hdiv
    exact hdiv
  have htwo : ell ∣ 2 := prime.dvd_of_dvd_pow (show ell ∣ 2 ^ 3 from height)
  rcases (Nat.dvd_prime Nat.prime_two).mp htwo with h | h
  · exact prime.ne_one h
  · exact hell h

end Arithmetic

section ActualCover

variable (F : Type) [Field F] [Finite F]

local instance rankTwoSpFintype : Fintype (Sp 2 F) := Fintype.ofFinite _
local instance rankTwoPSpFintype : Fintype (PSp 2 F) := Fintype.ofFinite _

variable (source : OddSymplecticFullCoverSource 2 F)

include source in
/-- The universal property and the elementary lift lemma derive maximality
over the literal Sp4-to-PSp4 map. No new cover conclusion is a source field. -/
theorem projection_maximal
    (D : Type) [Group D] [Fintype D] (f : D →* PSp 2 F)
    (hsurjective : Function.Surjective f)
    (hcentral : f.ker ≤ Subgroup.center D)
    (hperfect : commutator D = ⊤) :
    ∃ lift : Sp 2 F →* D,
      Function.Surjective lift ∧ f.comp lift = spProjection 2 F := by
  obtain ⟨lift, hlift, _⟩ := source.fullCover.2 D f ⟨hsurjective, hcentral⟩
  have hcomp : Function.Surjective (f.comp lift) := by
    rw [hlift]
    exact source.fullCover.1.1
  exact ⟨lift, lift_surjective_of_central_comp f lift hcomp hcentral hperfect, hlift⟩

include source in
theorem center_primeTo (ell : ℕ) (prime : Nat.Prime ell) (hell : ell ≠ 2) :
    ¬ ell ∣ Nat.card (Subgroup.center (Sp 2 F)) := by
  rw [source.center_card]
  intro h
  rcases (Nat.dvd_prime Nat.prime_two).mp h with h | h
  · exact prime.ne_one h
  · exact hell h

/-- Actual Sp4(F), its whole-centre quotient, and its fixed projection.
Sp perfectness is the standard structural fact on this exact group; the
remaining cover properties come from the existing full-cover source. -/
def actualCover (perfect : commutator (Sp 2 F) = ⊤)
    (ell : ℕ) (prime : Nat.Prime ell) (hell : ell ≠ 2) :
    EllPrimeCoverSource ell (Sp 2 F) where
  S := PSp 2 F
  quotient := spProjection 2 F
  quotient_surjective := QuotientGroup.mk'_surjective _
  quotient_kernel := QuotientGroup.ker_mk' _
  perfect := perfect
  simple := source.simple
  nonabelian := source.nonabelian
  centerPrimeTo := center_primeTo F source ell prime hell
  maximal := by
    intro D _ _ f hsurjective hcentral hperfect _
    exact projection_maximal F source D f hsurjective hcentral hperfect

@[simp] theorem actualCover_quotient (perfect : commutator (Sp 2 F) = ⊤)
    (ell : ℕ) (prime : Nat.Prime ell) (hell : ell ≠ 2) :
    (actualCover F source perfect ell prime hell).quotient = spProjection 2 F := rfl

end ActualCover

/-- Uniform E2 Brough--Schaeffer Fry Theorem 1.1 on the independently fixed
complete family, restricted to its odd-prime part. All coefficient, root
and specified local-source data have their authenticated standard meanings.
The simple quotient and projection are explicitly fixed to literal PSp4.
No branch-specific result or freely chosen family is an input. -/
structure Theorem11Certificate : Prop where
  allBlocks : ∀ (ell : ℕ) (F k K : Type)
      [Field F] [Finite F]
      [Field k] [Field K] [CharP k ell] [IsAlgClosed k] [CharZero K]
      [Fintype (Sp 2 F)] [Fintype (LiteralPrimitiveBlock k (Sp 2 F))]
      (prime : Nat.Prime ell)
      (iota : PrimeRegularRootEmbedding ell k K (Sp 2 F))
      (hinj : IrreducibleBrauerCharacterInjectivity iota)
      (blocks : BlockIdempotentDecomposition
        (fun b : LiteralPrimitiveBlock k (Sp 2 F) => b.1))
      (localSource : PrimitiveLocalSource iota)
      (coefficient : SpathCoefficientField ell k prime)
      (cover : EllPrimeCoverSource ell (Sp 2 F))
      (simpleEquiv : cover.S ≃* PSp 2 F),
    Odd (Nat.card F) → ell ≠ 2 → ell ∣ (Nat.card F) ^ 2 - 1 →
    simpleEquiv.toMonoidHom.comp cover.quotient = spProjection 2 F →
    Nonempty (FamilyWitness
      (primitiveFamily iota hinj blocks prime localSource) cover)

section Apply

variable (ell : ℕ) (F k K : Type)
variable [Field F] [Finite F]
variable [Field k] [Field K] [CharP k ell] [IsAlgClosed k] [CharZero K]

local instance applicationSpFintype : Fintype (Sp 2 F) := Fintype.ofFinite _

variable [Fintype (LiteralPrimitiveBlock k (Sp 2 F))]
variable (prime : Nat.Prime ell) (hell : ell ≠ 2)
variable (coverSource : OddSymplecticFullCoverSource 2 F)
variable (perfect : commutator (Sp 2 F) = ⊤)
variable (iota : PrimeRegularRootEmbedding ell k K (Sp 2 F))
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition
  (fun b : LiteralPrimitiveBlock k (Sp 2 F) => b.1))
variable (localSource : PrimitiveLocalSource iota)
variable (coefficient : SpathCoefficientField ell k prime)

include coefficient in
/-- The source receives the constructed exact cover, actual field order
and divisor, and a definitional projection square. -/
theorem full_block_condition_source_instantiated
    (hdiv : ell ∣ (Nat.card F) ^ 2 - 1) (source : Theorem11Certificate) :
    Nonempty (FamilyWitness
      (primitiveFamily iota hinj blocks prime localSource)
      (actualCover F coverSource perfect ell prime hell)) :=
  source.allBlocks ell F k K prime iota hinj blocks localSource coefficient
    (actualCover F coverSource perfect ell prime hell) (MulEquiv.refl _)
    coverSource.field_odd hell hdiv rfl

/-- A chosen inhabitant of precisely the complete canonical result. -/
def witness
    (hdiv : ell ∣ (Nat.card F) ^ 2 - 1) (source : Theorem11Certificate) :
    FamilyWitness
      (primitiveFamily iota hinj blocks prime localSource)
      (actualCover F coverSource perfect ell prime hell) :=
  Classical.choice (full_block_condition_source_instantiated ell F k K
    prime hell coverSource perfect iota hinj blocks localSource coefficient hdiv source)

end Apply

end ModularRep.PaperProofs.TypeCRankTwoOddSourceApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
