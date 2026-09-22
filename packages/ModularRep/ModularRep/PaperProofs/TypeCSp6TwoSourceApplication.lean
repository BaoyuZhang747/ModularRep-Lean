import ModularRep.PaperProofs.TypeCRankTwoOddSourceApplication
import ModularRep.PaperProofs.TypeBCyclicDefectSource
import ModularRep.Sp6DoubleCoverOrder

/-!
# The actual exceptional odd-prime cover of Sp6(2)

The carrier U is fixed by its ACTUAL full universal central projection to
literal PSp6(ZMod 2). Its centre has order two. It is not the centreless
matrix group used in the defining-prime lane or in the a >= 2 own-cover
lane. The E1 packet consists exclusively of actual group facts.

K constructs the prime-to-ell cover for every odd ell, exhausts the odd
prime divisors as 3,5,7, and proves subgroup cyclicity at 5 and 7. The
published Schaeffer Fry Theorem 5.5 is used at 3; the existing GENERAL
cyclic-defect theorem handles 5 and 7. All branches have the SAME fixed
complete primitive family and actual cover, with no free target predicate.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeCSp6TwoSourceApplication

open ModularRep FDRepSimpleClassKZero
open OddTwoConformalProjectiveRealisation (PSp)
open EvenFieldFLZSourceConditions EvenFieldFLZ318FixedTheoremGate
open TypeBFixedRootDefinitionFamily TypeBFullBlockCondition
open ManuscriptVerification.Sp6DoubleCoverOrder

/-- The simple quotient is literally the projective matrix group over F2. -/
abbrev SimpleGroup := PSp 3 (ZMod 2)

local instance simpleGroupFintype : Fintype SimpleGroup := Fintype.ofFinite _

/-- Standard E1 group data for the actual double cover. The universal
property pins U to its projection; an unrelated group of the same order
cannot meet this source merely by supplying its cardinality. -/
structure FullCoverSource (U : Type) [Group U] [Finite U]
    (projection : U →* SimpleGroup) : Prop where
  fullCover : IsUniversalCentralExtension projection
  perfect : commutator U = ⊤
  kernel_eq_center : projection.ker = Subgroup.center U
  center_card : Nat.card (Subgroup.center U) = 2
  simple : IsSimpleGroup SimpleGroup
  nonabelian : ¬ IsMulCommutative SimpleGroup
  order : Nat.card U = sp6DoubleCoverOrder

section Cover

variable (U : Type) [Group U] [Fintype U]
variable (projection : U →* SimpleGroup) (facts : FullCoverSource U projection)

include facts in
/-- The actual universal map gives lifts; perfectness of the extension's
TOTAL group makes each lift surjective by the existing commutator lemma. -/
theorem projection_maximal
    (D : Type) [Group D] [Fintype D] (f : D →* SimpleGroup)
    (hsurjective : Function.Surjective f)
    (hcentral : f.ker ≤ Subgroup.center D)
    (hperfect : commutator D = ⊤) :
    ∃ lift : U →* D, Function.Surjective lift ∧ f.comp lift = projection := by
  obtain ⟨lift, hlift, _⟩ := facts.fullCover.2 D f ⟨hsurjective, hcentral⟩
  have hcomp : Function.Surjective (f.comp lift) := by
    rw [hlift]
    exact facts.fullCover.1.1
  exact ⟨lift, TypeCRankTwoOddSourceApplication.lift_surjective_of_central_comp
    f lift hcomp hcentral hperfect, hlift⟩

include facts in
theorem center_primeTo (ell : ℕ) (prime : Nat.Prime ell) (hell : ell ≠ 2) :
    ¬ ell ∣ Nat.card (Subgroup.center U) := by
  rw [facts.center_card]
  intro h
  rcases (Nat.dvd_prime Nat.prime_two).mp h with h | h
  · exact prime.ne_one h
  · exact hell h

/-- The computed odd-prime cover has exactly the supplied full-cover
carrier U and its literal projection to PSp6(F2). -/
def actualCover (ell : ℕ) (prime : Nat.Prime ell) (hell : ell ≠ 2) :
    EllPrimeCoverSource ell U where
  S := SimpleGroup
  quotient := projection
  quotient_surjective := facts.fullCover.1.1
  quotient_kernel := facts.kernel_eq_center
  perfect := facts.perfect
  simple := facts.simple
  nonabelian := facts.nonabelian
  centerPrimeTo := center_primeTo U projection facts ell prime hell
  maximal := by
    intro D _ _ f hsurjective hcentral hperfect _
    exact projection_maximal U projection facts D f hsurjective hcentral hperfect

@[simp] theorem actualCover_quotient (ell : ℕ) (prime : Nat.Prime ell) (hell : ell ≠ 2) :
    (actualCover U projection facts ell prime hell).quotient = projection := rfl

include facts in
/-- The ORIGINAL simple-order divisor transfers along the SAME actual
surjective map, then the accepted order calculation exhausts the cases. -/
theorem odd_prime_cases (ell : ℕ) (prime : Nat.Prime ell) (hell : ell ≠ 2)
    (divides_simple_order : ell ∣ Nat.card SimpleGroup) :
    ell = 3 ∨ ell = 5 ∨ ell = 7 := by
  have hcover : ell ∣ Nat.card U := divides_simple_order.trans
    (Subgroup.card_dvd_of_surjective projection facts.fullCover.1.1)
  rw [facts.order] at hcover
  rcases prime_dvd_sp6DoubleCoverOrder prime hcover with h | h | h | h
  · exact (hell h).elim
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

include facts in
/-- Cyclicity at 5 or 7 concerns the actual cover's OWN subgroups. The
order is bound to that cover by the same structural packet. -/
theorem every_five_seven_subgroup_cyclic (ell : ℕ) (hcase : ell = 5 ∨ ell = 7)
    (D : Subgroup U) (hD : IsPGroup ell D) : IsCyclic D := by
  rcases hcase with rfl | rfl
  · exact isCyclic_five_subgroup facts.order D hD
  · exact isCyclic_seven_subgroup facts.order D hD

end Cover

/-- Uniform E2 Schaeffer Fry (2014), Theorem 5.5, restricted to the actual
Sp6(2) simple quotient. The theorem's a=1 proof explicitly uses the double
cover. All root and specified local data have their authenticated standard
modular-system meanings. This is not an assertion for an arbitrary family.

The cover and projection square are explicit: both the group source and
the complete target concern the SAME U and the SAME actual map. No
certificate inhabitant is declared. The later consumer uses this at 3. -/
structure Theorem55Sp6TwoCertificate : Prop where
  allBlocks : ∀ (ell : ℕ) (U k K : Type)
      [Group U] [Fintype U]
      [Field k] [Field K] [CharP k ell] [IsAlgClosed k] [CharZero K]
      [Fintype (LiteralPrimitiveBlock k U)]
      (prime : Nat.Prime ell)
      (projection : U →* SimpleGroup) (facts : FullCoverSource U projection)
      (iota : PrimeRegularRootEmbedding ell k K U)
      (hinj : IrreducibleBrauerCharacterInjectivity iota)
      (blocks : BlockIdempotentDecomposition (fun b : LiteralPrimitiveBlock k U => b.1))
      (localSource : PrimitiveLocalSource iota)
      (coefficient : SpathCoefficientField ell k prime)
      (cover : EllPrimeCoverSource ell U)
      (simpleEquiv : cover.S ≃* SimpleGroup),
    ell ≠ 2 → simpleEquiv.toMonoidHom.comp cover.quotient = projection →
    Nonempty (FamilyWitness (primitiveFamily iota hinj blocks prime localSource) cover)

section Apply

variable (ell : ℕ) (U k K : Type)
variable [Group U] [Fintype U]
variable [Field k] [Field K] [CharP k ell] [IsAlgClosed k] [CharZero K]
variable [Fintype (LiteralPrimitiveBlock k U)]
variable (prime : Nat.Prime ell) (hell : ell ≠ 2)
variable (projection : U →* SimpleGroup) (facts : FullCoverSource U projection)
variable (iota : PrimeRegularRootEmbedding ell k K U)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition (fun b : LiteralPrimitiveBlock k U => b.1))
variable (localSource : PrimitiveLocalSource iota)
variable (coefficient : SpathCoefficientField ell k prime)

include coefficient in
/-- The cyclic branches use only the existing GENERAL cyclic theorem
after subgroup cyclicity is proved on this actual full cover. -/
theorem cyclic_full_block_condition
    (hcase : ell = 5 ∨ ell = 7)
    (divides_simple_order : ell ∣ Nat.card SimpleGroup)
    (source : TypeBCyclicDefectSource.CyclicDefectCertificate) :
    Nonempty (FamilyWitness (primitiveFamily iota hinj blocks prime localSource)
      (actualCover U projection facts ell prime hell)) :=
  source.allBlocks prime (prime.odd_of_ne_two hell) iota hinj blocks localSource coefficient
    (actualCover U projection facts ell prime hell) divides_simple_order
    (every_five_seven_subgroup_cyclic U projection facts ell hcase)

include coefficient in
/-- Exhaust the actual odd simple-order divisors. The noncyclic 3-branch
uses the exact published theorem; 5 and 7 use the derived cyclic argument.
Both routes return precisely the same canonical complete output type. -/
theorem full_block_condition_source_instantiated
    (divides_simple_order : ell ∣ Nat.card SimpleGroup)
    (threeSource : Theorem55Sp6TwoCertificate)
    (cyclicSource : TypeBCyclicDefectSource.CyclicDefectCertificate) :
    Nonempty (FamilyWitness (primitiveFamily iota hinj blocks prime localSource)
      (actualCover U projection facts ell prime hell)) := by
  rcases odd_prime_cases U projection facts ell prime hell divides_simple_order with
    hthree | hcyclic
  · exact threeSource.allBlocks ell U k K prime projection facts iota hinj blocks
      localSource coefficient (actualCover U projection facts ell prime hell)
      (MulEquiv.refl _) hell rfl
  · exact cyclic_full_block_condition ell U k K prime hell projection facts
      iota hinj blocks localSource coefficient hcyclic divides_simple_order cyclicSource

/-- A selected inhabitant of that exact family and actual odd-prime cover. -/
def witness
    (divides_simple_order : ell ∣ Nat.card SimpleGroup)
    (threeSource : Theorem55Sp6TwoCertificate)
    (cyclicSource : TypeBCyclicDefectSource.CyclicDefectCertificate) :
    FamilyWitness (primitiveFamily iota hinj blocks prime localSource)
      (actualCover U projection facts ell prime hell) :=
  Classical.choice (full_block_condition_source_instantiated ell U k K prime hell
    projection facts iota hinj blocks localSource coefficient divides_simple_order
    threeSource cyclicSource)

end Apply

end ModularRep.PaperProofs.TypeCSp6TwoSourceApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
