import ModularRep.PaperProofs.TypeBRankThreePrincipalBrauerOrbitBinding
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# The rank-three principal orbit count from the actual quotient action

The actual SO action on the specified principal Omega Brauer fibre descends
to the literal quotient SO/Omega, by the already proved inner fixation.
The quotient action has the same orbit classes, with identical character
representatives. Burnside's formula for this order-two quotient and the
checked involution cycle identity identify its orbit cardinal with fixed
points plus nontrivial cycles. The existing principal constituent orbit
equivalence then gives the old numerical target as a deduction.

No orbit count, numerical character count, matching map, weight bijection
or inductive-condition assertion is introduced as a source input.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalOrbitCount

open ModularRep TypeBCentralKernelBlockSource
open TypeBRankThreePrincipalCountBinding TypeBRankThreePrincipalOrbitBinding
open TypeBRankThreePrincipalBrauerOrbitBinding TypeBGreenPrincipalConstituentSource

variable (F : Type) [Field F] [Finite F]

/-- The actual quotient of the fixed rank-three SO by its derived subgroup. -/
abbrev OrthogonalQuotient := (H F) ⧸ G F

local instance groupFintype (X : Type) [Group X] [Finite X] : Fintype X :=
  Fintype.ofFinite X

theorem quotient_card (indexTwo : (G F).index = 2) :
    Fintype.card (OrthogonalQuotient F) = 2 := by
  simpa only [Nat.card_eq_fintype_card] using (G F).index_eq_card.symm.trans indexTwo

theorem quotient_delta_ne_one (delta : H F) (outside : delta ∉ G F) :
    QuotientGroup.mk' (G F) delta ≠ 1 :=
  fun equal => outside ((QuotientGroup.eq_one_iff delta).mp equal)

variable {k K : Type} [Field k] [Field K] [CharP k 2]
  [IsAlgClosed k] [CharZero K]
  (S : OmegaWeightSource (k := k) (K := K) F)
  (literal : ∀ c, S.operations.ambientBlockData.blockIdempotent c = c.val)
  (root : PrimeRegularRootEmbedding 2 k K (G F))
  (b : LiteralPrimitiveBlock k (G F)) (hb : IsPrincipal b)

/-- The original action factors through the displayed normal subgroup
because every actual inner actor fixes the supported character itself. -/
def quotientBrauerHom : OrthogonalQuotient F →* Equiv.Perm (OmegaBrauer F root b) := by
  letI := principalBrauerAction F S literal root b hb
  refine QuotientGroup.lift (G F)
    (MulAction.toPermHom (H F) (OmegaBrauer F root b)) ?_
  intro h hh
  apply Equiv.ext
  intro theta
  change brauerStep F S literal root b hb h theta = theta
  exact brauerStep_eq_of_mem F S literal root b hb h hh theta

@[simp] theorem quotientBrauerHom_mk (h : H F) (theta : OmegaBrauer F root b) :
    quotientBrauerHom F S literal root b hb (QuotientGroup.mk' (G F) h) theta =
      brauerStep F S literal root b hb h theta := rfl

/-- The quotient actor is the actual descended homomorphism, including
the possibly trivial action on individual characters. -/
def quotientBrauerAction : MulAction (OrthogonalQuotient F) (OmegaBrauer F root b) :=
  MulAction.compHom (OmegaBrauer F root b) (quotientBrauerHom F S literal root b hb)

def quotientBrauerOrbitRel : Setoid (OmegaBrauer F root b) := by
  letI := quotientBrauerAction F S literal root b hb
  exact MulAction.orbitRel (OrthogonalQuotient F) (OmegaBrauer F root b)

abbrev QuotientBrauerOrbit := Quotient (quotientBrauerOrbitRel F S literal root b hb)

/-- Taking quotient actors changes neither the relation nor the original
character representative in any orbit. -/
theorem quotientBrauerOrbitRel_iff (theta eta : OmegaBrauer F root b) :
    quotientBrauerOrbitRel F S literal root b hb theta eta ↔
      principalBrauerOrbitRel F S literal root b hb theta eta := by
  change (∃ q : OrthogonalQuotient F,
      quotientBrauerHom F S literal root b hb q eta = theta) ↔
    (∃ h : H F, brauerStep F S literal root b hb h eta = theta)
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (G F) q
    exact ⟨h, hq⟩
  · rintro ⟨h, hh⟩
    exact ⟨QuotientGroup.mk' (G F) h, hh⟩

def quotientOrbitEquiv : QuotientBrauerOrbit F S literal root b hb ≃
    PrincipalBrauerOrbit F S literal root b hb :=
  Quotient.congr (Equiv.refl (OmegaBrauer F root b))
    (quotientBrauerOrbitRel_iff F S literal root b hb)

@[simp] theorem quotientOrbitEquiv_mk (theta : OmegaBrauer F root b) :
    quotientOrbitEquiv F S literal root b hb (Quotient.mk _ theta) =
      Quotient.mk (principalBrauerOrbitRel F S literal root b hb) theta := rfl

section Counting

variable [Fintype (OmegaBrauer F root b)] [DecidableEq (OmegaBrauer F root b)]

/-- Burnside's formula specializes to the actual two quotient elements.
Only the coset of delta, not delta itself, is required to have order two. -/
theorem quotient_burnside (delta : H F) (indexTwo : (G F).index = 2)
    (outside : delta ∉ G F) :
    Fintype.card (OmegaBrauer F root b) +
        Fintype.card (Function.fixedPoints
          (brauerPermutation F S literal root b hb delta indexTwo)) =
      2 * Nat.card (QuotientBrauerOrbit F S literal root b hb) := by
  classical
  letI := quotientBrauerAction F S literal root b hb
  letI : Fintype (Quotient (MulAction.orbitRel (OrthogonalQuotient F)
      (OmegaBrauer F root b))) := Fintype.ofFinite _
  let d : OrthogonalQuotient F := QuotientGroup.mk' (G F) delta
  have hd : d ≠ 1 := quotient_delta_ne_one F delta outside
  have qcard : Nat.card (OrthogonalQuotient F) = 2 :=
    (G F).index_eq_card.symm.trans indexTwo
  obtain ⟨other, _, unique⟩ := (Nat.card_eq_two_iff' (1 : OrthogonalQuotient F)).mp qcard
  have all : ∀ q : OrthogonalQuotient F, q = 1 ∨ q = d := by
    intro q
    by_cases hq : q = 1
    · exact Or.inl hq
    · exact Or.inr ((unique q hq).trans (unique d hd).symm)
  have univPair : (Finset.univ : Finset (OrthogonalQuotient F)) = {1, d} := by
    ext q
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact all q
  have fixedOne :
      Fintype.card (MulAction.fixedBy (OmegaBrauer F root b)
        (1 : OrthogonalQuotient F)) = Fintype.card (OmegaBrauer F root b) := by
    exact Fintype.card_congr
      ((Equiv.setCongr (MulAction.fixedBy_one_eq_univ
        (M := OrthogonalQuotient F) (α := OmegaBrauer F root b))).trans
        (Equiv.Set.univ (OmegaBrauer F root b)))
  have fixedDeltaSet : MulAction.fixedBy (OmegaBrauer F root b) d =
      Function.fixedPoints (brauerPermutation F S literal root b hb delta indexTwo) := by
    ext theta
    change quotientBrauerHom F S literal root b hb d theta = theta ↔
      brauerPermutation F S literal root b hb delta indexTwo theta = theta
    rfl
  have fixedDelta := Fintype.card_congr (Equiv.setCongr fixedDeltaSet)
  have burnside := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
    (OrthogonalQuotient F) (OmegaBrauer F root b)
  rw [univPair, Finset.sum_insert (by simpa only [Finset.mem_singleton] using Ne.symm hd),
    Finset.sum_singleton, fixedOne, fixedDelta] at burnside
  have quotientCardCurrent : Fintype.card (OrthogonalQuotient F) = 2 :=
    (show Nat.card (OrthogonalQuotient F) = Fintype.card (OrthogonalQuotient F) from
      Nat.card_eq_fintype_card).symm.trans qcard
  have burnsideTwo := burnside.trans
    (congrArg (fun m : ℕ => Fintype.card
      (Quotient (MulAction.orbitRel (OrthogonalQuotient F) (OmegaBrauer F root b))) * m)
      quotientCardCurrent)
  change Fintype.card (OmegaBrauer F root b) +
      Fintype.card (Function.fixedPoints
        (brauerPermutation F S literal root b hb delta indexTwo)) =
    2 * Nat.card (Quotient (MulAction.orbitRel (OrthogonalQuotient F)
      (OmegaBrauer F root b)))
  simpa only [Nat.card_eq_fintype_card, Nat.mul_comm] using burnsideTwo

/-- This is the actual quotient cardinal, identified with the old
singleton-plus-two-cycle expression by the checked involution identity. -/
theorem quotient_orbit_count (delta : H F) (indexTwo : (G F).index = 2)
    (outside : delta ∉ G F) :
    Fintype.card (Function.fixedPoints
        (brauerPermutation F S literal root b hb delta indexTwo)) +
      (brauerPermutation F S literal root b hb delta indexTwo).cycleType.card =
        Nat.card (QuotientBrauerOrbit F S literal root b hb) := by
  have burnside := quotient_burnside F S literal root b hb delta indexTwo outside
  have cycles := Formalisation.C2Cancellation.card_eq_fixed_add_twice_cycleCount
    (brauerPermutation F S literal root b hb delta indexTwo)
    (brauerStep_involutive F S literal root b hb delta indexTwo)
  omega

variable (delta : H F) (indexTwo : (G F).index = 2) (outside : delta ∉ G F)
  (rootH : PrimeRegularRootEmbedding 2 k K (H F))
  (bH : LiteralPrimitiveBlock k (H F)) (hbH : IsPrincipal bH)
  (roots : RootAgreement (G F) rootH root)
  (fieldScope : SpathCoefficientField 2 k rootH.prime)
  (green : Green811Source (G F) rootH root roots fieldScope
    (quotient_isTwoGroup (G F) indexTwo))
  (principalLift : PrincipalLiftSource (G F) rootH root roots fieldScope
    (quotient_isTwoGroup (G F) indexTwo))
  (clifford : Clifford85_87Source (G F) rootH root roots fieldScope)
  (principalRestriction : PrincipalRestrictionSource (G F) rootH root roots fieldScope)
  [Fintype (SOBrauer F rootH bH)]

include outside hbH roots fieldScope green principalLift clifford principalRestriction in
/-- The old principal Clifford orbit-count equation is now a deduction
from the same literal constituent orbit equivalence and quotient action. -/
theorem principal_orbit_count :
    Fintype.card (Function.fixedPoints
        (brauerPermutation F S literal root b hb delta indexTwo)) +
      (brauerPermutation F S literal root b hb delta indexTwo).cycleType.card =
        Fintype.card (SOBrauer F rootH bH) := by
  calc
    Fintype.card (Function.fixedPoints
        (brauerPermutation F S literal root b hb delta indexTwo)) +
        (brauerPermutation F S literal root b hb delta indexTwo).cycleType.card =
      Nat.card (QuotientBrauerOrbit F S literal root b hb) :=
        quotient_orbit_count F S literal root b hb delta indexTwo outside
    _ = Nat.card (SOBrauer F rootH bH) :=
      Nat.card_congr ((quotientOrbitEquiv F S literal root b hb).trans
        (principalOrbitEquiv F S literal root b hb rootH bH hbH roots fieldScope indexTwo
          green principalLift clifford principalRestriction))
    _ = Fintype.card (SOBrauer F rootH bH) := Nat.card_eq_fintype_card

end Counting

end ModularRep.PaperProofs.TypeBRankThreePrincipalOrbitCount


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
