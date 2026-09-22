import ModularRep.LinearBlockStabilizer
import ModularRep.PaperProofs.TypeBModularLinearCharacterLift

/-!
# Ordinary and Brauer forms of the linear-block-stabiliser bound

The pointwise root lift already constructed in
`TypeBModularLinearCharacterLift` is valid for every finite group, despite
its historical namespace. Its range is exactly the ordinary quotient
characters of prime-to-`p` order. This file uses that same equivalence to
identify the two block actions, and proves the ordinary factorisation and
bound. No new reduction or character-correspondence premise is introduced.
-/

noncomputable section

namespace ModularRep.LinearBlockStabilizer

open PaperProofs.TypeBModularLinearCharacterLift

universe u

variable {p : ℕ} {k K G : Type u}
  [Field k] [Field K] [Group G] [Finite G]
  [CharP k p] [IsAlgClosed k] [CharZero K]
  (iota : PrimeRegularRootEmbedding p k K G)
  (N : Subgroup G) [N.Normal]

/-- All ordinary linear quotient characters of prime-to-`p` order, using
the already constructed root-lift range as a subgroup. -/
abbrev OrdinaryQuotientCharacters := (quotientLift iota N).range

theorem ordinaryQuotientCharacters_mem_iff (lambda : G →* Kˣ) :
    lambda ∈ OrdinaryQuotientCharacters iota N ↔
      N ≤ lambda.ker ∧ p.Coprime (orderOf lambda) :=
  mem_quotientLift_range_iff iota N lambda

/-- Reduction is the inverse of the fixed, pointwise root lift. -/
def ordinaryToBrauerQuotient :
    OrdinaryQuotientCharacters iota N ≃* linearCharactersTrivialOn (k := k) N :=
  (quotientLiftRangeEquiv iota N).symm

/-- The ordinary tensor action is the Brauer tensor action transported
through the fixed root reduction. Its specified interpretation is supplied
by the tensor-support dictionary and `reduction_commutes_with_tensor`
below, under the explicitly stated modular-system compatibility. -/
@[instance_reducible]
def ordinaryBlockAction
    [MulAction (linearCharactersTrivialOn (k := k) N) (LiteralPrimitiveBlock k G)] :
    MulAction (OrdinaryQuotientCharacters iota N) (LiteralPrimitiveBlock k G) :=
  MulAction.compHom _ (ordinaryToBrauerQuotient iota N).toMonoidHom

section Actions

variable [MulAction (linearCharactersTrivialOn (k := k) N) (LiteralPrimitiveBlock k G)]

/-- The ordinary and modular block stabilisers are actually equivalent. -/
def reductionStabilizerEquiv (b : LiteralPrimitiveBlock k G) :
    letI := ordinaryBlockAction iota N
    MulAction.stabilizer (OrdinaryQuotientCharacters iota N) b ≃*
      MulAction.stabilizer (linearCharactersTrivialOn (k := k) N) b := by
  letI := ordinaryBlockAction iota N
  refine
    { toFun := fun c => ⟨ordinaryToBrauerQuotient iota N c.1, c.2⟩
      invFun := fun c => ⟨(ordinaryToBrauerQuotient iota N).symm c.1, ?_⟩
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_ }
  · change (ordinaryToBrauerQuotient iota N)
      ((ordinaryToBrauerQuotient iota N).symm c.1) • b = b
    rw [MulEquiv.apply_symm_apply]
    exact c.2
  · intro c
    apply Subtype.ext
    exact (ordinaryToBrauerQuotient iota N).symm_apply_apply c.1
  · intro c
    apply Subtype.ext
    exact (ordinaryToBrauerQuotient iota N).apply_symm_apply c.1
  · intro c d
    apply Subtype.ext
    exact map_mul (ordinaryToBrauerQuotient iota N) c.1 d.1

/-- Ordinary prime-to-`p` quotient characters stabilising the block are
trivial on the centre. The regular part follows from the shared modular
sector; the primary part follows from the ordinary character's order. -/
theorem ordinary_stabilizer_center_le_ker
    (source : SimpleBlockTensorSource
      (linearCharactersTrivialOn (k := k) N).subtype)
    (b : LiteralPrimitiveBlock k G) :
    letI := ordinaryBlockAction iota N
    ∀ c : MulAction.stabilizer (OrdinaryQuotientCharacters iota N) b,
      Subgroup.center G ≤ c.1.1.ker := by
  let := ordinaryBlockAction iota N
  intro c
  let d := reductionStabilizerEquiv iota N b c
  have hreg := stabilizer_trivial_on_central_regular iota.prime
    (linearCharactersTrivialOn (k := k) N).subtype source b d
  apply center_le_ker_of_regular_and_primary iota.prime c.1.1
  · intro g hg
    change c.1.1 g = 1
    have hlift := liftCharacter_eq_one iota d.1.1 g (hreg hg)
    have hsame : liftCharacter iota d.1.1 = c.1.1 :=
      quotientLiftRangeEquiv_symm_apply iota N c.1
    simpa only [hsame] using hlift
  · intro g n hn
    exact primeTo_character_trivial_on_p_element c.1.1
      (ordinaryRange_order_coprime iota N c.1) hn

/-- Ordinary form of the general lemma, with a concrete factor character
for each element of the block stabiliser and the index bound. -/
theorem ordinary_block_stabilizer_bound
    (source : SimpleBlockTensorSource
      (linearCharactersTrivialOn (k := k) N).subtype)
    (b : LiteralPrimitiveBlock k G) :
    letI := ordinaryBlockAction iota N
    (∀ c : MulAction.stabilizer (OrdinaryQuotientCharacters iota N) b,
      ∃ lambdaQ : G ⧸ (N ⊔ Subgroup.center G) →* Kˣ,
        lambdaQ.comp (QuotientGroup.mk' _) = c.1.1) ∧
    Nat.card (MulAction.stabilizer (OrdinaryQuotientCharacters iota N) b) ≤
      Nat.card (G ⧸ (N ⊔ Subgroup.center G)) := by
  let := ordinaryBlockAction iota N
  have hZ := ordinary_stabilizer_center_le_ker iota N source b
  have hN (c : MulAction.stabilizer (OrdinaryQuotientCharacters iota N) b) :
      N ≤ c.1.1.ker := (ordinaryQuotientCharacters_mem_iff iota N c.1.1).mp c.1.2 |>.1
  constructor
  · intro c
    exact ⟨descendCenterQuotient N c.1.1 (hN c) (hZ c), rfl⟩
  · exact card_le_center_quotient N (fun c => c.1.1)
      (fun _ _ h => Subtype.ext (Subtype.ext h)) hN hZ

include iota in
/-- Brauer form for the full modular quotient character group. The
existing quotient equivalence identifies it with characters of `G/N`. -/
theorem brauer_quotient_block_stabilizer_bound
    (source : SimpleBlockTensorSource
      (linearCharactersTrivialOn (k := k) N).subtype)
    (b : LiteralPrimitiveBlock k G) :
    (∀ c : MulAction.stabilizer (linearCharactersTrivialOn (k := k) N) b,
      ∃ lambdaQ : G ⧸ (N ⊔ Subgroup.center G) →* kˣ,
        lambdaQ.comp (QuotientGroup.mk' _) = c.1.1) ∧
    Nat.card (MulAction.stabilizer (linearCharactersTrivialOn (k := k) N) b) ≤
      Nat.card (G ⧸ (N ⊔ Subgroup.center G)) :=
  modular_block_stabilizer_bound iota.prime N
    (linearCharactersTrivialOn (k := k) N).subtype Subtype.coe_injective
    (fun c => c.2) source b

end Actions

section Decomposition

open ExactGrothendieckGroup FDRepSimpleClassKZero

variable {O : Type u} [CommRing O] [IsDomain O] [Algebra O K]

omit [N.Normal] in
/-- The same constructed ordinary/Brauer identification commutes with
tensoring under the exact decomposition map. The only premises here are
the existing modular-system character square and Brauer tensor formula. -/
theorem reduction_commutes_with_tensor
    (Msys : ModularSystem p K O k)
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (productFormula : BrauerLinearTensorProductFormula iota)
    (lambda : linearCharactersTrivialOn (k := k) N) (x : FDRepKZero K G) :
    decompositionMapOfStableReduction Msys iota hcompat
        (linearCharacterTwistKZero (quotientLift iota N lambda) x) =
      linearCharacterTwistKZero lambda.1
        (decompositionMapOfStableReduction Msys iota hcompat x) :=
  decompositionMapOfStableReduction_linearCharacterTwist Msys iota hcompat
    productFormula _ _ (liftCharacter_regularCompatible iota lambda.1) x

end Decomposition

end ModularRep.LinearBlockStabilizer


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
