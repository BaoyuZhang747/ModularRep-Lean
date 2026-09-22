import ModularRep.PaperProofs.TypeBFLZCentralizerCharacterDescent
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

/-!
# One cyclotomic coefficient model for the Type B sources

The conductor is the least common multiple of the orders of the actual
special Clifford and conformal symplectic groups. Existing sufficient-root
hypotheses construct a primitive root for this conductor and an embedding of
its rational cyclotomic field into the prescribed ordinary field. Its map
into the algebraic closure is the composite of that same embedding.

This fixes literal maps on which published character-value certificates can
be stated. It does not assert a character, Jordan, block, or reduction result.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBFLZCyclotomicModel

open TypeBCliffordCarriers TypeBConformalDualCarriers TypeBFLZLabelSource

universe u
variable (F : Type u) [Field F] (n : ℕ)

/-- The two group orders are retained separately in one conductor. -/
def conductor : ℕ :=
  Nat.lcm (Nat.card (SpecialClifford n F)) (Nat.card (CSp F n))

theorem ordinary_order_dvd : Nat.card (SpecialClifford n F) ∣ conductor F n :=
  Nat.dvd_lcm_left _ _

theorem dual_order_dvd : Nat.card (CSp F n) ∣ conductor F n :=
  Nat.dvd_lcm_right _ _

variable [Finite F] [Finite (Clifford n F)]

theorem conductor_pos : 0 < conductor F n :=
  Nat.lcm_pos Nat.card_pos Nat.card_pos

instance conductor_neZero : NeZero (conductor F n) :=
  ⟨(conductor_pos F n).ne'⟩

/-- A literal common number field, not an identification of K with C. -/
abbrev ValueField := CyclotomicField (conductor F n) ℚ

instance valueFieldCyclotomic :
    IsCyclotomicExtension {conductor F n} ℚ (ValueField F n) :=
  CyclotomicField.isCyclotomicExtension (conductor F n) ℚ

variable {F n} (K : Type u) [Field K] [CharZero K]

/-- Choosing the image of the primitive root fixes the common embedding.
This data is constructed from the existing two enough-root hypotheses below. -/
structure Choice where
  root : K
  primitive : IsPrimitiveRoot root (conductor F n)

/-- A common primitive root is constructed without equating the group orders. -/
def choiceOfRoots
    (ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F)))
    (dualRoots : HasEnoughRootsOfUnity K (Nat.card (CSp F n))) : Choice (F := F) (n := n) K := by
  letI := ordinaryRoots
  letI := dualRoots
  let a := HasEnoughRootsOfUnity.exists_primitiveRoot K (Nat.card (SpecialClifford n F))
  let b := HasEnoughRootsOfUnity.exists_primitiveRoot K (Nat.card (CSp F n))
  exact ⟨_, a.choose_spec.pow_mul_pow_lcm b.choose_spec Nat.card_pos.ne' Nat.card_pos.ne'⟩

variable {K} (choice : Choice (F := F) (n := n) K)

/-- All sufficient-root guards below come from the same primitive root. -/
def Choice.commonRoots : HasEnoughRootsOfUnity K (conductor F n) where
  prim := ⟨choice.root, choice.primitive⟩
  cyc := rootsOfUnity.isCyclic K (conductor F n)

def Choice.ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F)) := by
  letI := choice.commonRoots
  exact HasEnoughRootsOfUnity.of_dvd K (ordinary_order_dvd F n)

def Choice.dualRoots : HasEnoughRootsOfUnity K (Nat.card (CSp F n)) := by
  letI := choice.commonRoots
  exact HasEnoughRootsOfUnity.of_dvd K (dual_order_dvd F n)

/-- Lagrange binds each actual centralizer to this same root choice. -/
def Choice.centralizerRoots {p : ℕ} (s : SemisimpleParameter F p n) :
    HasEnoughRootsOfUnity K (Nat.card (parameterCentralizer F p n s)) :=
  TypeBFLZCentralizerCharacterDescent.centralizerRoots choice.dualRoots s

/-- The canonical primitive generator in the fixed rational cyclotomic field. -/
def generator : ValueField F n :=
  IsCyclotomicExtension.zeta (conductor F n) ℚ (ValueField F n)

theorem generator_primitive : IsPrimitiveRoot (generator (F := F) (n := n)) (conductor F n) :=
  IsCyclotomicExtension.zeta_spec (conductor F n) ℚ (ValueField F n)

/-- The prescribed primitive-root image determines the ordinary embedding. -/
def Choice.embedding : ValueField F n →ₐ[ℚ] K :=
  ((generator_primitive (F := F) (n := n)).embeddingsEquivPrimitiveRoots K
    (Polynomial.cyclotomic.irreducible_rat (conductor_pos F n))).symm
      ⟨choice.root, (mem_primitiveRoots (conductor_pos F n)).mpr choice.primitive⟩

theorem Choice.embedding_generator :
    choice.embedding (generator (F := F) (n := n)) = choice.root := by
  exact congrArg Subtype.val
    (((generator_primitive (F := F) (n := n)).embeddingsEquivPrimitiveRoots K
      (Polynomial.cyclotomic.irreducible_rat (conductor_pos F n))).apply_symm_apply _)

theorem Choice.embedding_injective : Function.Injective choice.embedding :=
  choice.embedding.injective

/-- The closure uses the composite of the SAME ordinary-field embedding. -/
def Choice.closureEmbedding : ValueField F n →ₐ[ℚ] AlgebraicClosure K :=
  (IsScalarTower.toAlgHom ℚ K (AlgebraicClosure K)).comp choice.embedding

@[simp] theorem Choice.closureEmbedding_apply (a : ValueField F n) :
    choice.closureEmbedding a = algebraMap K (AlgebraicClosure K) (choice.embedding a) := rfl

theorem Choice.closureEmbedding_generator :
    choice.closureEmbedding (generator (F := F) (n := n)) =
      algebraMap K (AlgebraicClosure K) choice.root := by
  rw [Choice.closureEmbedding_apply, Choice.embedding_generator]

/-- Equality of published values upstairs determines their ordinary values. -/
theorem Choice.value_eq_iff (x : K) (a : ValueField F n) :
    algebraMap K (AlgebraicClosure K) x = choice.closureEmbedding a ↔
      x = choice.embedding a :=
  (algebraMap K (AlgebraicClosure K)).injective.eq_iff

end ModularRep.PaperProofs.TypeBFLZCyclotomicModel


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
