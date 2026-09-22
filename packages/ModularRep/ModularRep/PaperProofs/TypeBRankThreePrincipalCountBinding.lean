import ModularRep.PaperProofs.TypeBOrthogonalOmegaCarriers
import ModularRep.CharacterWeightBlockAssignment
import ModularRep.PaperProofs.TypeBCentralKernelPrincipalStability
import ModularRep.PaperProofs.TypeBCentralKernelInertia
import ModularRep.PaperProofs.TypeBWeightCoveringSource
import ModularRep.PaperProofs.TypeBExceptionalQ3Proposition416Relative
import Formalisation.C2Cancellation

/-!
# Rank-three principal counting on literal orthogonal carriers

The actor is conjugation by an element of the actual SO carrier. Its square
lies in the actual derived subgroup because the displayed index is two;
the actor itself is not assumed to have order two. Inner fixation and
specified principal-block stability give involutions on supported Brauer
characters and ordinary weight conjugacy classes.

The narrow published numerical and covering inputs retain these exact
carriers, roots, principal idempotents and local block assignments. The
existing dimension-seven covering arithmetic and finite C2 classification
then construct a correspondence. No field fixation, overgroup matching,
character triple, criterion or goodness conclusion is a source input.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalCountBinding

open ModularRep CharacterWeight
open TypeBCliffordCarriers TypeBOrthogonalOmegaCarriers
open TypeBCentralKernelBlockSource TypeBCentralKernelInertia
open TypeBCentralKernelPrincipalStability
open TypeBExceptionalQ3Proposition416Relative

variable (F : Type) [Field F] [Finite F]

abbrev H := SpecialOrthogonal 3 F
abbrev G := omegaSubgroup 3 F

local instance groupFintype (X : Type) [Group X] [Finite X] : Fintype X :=
  Fintype.ofFinite X

variable {k K : Type} [Field k] [Field K] [CharP k 2]
  [IsAlgClosed k] [CharZero K]

abbrev OmegaBrauer (root : PrimeRegularRootEmbedding 2 k K (G F))
    (b : LiteralPrimitiveBlock k (G F)) := BrauerFibre root b

abbrev SOBrauer (root : PrimeRegularRootEmbedding 2 k K (H F))
    (b : LiteralPrimitiveBlock k (H F)) := BrauerFibre root b

abbrev OmegaWeightSource := LocalBlockInductionSource
  (p := 2) (k := k) (K := K) (G := G F) (Block := LiteralPrimitiveBlock k (G F))

abbrev SOWeightSource := LocalBlockInductionSource
  (p := 2) (k := k) (K := K) (G := H F) (Block := LiteralPrimitiveBlock k (H F))

abbrev OmegaWeight (S : OmegaWeightSource (k := k) (K := K) F)
    (b : LiteralPrimitiveBlock k (G F)) := S.Fibre b

abbrev SOWeight (S : SOWeightSource (k := k) (K := K) F)
    (b : LiteralPrimitiveBlock k (H F)) := S.Fibre b

variable (S : OmegaWeightSource (k := k) (K := K) F)
  (literal : ∀ b, S.operations.ambientBlockData.blockIdempotent b = b.val)

/-- The same specified decomposition used by the ordinary weight allocation.
The displayed equality excludes a relabelled ambient catalogue. -/
def omegaDecomposition :
    letI := S.operations.ambientBlockData.fintypeBlock
    BlockIdempotentDecomposition (fun b : LiteralPrimitiveBlock k (G F) => b.val) := by
  letI := S.operations.ambientBlockData.fintypeBlock
  have values : S.operations.ambientBlockData.blockIdempotent =
      (fun b : LiteralPrimitiveBlock k (G F) => b.val) := funext literal
  rw [← values]
  exact S.operations.ambientBlockData.blocks

variable (root : PrimeRegularRootEmbedding 2 k K (G F))
  (b : LiteralPrimitiveBlock k (G F)) (hb : IsPrincipal b)
  (delta : H F) (indexTwo : (G F).index = 2)

include indexTwo in
/-- Only the coset has order two. This is derived for every SO element. -/
theorem square_mem_omega : delta * delta ∈ G F := by
  simpa only [indexTwo, pow_two] using (G F).pow_index_mem delta

def brauerStep (theta : OmegaBrauer F root b) : OmegaBrauer F root b := by
  letI := S.operations.ambientBlockData.fintypeBlock
  exact ⟨conjugationOp (G F) delta • theta.val,
    supported_principal_op_smul (omegaDecomposition F S literal) root b hb
      (conjugationOp (G F) delta) theta.val theta.property⟩

include indexTwo in
theorem brauerStep_involutive :
    Function.Involutive (brauerStep F S literal root b hb delta) := by
  intro theta
  apply Subtype.ext
  change conjugationOp (G F) delta •
    (conjugationOp (G F) delta • theta.val) = theta.val
  rw [← mul_smul, ← map_mul]
  exact G_le_T (G F) root theta.val (square_mem_omega F delta indexTwo)

def brauerPermutation : Equiv.Perm (OmegaBrauer F root b) where
  toFun := brauerStep F S literal root b hb delta
  invFun := brauerStep F S literal root b hb delta
  left_inv := brauerStep_involutive F S literal root b hb delta indexTwo
  right_inv := brauerStep_involutive F S literal root b hb delta indexTwo

@[simp] theorem brauerPermutation_val (theta : OmegaBrauer F root b) :
    (brauerPermutation F S literal root b hb delta indexTwo theta).val =
      conjugationOp (G F) delta • theta.val := rfl

def weightStep (w : OmegaWeight F S b) : OmegaWeight F S b := by
  letI := S.operations.ambientBlockData.fintypeBlock
  refine ⟨conjugationOp (G F) delta • w.val, ?_⟩
  change S.weightBlock (conjugationOp (G F) delta • w.val) = b
  have hw : S.weightBlock w.val = b := w.property
  exact (S.weightBlock_transport (conjugationOp (G F) delta) w.val).trans
    ((congrArg (fun c : LiteralPrimitiveBlock k (G F) =>
      conjugationOp (G F) delta • c) hw).trans
      (principal_op_smul_eq (omegaDecomposition F S literal) b hb _))

/-- Actual inner conjugation fixes the quotient of ordinary raw weights.
This is a quotient deduction, not a source fact about a permutation. -/
theorem inner_fixes_weightClass (g : G F)
    (w : CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := G F)) :
    conjugationOp (G F) (g : H F) • w = w := by
  refine Quotient.inductionOn w ?_
  intro W
  change (Quotient.mk'' (conjugationOp (G F) (g : H F) • W) :
    CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := G F)) = Quotient.mk'' W
  rw [iso_action_inner]
  exact Quotient.sound ⟨g, rfl⟩

include indexTwo in
theorem weightStep_involutive :
    Function.Involutive (weightStep F S literal b hb delta) := by
  intro w
  apply Subtype.ext
  change conjugationOp (G F) delta •
    (conjugationOp (G F) delta • w.val) = w.val
  rw [← mul_smul, ← map_mul]
  exact inner_fixes_weightClass F
    ⟨delta * delta, square_mem_omega F delta indexTwo⟩ w.val

def weightPermutation : Equiv.Perm (OmegaWeight F S b) where
  toFun := weightStep F S literal b hb delta
  invFun := weightStep F S literal b hb delta
  left_inv := weightStep_involutive F S literal b hb delta indexTwo
  right_inv := weightStep_involutive F S literal b hb delta indexTwo

@[simp] theorem weightPermutation_val (w : OmegaWeight F S b) :
    (weightPermutation F S literal b hb delta indexTwo w).val =
      conjugationOp (G F) delta • w.val := rfl

section SourceCounts

variable {r f : ℕ} [CharP F r]
  (parameters : OddFieldParameters F r f) (notThree : Nat.card F ≠ 3)
  (outside : delta ∉ G F)
  (SH : SOWeightSource (k := k) (K := K) F)
  (literalH : ∀ c, SH.operations.ambientBlockData.blockIdempotent c = c.val)
  (rootH : PrimeRegularRootEmbedding 2 k K (H F))
  (bH : LiteralPrimitiveBlock k (H F)) (hbH : IsPrincipal bH)
  [Fintype (OmegaBrauer F root b)] [DecidableEq (OmegaBrauer F root b)]
  [Fintype (SOBrauer F rootH bH)]
  [Fintype (OmegaWeight F S b)] [DecidableEq (OmegaWeight F S b)]
  [Fintype (SOWeight F SH bH)] [DecidableEq (SOWeight F SH bH)]

/-- E2/U: the fixed dimension-seven principal numerical specializations.
The source-model, discriminant-normalization, root and specified-block
realizations are obligations of an inhabitant. Chaneb's union of unipotent
blocks must not silently be replaced by the principal primitive block.
The separate SO weight number uses the classification, not an assumed
Brauer-to-weight cardinality equality or correspondence. -/
structure PublishedCounts
    (parameters : OddFieldParameters F r f) (notThree : Nat.card F ≠ 3)
    (hb : IsPrincipal b) (hbH : IsPrincipal bH)
    (literal : ∀ c, S.operations.ambientBlockData.blockIdempotent c = c.val)
    (literalH : ∀ c, SH.operations.ambientBlockData.blockIdempotent c = c.val) : Prop where
  omegaBrauer_card : Fintype.card (OmegaBrauer F root b) = 12
  soBrauer_card : Fintype.card (SOBrauer F rootH bH) = 10
  soWeight_card : Fintype.card (SOWeight F SH bH) = 10

/-- E1/U: principal modular Clifford orbit counting on the literal index-two
inclusion and its nontrivial coset. The number on the left is the actual
involution's singleton-plus-two-cycle orbit count. Its constituent-level
realization remains explicit for the later SAME-map overgroup/J join.
No action, fixed-point count or correspondence is supplied. -/
structure PrincipalCliffordOrbitCount
    (parameters : OddFieldParameters F r f) (notThree : Nat.card F ≠ 3)
    (outside : delta ∉ G F) (hbH : IsPrincipal bH)
    (literalH : ∀ c, SH.operations.ambientBlockData.blockIdempotent c = c.val) : Prop where
  orbit_count :
    Fintype.card (Function.fixedPoints
      (brauerPermutation F S literal root b hb delta indexTwo)) +
      (brauerPermutation F S literal root b hb delta indexTwo).cycleType.card =
        Fintype.card (SOBrauer F rootH bH)

/-- The exact covering relation uses the existing intermediate quotient,
defect block, DGN character and ordinary constituent occurrence. -/
abbrev WeightCoveringModel :=
  TypeBWeightCoveringSource.DGNSource (ell := 2) (K := K) (k := k) (G F)

/-- E2/U: the dimension-seven principal weight covering classification,
with the actor fixed to actual SO conjugation. Involutivity and the final
12/8 signature are not fields. `covers_iff` prevents a free relabelling of
the covering map independently of the literal local-character relation. -/
structure PublishedWeightCovering
    (parameters : OddFieldParameters F r f) (notThree : Nat.card F ≠ 3)
    (outside : delta ∉ G F) (hbH : IsPrincipal bH)
    (literalH : ∀ c, SH.operations.ambientBlockData.blockIdempotent c = c.val)
    (dgn : WeightCoveringModel (k := k) (K := K) F) where
  splits : SOWeight F SH bH → Prop
  splitsDecidable : DecidablePred splits
  splittingParametrisation :
    {w : SOWeight F SH bH // splits w} ≃ SplittingParameterIndex
  cover : OmegaWeight F S b → SOWeight F SH bH
  covers_iff : ∀ (h : SOWeight F SH bH) (w : OmegaWeight F S b),
    TypeBWeightCoveringSource.CoversClass (G F) dgn h.val w.val ↔ cover w = h
  cover_surjective : Function.Surjective cover
  cover_action : ∀ w,
    cover (weightPermutation F S literal b hb delta indexTwo w) = cover w
  fibre_card : ∀ w,
    Fintype.card {v : OmegaWeight F S b // cover v = w} = if splits w then 2 else 1
  split_weights_are_moved : ∀ w,
    splits (cover w) → weightPermutation F S literal b hb delta indexTwo w ≠ w

variable
  (counts : PublishedCounts F S root b SH rootH bH parameters notThree hb hbH literal literalH)
  (clifford : PrincipalCliffordOrbitCount F S literal root b hb delta indexTwo
    SH rootH bH parameters notThree outside hbH literalH)
  (dgn : WeightCoveringModel (k := k) (K := K) F)
  (covering : PublishedWeightCovering F S literal b hb delta indexTwo SH bH
    parameters notThree outside hbH literalH dgn)

include counts clifford in
theorem principalBrauer_action_signature :
    (Fintype.card (OmegaBrauer F root b),
      Fintype.card (Function.fixedPoints
        (brauerPermutation F S literal root b hb delta indexTwo))) = (12, 8) := by
  have total := Formalisation.C2Cancellation.card_eq_fixed_add_twice_cycleCount
    (brauerPermutation F S literal root b hb delta indexTwo)
    (brauerStep_involutive F S literal root b hb delta indexTwo)
  have orbitCount := clifford.orbit_count
  have htotal := counts.omegaBrauer_card
  have horbits := counts.soBrauer_card
  exact Prod.ext htotal (by omega)

/-- Reuse of the already checked dimension-seven covering arithmetic.
Although its original consumer was q=3, its theorem has no field parameter
and is applied here to the displayed nonexceptional actual carriers. -/
def coveringInput : PrincipalWeightCoveringInput (SOWeight F SH bH) (OmegaWeight F S b) where
  splits := covering.splits
  splitsDecidable := covering.splitsDecidable
  splittingParametrisation := covering.splittingParametrisation
  cover := covering.cover
  cover_surjective := covering.cover_surjective
  weightAction := weightPermutation F S literal b hb delta indexTwo
  weightAction_involutive := weightStep_involutive F S literal b hb delta indexTwo
  cover_action := covering.cover_action
  fibre_card := covering.fibre_card
  split_weights_are_moved := covering.split_weights_are_moved
  hWeight_card := counts.soWeight_card

include counts covering in
theorem principalWeight_action_signature :
    (Fintype.card (OmegaWeight F S b),
      Fintype.card (Function.fixedPoints
        (weightPermutation F S literal b hb delta indexTwo))) = (12, 8) :=
  (coveringInput F S literal root b hb delta indexTwo parameters notThree outside
    SH literalH rootH bH hbH counts dgn covering).principalWeight_action_signature

include counts clifford covering in
/-- The actual supported principal Brauer fibre and specified principal
weight fibre admit an equivariant equivalence for the nontrivial SO coset.
All source premises above are numerical, constituent-count or covering
facts; none supplies a character-to-weight matching. -/
theorem principalOmega_equivariantEquiv :
    ∃ equivalence : OmegaBrauer F root b ≃ OmegaWeight F S b,
      ∀ theta,
        equivalence (brauerPermutation F S literal root b hb delta indexTwo theta) =
          weightPermutation F S literal b hb delta indexTwo (equivalence theta) := by
  have brauer := principalBrauer_action_signature F S literal root b hb delta indexTwo
    parameters notThree outside SH literalH rootH bH hbH counts clifford
  have weight := principalWeight_action_signature F S literal root b hb delta indexTwo
    parameters notThree outside SH literalH rootH bH hbH counts dgn covering
  exact Formalisation.C2Cancellation.exists_equivariantEquiv_of_card_eq_of_fixed_card_eq
    (brauerPermutation F S literal root b hb delta indexTwo)
    (weightPermutation F S literal b hb delta indexTwo)
    (brauerStep_involutive F S literal root b hb delta indexTwo)
    (weightStep_involutive F S literal b hb delta indexTwo)
    ((congrArg Prod.fst brauer).trans (congrArg Prod.fst weight).symm)
    ((congrArg Prod.snd brauer).trans (congrArg Prod.snd weight).symm)

end SourceCounts

end ModularRep.PaperProofs.TypeBRankThreePrincipalCountBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
