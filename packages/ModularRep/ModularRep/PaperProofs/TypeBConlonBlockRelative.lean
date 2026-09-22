import ModularRep.PaperProofs.OddConformalProposition311Relative

/-!
# The Conlon block argument in Lemma 4.2

This file checks the manuscript-specific deduction in Lemma 4.2 for either
of its block stabilisers.  It starts from a global integral basic set on the
actual function-valued set `IBr`, restricts the exact decomposition map to a
stable block, proves equivariance of that restriction from exact `K₀`
naturality, and applies the already checked Conlon--Burnside bridge.

The order bound on the normal tensor subgroup is not supplied directly.
Instead, Lean derives it from the source-shaped conclusion of the block-label
argument: the subgroup embeds in the scalar group of a field and every image
has square one.  The field projection remains explicit, while Lean identifies
its kernel as normal and constructs the quotient embedding in its cyclic
target.

No blockwise lattice equivalence, blockwise set bijection, or
`2`-hypoelementary conclusion is an input.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBConlonBlockRelative

open ModularRep.BlockFibreRestriction
open ModularRep.DecompositionBasicSetBridge
open ModularRep.FDRepSimpleClassKZero
open ModularRep.ExactGrothendieckGroup
open ModularRep.IntegralBasicSetBridge
open ModularRep.PaperProofs.ConlonBasicSet
open ModularRep.PaperProofs.OddConformalProposition311Relative

universe u

/-- If a finite type injects into the units of a field and every image has
square one, then it has at most two elements.  This is the elementary last
step in the scalar-multiplier argument of Lemma 4.2. -/
theorem natCard_le_two_of_units_square_one
    {D F : Type u} [Finite D] [Field F]
    (scalar : D → Fˣ)
    (scalar_injective : Function.Injective scalar)
    (scalar_square_one : forall d : D, scalar d ^ 2 = 1) :
    Nat.card D ≤ 2 := by
  classical
  let signCode : D → Bool := fun d => decide ((scalar d : F) = 1)
  have signCode_injective : Function.Injective signCode := by
    intro x y hxy
    apply scalar_injective
    apply Units.ext
    by_cases hx : (scalar x : F) = 1
    · by_cases hy : (scalar y : F) = 1
      · exact hx.trans hy.symm
      · have hxcode : signCode x = true := by
          simp only [signCode, decide_eq_true_eq]
          exact hx
        have hycode : signCode y = false := by
          simp only [signCode, decide_eq_false_iff_not]
          exact hy
        rw [hxcode, hycode] at hxy
        exact Bool.noConfusion hxy
    · by_cases hy : (scalar y : F) = 1
      · have hxcode : signCode x = false := by
          simp only [signCode, decide_eq_false_iff_not]
          exact hx
        have hycode : signCode y = true := by
          simp only [signCode, decide_eq_true_eq]
          exact hy
        rw [hxcode, hycode] at hxy
        exact Bool.noConfusion hxy
      · have hsx : (scalar x : F) ^ 2 = 1 := by
          simpa using congrArg Units.val (scalar_square_one x)
        have hsy : (scalar y : F) ^ 2 = 1 := by
          simpa using congrArg Units.val (scalar_square_one y)
        rcases sq_eq_one_iff.mp hsx with hxone | hxneg
        · exact (hx hxone).elim
        · rcases sq_eq_one_iff.mp hsy with hyone | hyneg
          · exact (hy hyone).elim
          · exact hxneg.trans hyneg.symm
  simpa using Nat.card_le_card_of_injective signCode signCode_injective

/-- Conjugacy of a parameter with all its scalar translates forces the
scalars to have square one when the multiplier is conjugacy invariant and a
scalar translate multiplies it by the square of that scalar.  This isolates
the manuscript deduction from the block-label theorem and the conformal
multiplier formula; neither the square-one conclusion nor the order bound is
an input. -/
theorem scalar_square_one_of_translated_conjugate
    {D F Semisimple : Type u} [Field F]
    (scalar : D → Fˣ)
    (parameter : Semisimple)
    (translate : Fˣ → Semisimple → Semisimple)
    (multiplier : Semisimple → Fˣ)
    (IsConjugate : Semisimple → Semisimple → Prop)
    (multiplier_eq_of_conjugate : forall {s t : Semisimple},
      IsConjugate s t → multiplier s = multiplier t)
    (translated_conjugate : forall d : D,
      IsConjugate parameter (translate (scalar d) parameter))
    (multiplier_translate : forall (z : Fˣ) (s : Semisimple),
      multiplier (translate z s) = z ^ 2 * multiplier s) :
    forall d : D, scalar d ^ 2 = 1 := by
  intro d
  have hmultiplier :
      multiplier parameter = scalar d ^ 2 * multiplier parameter := by
    calc
      multiplier parameter =
          multiplier (translate (scalar d) parameter) :=
        multiplier_eq_of_conjugate (translated_conjugate d)
      _ = scalar d ^ 2 * multiplier parameter :=
        multiplier_translate (scalar d) parameter
  apply mul_right_cancel (b := multiplier parameter)
  simpa using hmultiplier.symm

variable {p : Nat}
variable {G k K Basic J BlockIndex CyclicTarget ScalarField : Type u}
variable [Group G] [Finite G]
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group J] [Finite J]
variable [Group CyclicTarget] [IsCyclic CyclicTarget]
variable [Field ScalarField]
variable [Finite Basic] [MulAction J Basic]

/-- The relative form of manuscript Lemma 4.2.

The global basic set and the exact naturality of reduction are substantive
source inputs.  Lean constructs the block restriction, its integral
permutation-lattice equivalence, the order bound for the normal tensor
subgroup, the `2`-hypoelementary property of the stabiliser, and the final
equivariant bijection. -/
theorem lemma_4_3_relative
    (iota : PrimeRegularRootEmbedding p k K G)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    [MulAction J (IBr iota)]
    [Fintype BlockIndex]
    {blockIdempotent : BlockIndex → k[G]}
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (block : BlockIndex)
    {decomposition : FDRepKZero K G →+ FDRepKZero k G}
    (basicSet : RestrictedIntegralBasicSetOnIBr
      iota hinj Basic decomposition)
    (ordinaryBlock : Basic → BlockIndex)
    (hblockDiagonal : BlockDiagonalLinearEquiv ordinaryBlock
      (irreducibleBrauerCharacterBlock iota hinj blocks)
      basicSet.linearEquiv)
    (tensorFieldActions : LabelledKZeroActionData (A := J)
      basicSet.toRestrictedIntegralBasicSet)
    (reductionNatural : DecompositionNatural (A := J) decomposition
      tensorFieldActions.ordinaryAction tensorFieldActions.modularAction)
    (hOrdinaryBlockStable : forall (j : J) (x : Basic),
      ordinaryBlock x = block → ordinaryBlock (j • x) = block)
    (hBrauerBlockStable : forall (j : J) (phi : IBr iota),
      irreducibleBrauerCharacterBlock iota hinj blocks phi = block →
        irreducibleBrauerCharacterBlock iota hinj blocks (j • phi) = block)
    (fieldProjection : J →* CyclicTarget)
    (scalar : fieldProjection.ker → ScalarFieldˣ)
    (scalar_injective : Function.Injective scalar)
    {Semisimple : Type u}
    (parameter : Semisimple)
    (translate : ScalarFieldˣ → Semisimple → Semisimple)
    (multiplier : Semisimple → ScalarFieldˣ)
    (IsConjugate : Semisimple → Semisimple → Prop)
    (multiplier_eq_of_conjugate : forall {s t : Semisimple},
      IsConjugate s t → multiplier s = multiplier t)
    (translated_conjugate : forall d : fieldProjection.ker,
      IsConjugate parameter (translate (scalar d) parameter))
    (multiplier_translate : forall (z : ScalarFieldˣ) (s : Semisimple),
      multiplier (translate z s) = z ^ 2 * multiplier s)
    (conlon : PadicConlonMarkDetection.{u, u} (p := 2) (A := J))
    (burnside : PublishedBurnsideMarkInjectivity.{u, u} (A := J)) :
    let _ : MulAction J (BlockFibre ordinaryBlock block) :=
      stableBlockFibreMulAction ordinaryBlock block hOrdinaryBlockStable
    let _ : MulAction J
        (BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks)
          block) :=
      stableBlockFibreMulAction
        (irreducibleBrauerCharacterBlock iota hinj blocks) block
        hBrauerBlockStable
    Nonempty
        ((Representation.ofMulAction ℤ J (BlockFibre ordinaryBlock block)).Equiv
          (Representation.ofMulAction ℤ J
            (BlockFibre
              (irreducibleBrauerCharacterBlock iota hinj blocks) block))) ∧
      ∃ e : BlockFibre
          (irreducibleBrauerCharacterBlock iota hinj blocks) block ≃
            BlockFibre ordinaryBlock block,
        forall (j : J)
          (phi : BlockFibre
            (irreducibleBrauerCharacterBlock iota hinj blocks) block),
          e (j • phi) = j • e phi := by
  dsimp only
  letI : MulAction J (BlockFibre ordinaryBlock block) :=
    stableBlockFibreMulAction ordinaryBlock block hOrdinaryBlockStable
  letI : MulAction J
      (BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) block) :=
    stableBlockFibreMulAction
      (irreducibleBrauerCharacterBlock iota hinj blocks) block
      hBrauerBlockStable
  have hOrdinaryAction : BlockFibreActionCompatible
      (A := J) ordinaryBlock block := by
    intro j x
    rfl
  have hBrauerAction : BlockFibreActionCompatible
      (A := J) (irreducibleBrauerCharacterBlock iota hinj blocks) block := by
    intro j phi
    rfl
  let restricted := restrictRestrictedIntegralBasicSet
    basicSet.toRestrictedIntegralBasicSet ordinaryBlock
      (irreducibleBrauerCharacterBlock iota hinj blocks)
      hblockDiagonal block
  have hmatrix : MatrixEquivariant (A := J)
      restricted.linearEquiv.toLinearMap :=
    matrixEquivariant_restrictBlock_of_kZero_naturality
      basicSet.toRestrictedIntegralBasicSet hblockDiagonal
      tensorFieldActions reductionNatural hOrdinaryAction hBrauerAction
  let latticeEquiv := permutationLatticeEquiv restricted.linearEquiv hmatrix
  have scalar_square_one : forall d : fieldProjection.ker,
      scalar d ^ 2 = 1 :=
    scalar_square_one_of_translated_conjugate scalar parameter translate
      multiplier IsConjugate multiplier_eq_of_conjugate
      translated_conjugate multiplier_translate
  have hsmall : Nat.card fieldProjection.ker ≤ 2 :=
    natCard_le_two_of_units_square_one
      scalar scalar_injective scalar_square_one
  let quotientEmbedding : J ⧸ fieldProjection.ker →* CyclicTarget :=
    fieldProjection.range.subtype.comp
      (QuotientGroup.quotientKerEquivRange fieldProjection).toMonoidHom
  have quotientEmbedding_injective :
      Function.Injective quotientEmbedding :=
    fieldProjection.range.subtype_injective.comp
      (QuotientGroup.quotientKerEquivRange fieldProjection).injective
  have hset := proposition_3_11_relative
    iota hinj blocks block basicSet ordinaryBlock hblockDiagonal
    tensorFieldActions reductionNatural hOrdinaryBlockStable
    hBrauerBlockStable fieldProjection.ker hsmall quotientEmbedding
    quotientEmbedding_injective conlon burnside
  exact ⟨⟨latticeEquiv⟩, hset⟩

end ModularRep.PaperProofs.TypeBConlonBlockRelative


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
