import ModularRep.PaperProofs.SporadicDefectZeroLiteralBaseActual

/-!
# Lemma 5.2 on sets of characters and weights

This module replaces the global `Formalisation.IBAW.Context` endpoint of the
earlier Lemma 5.2 formalisation by the manuscript's actual carriers:

* function-valued irreducible Brauer characters `IBr iota`;
* conjugacy classes of literal character weights;
* primitive central idempotents of the modular group algebra as blocks;
* conjugacy classes of literal radical subgroups;
* the block of a weight constructed by local block formation, inflation, and
  block induction, with the ambient catalogue identified pointwise with the
  underlying primitive idempotents.

The numerical blockwise Alperin weight conjecture is retained as the stated
premise of the manuscript lemma.  Lean chooses blockwise equivalences while
preserving the prescribed defect-zero normalisation, combines them, proves
block preservation, derives the radical partition and all block/radical
restrictions, and proves automorphism equivariance from the exact assertion
that every automorphism is inner.

The reduction of a defect-zero ordinary character is not an arbitrary map:
it is chosen from an existence-and-uniqueness theorem about equality on
prime regular elements.  The weight at the trivial radical subgroup is also
constructed literally.  Its completeness follows from the literal quotient
definitions and `N_X(1)/1 ≃ X`.  Its injectivity and compatibility with block
induction remain narrowly stated E1 inputs.

No BAW/iBAW predicate, `Formalisation.IBAW.Data`, global character--weight
map, or final inductive-condition conclusion is an input or output here.
The existing concrete reduction-and-inflation endpoint is re-exposed below
for a literal representative of every matched weight.  Compatible
extensions, intermediate block equalities, and modular character triples
remain E2 clauses outside the K-level carrier construction.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual

open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero

universe u

variable {p : ℕ} {k K X BlockIndex : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X] [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}

noncomputable local instance centerFintype :
    Fintype (Subgroup.center X) :=
  Fintype.ofFinite _

variable (iota : PrimeRegularRootEmbedding p k K X)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)

noncomputable local instance actualBlockDecidableEq :
    DecidableEq (ActualBlock (k := k) (X := X)) :=
  Classical.decEq _

noncomputable local instance brauerCharacterDecidableEq :
    DecidableEq (IBr iota) :=
  Classical.decEq _

noncomputable local instance weightClassDecidableEq :
    DecidableEq (WeightClass (p := p) (K := K) (X := X)) :=
  Classical.decEq _

noncomputable local instance globalDefectZeroCharacterDecidableEq :
    DecidableEq (GlobalDefectZeroCharacter (p := p) (K := K) (X := X)) :=
  Classical.decEq _

variable (R : LiteralBlockSource (p := p) (k := k) (K := K) (X := X))
variable (D : DefectZeroReductionSource (p := p) (K := K) (X := X) iota)
variable (T : TrivialWeightSource (p := p) (X := X))

variable (C : TrivialWeightBlockCompatibility iota hinj blocks R D T)

/-- Numerical blockwise AWC on the two literal carriers. -/
def NumericalBlockwiseAWC [Fintype (IBr iota)]
    [Fintype (WeightClass (p := p) (K := K) (X := X))] : Prop :=
  ∀ b : ActualBlock (k := k) (X := X),
    Fintype.card {phi : IBr iota //
      brauerBlock (iota := iota) (hinj := hinj) (blocks := blocks) phi = b} =
      Fintype.card {w : WeightClass (p := p) (K := K) (X := X) //
        R.1.weightBlock w = b}

/-- Defect-zero characters whose reduction belongs to `b`. -/
abbrev DefectZeroFibre (b : ActualBlock (k := k) (X := X)) :=
  {d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X) //
    brauerBlock (iota := iota) (hinj := hinj) (blocks := blocks)
      (D.reduce (iota := iota) d) = b}

/-- Literal irreducible Brauer characters in `b`. -/
abbrev BrauerFibre (b : ActualBlock (k := k) (X := X)) :=
  {phi : IBr iota //
    brauerBlock (iota := iota) (hinj := hinj) (blocks := blocks) phi = b}

/-- Literal character weights whose induced block is `b`. -/
abbrev WeightFibre (b : ActualBlock (k := k) (X := X)) :=
  {w : WeightClass (p := p) (K := K) (X := X) // R.1.weightBlock w = b}

/-- Canonical reduction restricted to one literal block. -/
def reduceInBlock (b : ActualBlock (k := k) (X := X)) :
    DefectZeroFibre (iota := iota) (hinj := hinj) (blocks := blocks) D b →
      BrauerFibre (iota := iota) (hinj := hinj) (blocks := blocks) b :=
  fun d ↦ ⟨D.reduce (iota := iota) d, d.2⟩

/-- The constructed trivial-radical weight restricted to the same block. -/
def atOneInBlock (b : ActualBlock (k := k) (X := X)) :
    DefectZeroFibre (iota := iota) (hinj := hinj) (blocks := blocks) D b →
      WeightFibre (R := R) b :=
  fun d ↦ ⟨T.atOne d, (C.block_atOne d).trans d.2⟩

theorem reduceInBlock_injective (b : ActualBlock (k := k) (X := X)) :
    Function.Injective
      (reduceInBlock (iota := iota) (hinj := hinj) (blocks := blocks) D b) := by
  intro d d' h
  apply Subtype.ext
  exact D.reduce_injective (iota := iota) (congrArg Subtype.val h)

theorem atOneInBlock_injective
    (TI : TrivialWeightIdentification (p := p) (K := K) (X := X) T)
    (b : ActualBlock (k := k) (X := X)) :
    Function.Injective (atOneInBlock
      (iota := iota) (hinj := hinj) (blocks := blocks)
      (R := R) (D := D) (T := T) (C := C) b) := by
  intro d d' h
  apply Subtype.ext
  exact TI.injective (congrArg Subtype.val h)

/-- The prescribed normalisation between its two images in a block. -/
def normalisationImageEquiv
    (TI : TrivialWeightIdentification (p := p) (K := K) (X := X) T)
    (b : ActualBlock (k := k) (X := X)) :
    Set.range (reduceInBlock
      (iota := iota) (hinj := hinj) (blocks := blocks) D b) ≃
      Set.range (atOneInBlock
        (iota := iota) (hinj := hinj) (blocks := blocks)
        (R := R) (D := D) (T := T) (C := C) b) :=
  (Equiv.ofInjective
    (reduceInBlock (iota := iota) (hinj := hinj) (blocks := blocks) D b)
    (reduceInBlock_injective
      (iota := iota) (hinj := hinj) (blocks := blocks) D b)).symm |>.trans
      (Equiv.ofInjective
        (atOneInBlock (iota := iota) (hinj := hinj) (blocks := blocks)
          (R := R) (D := D) (T := T) (C := C) b)
        (atOneInBlock_injective
          (iota := iota) (hinj := hinj) (blocks := blocks)
          (R := R) (D := D) (T := T) (C := C) (TI := TI) b))

@[simp]
theorem normalisationImageEquiv_reduce
    (TI : TrivialWeightIdentification (p := p) (K := K) (X := X) T)
    (b : ActualBlock (k := k) (X := X))
    (d : DefectZeroFibre
      (iota := iota) (hinj := hinj) (blocks := blocks) D b) :
    (normalisationImageEquiv
      (iota := iota) (hinj := hinj) (blocks := blocks)
      (R := R) (D := D) (T := T) (C := C) (TI := TI) b
      ⟨reduceInBlock (iota := iota) (hinj := hinj) (blocks := blocks) D b d,
        Set.mem_range_self d⟩ : WeightFibre (R := R) b) =
      atOneInBlock (iota := iota) (hinj := hinj) (blocks := blocks)
        (R := R) (D := D) (T := T) (C := C) b d := by
  simp [normalisationImageEquiv]

section Finite

variable [Fintype (IBr iota)]
variable [Fintype (WeightClass (p := p) (K := K) (X := X))]
variable [Fintype (GlobalDefectZeroCharacter (p := p) (K := K) (X := X))]
variable (TI : TrivialWeightIdentification (p := p) (K := K) (X := X) T)
variable (hAWC : NumericalBlockwiseAWC
  (iota := iota) (hinj := hinj) (blocks := blocks) (R := R))

/-- Equal total block cardinalities leave equal complements after the
defect-zero normalisation has been reserved. -/
theorem card_compl_normalisation_eq
    (TI : TrivialWeightIdentification (p := p) (K := K) (X := X) T)
    (hAWC : NumericalBlockwiseAWC
      (iota := iota) (hinj := hinj) (blocks := blocks) (R := R))
    (b : ActualBlock (k := k) (X := X)) :
    Fintype.card ↑((Set.range
      (reduceInBlock (iota := iota) (hinj := hinj) (blocks := blocks)
        D b))ᶜ) =
      Fintype.card ↑((Set.range
        (atOneInBlock (iota := iota) (hinj := hinj) (blocks := blocks)
          (R := R) (D := D) (T := T) (C := C) b))ᶜ) := by
  rw [Fintype.card_compl_set, Fintype.card_compl_set]
  rw [hAWC b]
  congr 1
  exact Fintype.card_congr
    (normalisationImageEquiv
      (iota := iota) (hinj := hinj) (blocks := blocks)
      (R := R) (D := D) (T := T) (C := C) (TI := TI) b)

/-- A chosen equivalence on one literal block, extending
`chi^0 ↦ (1, chi)`. -/
def blockEquiv
    (TI : TrivialWeightIdentification (p := p) (K := K) (X := X) T)
    (hAWC : NumericalBlockwiseAWC
      (iota := iota) (hinj := hinj) (blocks := blocks) (R := R))
    (b : ActualBlock (k := k) (X := X)) :
    BrauerFibre (iota := iota) (hinj := hinj) (blocks := blocks) b ≃
      WeightFibre (R := R) b := by
  let e₀ := normalisationImageEquiv
    (iota := iota) (hinj := hinj) (blocks := blocks)
    (R := R) (D := D) (T := T) (C := C) (TI := TI) b
  let eCompl :
      ↑((Set.range (reduceInBlock
        (iota := iota) (hinj := hinj) (blocks := blocks) D b))ᶜ) ≃
        ↑((Set.range (atOneInBlock
          (iota := iota) (hinj := hinj) (blocks := blocks)
          (R := R) (D := D) (T := T) (C := C) b))ᶜ) :=
    Fintype.equivOfCardEq
      (card_compl_normalisation_eq
        (iota := iota) (hinj := hinj) (blocks := blocks)
        (R := R) (D := D) (T := T) (C := C) (TI := TI) (hAWC := hAWC) b)
  exact ((Equiv.Set.compl e₀).symm eCompl).1

theorem blockEquiv_reduce
    (TI : TrivialWeightIdentification (p := p) (K := K) (X := X) T)
    (hAWC : NumericalBlockwiseAWC
      (iota := iota) (hinj := hinj) (blocks := blocks) (R := R))
    (b : ActualBlock (k := k) (X := X))
    (d : DefectZeroFibre
      (iota := iota) (hinj := hinj) (blocks := blocks) D b) :
    blockEquiv (iota := iota) (hinj := hinj) (blocks := blocks)
        (R := R) (D := D) (T := T) (C := C) (TI := TI) (hAWC := hAWC) b
        (reduceInBlock (iota := iota) (hinj := hinj) (blocks := blocks) D b d) =
      atOneInBlock (iota := iota) (hinj := hinj) (blocks := blocks)
        (R := R) (D := D) (T := T) (C := C) b d := by
  let e₀ := normalisationImageEquiv
    (iota := iota) (hinj := hinj) (blocks := blocks)
    (R := R) (D := D) (T := T) (C := C) (TI := TI) b
  let eCompl :
      ↑((Set.range (reduceInBlock
        (iota := iota) (hinj := hinj) (blocks := blocks) D b))ᶜ) ≃
        ↑((Set.range (atOneInBlock
          (iota := iota) (hinj := hinj) (blocks := blocks)
          (R := R) (D := D) (T := T) (C := C) b))ᶜ) :=
    Fintype.equivOfCardEq
      (card_compl_normalisation_eq
        (iota := iota) (hinj := hinj) (blocks := blocks)
        (R := R) (D := D) (T := T) (C := C) (TI := TI) (hAWC := hAWC) b)
  change (((Equiv.Set.compl e₀).symm eCompl).1
    (reduceInBlock (iota := iota) (hinj := hinj) (blocks := blocks) D b d)) = _
  have hExtension := ((Equiv.Set.compl e₀).symm eCompl).2
  exact (hExtension
    ⟨reduceInBlock (iota := iota) (hinj := hinj) (blocks := blocks) D b d,
      Set.mem_range_self d⟩).trans
      (normalisationImageEquiv_reduce
        (iota := iota) (hinj := hinj) (blocks := blocks)
        (R := R) (D := D) (T := T) (C := C) (TI := TI) b d)

/-- The global equivalence on the two literal carriers. -/
def globalEquiv
    (TI : TrivialWeightIdentification (p := p) (K := K) (X := X) T)
    (hAWC : NumericalBlockwiseAWC
      (iota := iota) (hinj := hinj) (blocks := blocks) (R := R)) :
    IBr iota ≃ WeightClass (p := p) (K := K) (X := X) :=
  (Equiv.sigmaFiberEquiv
    (brauerBlock (iota := iota) (hinj := hinj) (blocks := blocks))).symm |>.trans
    (Equiv.sigmaCongrRight
      (blockEquiv (iota := iota) (hinj := hinj) (blocks := blocks)
        (R := R) (D := D) (T := T) (C := C) (TI := TI) (hAWC := hAWC))) |>.trans
    (Equiv.sigmaFiberEquiv R.1.weightBlock)

@[simp]
theorem globalEquiv_apply (phi : IBr iota) :
    globalEquiv (iota := iota) (hinj := hinj) (blocks := blocks)
      (R := R) (D := D) (T := T) (C := C) (TI := TI) (hAWC := hAWC) phi =
      (blockEquiv (iota := iota) (hinj := hinj) (blocks := blocks)
        (R := R) (D := D) (T := T) (C := C) (TI := TI) (hAWC := hAWC)
        (brauerBlock (iota := iota) (hinj := hinj) (blocks := blocks) phi)
        ⟨phi, rfl⟩ :
          WeightFibre (R := R)
            (brauerBlock (iota := iota) (hinj := hinj) (blocks := blocks) phi)) :=
  rfl

/-- The constructed equivalence preserves the literal induced block. -/
theorem globalEquiv_block_preserving (phi : IBr iota) :
    R.1.weightBlock (globalEquiv
      (iota := iota) (hinj := hinj) (blocks := blocks)
      (R := R) (D := D) (T := T) (C := C) (TI := TI) (hAWC := hAWC) phi) =
      brauerBlock (iota := iota) (hinj := hinj) (blocks := blocks) phi :=
  (blockEquiv (iota := iota) (hinj := hinj) (blocks := blocks)
    (R := R) (D := D) (T := T) (C := C) (TI := TI) (hAWC := hAWC)
    (brauerBlock (iota := iota) (hinj := hinj) (blocks := blocks) phi)
    ⟨phi, rfl⟩).2

section CentralSectors

variable [Invertible (Fintype.card (Subgroup.center X) : k)]

/-- Block preservation also preserves the literal central character sector
defined from the primitive block idempotent. -/
theorem globalEquiv_sector_preserving (phi : IBr iota) :
    ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual.weightSector
        (R := R)
        (globalEquiv (iota := iota) (hinj := hinj) (blocks := blocks)
          (R := R) (D := D) (T := T) (C := C) (TI := TI)
          (hAWC := hAWC) phi) =
      ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual.brauerSector
        iota hinj blocks phi := by
  unfold
    ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual.weightSector
    ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual.brauerSector
  rw [globalEquiv_block_preserving
    (iota := iota) (hinj := hinj) (blocks := blocks)
    (R := R) (D := D) (T := T) (C := C) (TI := TI)
    (hAWC := hAWC)]
  rfl

end CentralSectors

/-- The chosen equivalence retains the required defect-zero
normalisation. -/
theorem globalEquiv_normalisation
    (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X)) :
    globalEquiv (iota := iota) (hinj := hinj) (blocks := blocks)
      (R := R) (D := D) (T := T) (C := C) (TI := TI) (hAWC := hAWC)
      (D.reduce (iota := iota) d) =
      T.atOne d := by
  let d' : DefectZeroFibre
      (iota := iota) (hinj := hinj) (blocks := blocks) D
      (brauerBlock (iota := iota) (hinj := hinj) (blocks := blocks)
        (D.reduce (iota := iota) d)) := ⟨d, rfl⟩
  change
    (blockEquiv (iota := iota) (hinj := hinj) (blocks := blocks)
      (R := R) (D := D) (T := T) (C := C) (TI := TI) (hAWC := hAWC)
      (brauerBlock (iota := iota) (hinj := hinj) (blocks := blocks)
        (D.reduce (iota := iota) d))
      (reduceInBlock (iota := iota) (hinj := hinj) (blocks := blocks)
        D _ d') : WeightFibre (R := R) _) = T.atOne d
  exact congrArg Subtype.val
    (blockEquiv_reduce
      (iota := iota) (hinj := hinj) (blocks := blocks)
      (R := R) (D := D) (T := T) (C := C) (TI := TI) (hAWC := hAWC) _ d')

/-! ## The complete-group automorphism collapse -/

/-- Exact group-theoretic meaning of `Out(X)=1`: every automorphism of the
literal cover is inner. -/
structure AllAutomorphismsInner : Prop where
  eq_conj : ∀ alpha : MulAut X, ∃ x : X, alpha = MulAut.conj x

namespace AllAutomorphismsInner

/-- The canonical automorphism action on `IBr` is trivial. -/
theorem brauer_fixed (O : AllAutomorphismsInner (X := X))
    (alpha : (MulAut X)ᵐᵒᵖ) (phi : IBr iota) :
    alpha • phi = phi := by
  obtain ⟨x, hx⟩ := O.eq_conj alpha.unop
  apply IrreducibleBrauerCharacter.twist_eq_self_of_underlying
  rw [hx]
  exact PrimeRegularClassFunction.twist_conj phi.1 x

/-- The canonical automorphism action on conjugacy classes of literal
weights is trivial. -/
theorem weight_fixed (O : AllAutomorphismsInner (X := X))
    (alpha : (MulAut X)ᵐᵒᵖ)
    (w : WeightClass (p := p) (K := K) (X := X)) :
    alpha • w = w := by
  obtain ⟨x, hx⟩ := O.eq_conj alpha.unop
  have halpha : alpha = MulOpposite.op (MulAut.conj x) := by
    apply MulOpposite.unop_injective
    simpa using hx
  rw [halpha]
  refine Quotient.inductionOn w ?_
  intro W
  apply Quotient.sound
  refine ⟨x⁻¹, ?_⟩
  change
    CharacterWeight.rightTwistIsoClass (MulAut.conj (x⁻¹)⁻¹) W =
      CharacterWeight.rightTwistIsoClass (MulAut.conj x) W
  simp

/-- Hence the constructed global equivalence is equivariant for the full
canonical automorphism actions. -/
theorem globalEquiv_equivariant
    (O : AllAutomorphismsInner (X := X))
    (alpha : (MulAut X)ᵐᵒᵖ) (phi : IBr iota) :
    globalEquiv (iota := iota) (hinj := hinj) (blocks := blocks)
        (R := R) (D := D) (T := T) (C := C) (TI := TI) (hAWC := hAWC) (alpha • phi) =
      alpha • globalEquiv (iota := iota) (hinj := hinj) (blocks := blocks)
        (R := R) (D := D) (T := T) (C := C) (TI := TI) (hAWC := hAWC) phi := by
  rw [brauer_fixed (iota := iota) O, weight_fixed O]

end AllAutomorphismsInner

/-! ## The radical partition and local restrictions -/

/-- The radical class assigned to a Brauer character by the constructed
literal equivalence. -/
def part (phi : IBr iota) : RadicalClass (p := p) (X := X) :=
  CharacterWeight.radicalClass
    (globalEquiv (iota := iota) (hinj := hinj) (blocks := blocks)
      (R := R) (D := D) (T := T) (C := C) (TI := TI) (hAWC := hAWC) phi)

/-- The radical decomposition is equivariant for the canonical action. -/
theorem part_equivariant
    (O : AllAutomorphismsInner (X := X))
    (alpha : (MulAut X)ᵐᵒᵖ) (phi : IBr iota) :
    part (iota := iota) (hinj := hinj) (blocks := blocks)
        (R := R) (D := D) (T := T) (C := C) (TI := TI) (hAWC := hAWC) (alpha • phi) =
      alpha • part (iota := iota) (hinj := hinj) (blocks := blocks)
        (R := R) (D := D) (T := T) (C := C) (TI := TI) (hAWC := hAWC) phi := by
  unfold part
  rw [AllAutomorphismsInner.globalEquiv_equivariant
      (iota := iota) (hinj := hinj) (blocks := blocks)
      (R := R) (D := D) (T := T) (C := C) (TI := TI) (hAWC := hAWC) O,
    CharacterWeight.radicalClass_equivariant]

/-- The derived parts form a genuine disjoint-union partition. -/
def partitionEquiv :
    IBr iota ≃ Sigma fun radical : RadicalClass (p := p) (X := X) ↦
      {phi : IBr iota //
        part (iota := iota) (hinj := hinj) (blocks := blocks)
          (R := R) (D := D) (T := T) (C := C) (TI := TI) (hAWC := hAWC) phi = radical} :=
  (Equiv.sigmaFiberEquiv
    (part (iota := iota) (hinj := hinj) (blocks := blocks)
      (R := R) (D := D) (T := T) (C := C) (TI := TI) (hAWC := hAWC))).symm

/-- The blockwise local bijection at a literal radical class. -/
def localEquiv
    (b : ActualBlock (k := k) (X := X))
    (radical : RadicalClass (p := p) (X := X)) :
    {phi : IBr iota //
      brauerBlock (iota := iota) (hinj := hinj) (blocks := blocks) phi = b ∧
        part (iota := iota) (hinj := hinj) (blocks := blocks)
          (R := R) (D := D) (T := T) (C := C) (TI := TI) (hAWC := hAWC) phi = radical} ≃
      {w : WeightClass (p := p) (K := K) (X := X) //
        R.1.weightBlock w = b ∧
          CharacterWeight.radicalClass w = radical} := by
  let e := globalEquiv (iota := iota) (hinj := hinj) (blocks := blocks)
    (R := R) (D := D) (T := T) (C := C) (TI := TI) (hAWC := hAWC)
  refine
    { toFun := fun phi ↦ ⟨e phi, ?_⟩
      invFun := fun w ↦ ⟨e.symm w, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · exact ⟨by
      rw [globalEquiv_block_preserving
          (iota := iota) (hinj := hinj) (blocks := blocks)
          (R := R) (D := D) (T := T) (C := C) (TI := TI) (hAWC := hAWC),
        phi.2.1], phi.2.2⟩
  · constructor
    · calc
        brauerBlock (iota := iota) (hinj := hinj) (blocks := blocks)
            (e.symm w) = R.1.weightBlock (e (e.symm w)) :=
          (globalEquiv_block_preserving
            (iota := iota) (hinj := hinj) (blocks := blocks)
            (R := R) (D := D) (T := T) (C := C) (TI := TI) (hAWC := hAWC) (e.symm w)).symm
        _ = R.1.weightBlock w := by rw [e.apply_symm_apply]
        _ = b := w.2.1
    · change CharacterWeight.radicalClass (e (e.symm w)) = radical
      rw [e.apply_symm_apply]
      exact w.2.2
  · intro phi
    apply Subtype.ext
    exact e.symm_apply_apply phi
  · intro w
    apply Subtype.ext
    exact e.apply_symm_apply w

/-- Every defect-zero reduction belongs to the literal part indexed by the
trivial radical class. -/
theorem part_reduce
    (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X)) :
    part (iota := iota) (hinj := hinj) (blocks := blocks)
      (R := R) (D := D) (T := T) (C := C) (TI := TI) (hAWC := hAWC)
      (D.reduce (iota := iota) d) =
      RadicalConjugacyClass.trivialClass T.trivialRadical := by
  unfold part
  rw [globalEquiv_normalisation
    (iota := iota) (hinj := hinj) (blocks := blocks)
    (R := R) (D := D) (T := T) (C := C) (TI := TI) (hAWC := hAWC)]
  exact T.radicalClass_atOne d

/-- The part at the trivial radical class consists exactly of the canonical
reductions of defect-zero ordinary characters. -/
theorem part_eq_trivial_iff (phi : IBr iota) :
    part (iota := iota) (hinj := hinj) (blocks := blocks)
      (R := R) (D := D) (T := T) (C := C) (TI := TI) (hAWC := hAWC) phi =
        RadicalConjugacyClass.trivialClass T.trivialRadical ↔
      ∃ d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X),
        D.reduce (iota := iota) d = phi := by
  constructor
  · intro hphi
    obtain ⟨d, hd⟩ := T.exists_atOne_of_radicalClass_eq_trivial
      (globalEquiv (iota := iota) (hinj := hinj) (blocks := blocks)
        (R := R) (D := D) (T := T) (C := C) (TI := TI) (hAWC := hAWC) phi) hphi
    refine ⟨d, (globalEquiv
      (iota := iota) (hinj := hinj) (blocks := blocks)
      (R := R) (D := D) (T := T) (C := C) (TI := TI) (hAWC := hAWC)).injective ?_⟩
    rw [globalEquiv_normalisation
      (iota := iota) (hinj := hinj) (blocks := blocks)
      (R := R) (D := D) (T := T) (C := C) (TI := TI) (hAWC := hAWC), hd]
  · rintro ⟨d, rfl⟩
    exact part_reduce
      (iota := iota) (hinj := hinj) (blocks := blocks)
      (R := R) (D := D) (T := T) (C := C) (TI := TI) (hAWC := hAWC) d

/-- Every Brauer character in the trivial radical part is the reduction of
a unique defect-zero ordinary character. -/
theorem existsUnique_reduce_of_part_eq_trivial
    (phi : IBr iota)
    (hphi : part (iota := iota) (hinj := hinj) (blocks := blocks)
      (R := R) (D := D) (T := T) (C := C) (TI := TI)
      (hAWC := hAWC) phi =
        RadicalConjugacyClass.trivialClass T.trivialRadical) :
    ∃! d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X),
      D.reduce (iota := iota) d = phi := by
  obtain ⟨d, hd⟩ :=
    (part_eq_trivial_iff
      (iota := iota) (hinj := hinj) (blocks := blocks)
      (R := R) (D := D) (T := T) (C := C) (TI := TI)
      (hAWC := hAWC) phi).mp hphi
  refine ⟨d, hd, ?_⟩
  intro d' hd'
  exact D.reduce_injective (iota := iota) (hd'.trans hd.symm)

/-- The canonical equivalence between defect-zero ordinary characters and
the trivial radical part of the constructed partition. -/
def trivialPartEquiv :
    GlobalDefectZeroCharacter (p := p) (K := K) (X := X) ≃
      {phi : IBr iota //
        part (iota := iota) (hinj := hinj) (blocks := blocks)
          (R := R) (D := D) (T := T) (C := C) (TI := TI)
          (hAWC := hAWC) phi =
            RadicalConjugacyClass.trivialClass T.trivialRadical} :=
  Equiv.ofBijective
    (fun d ↦ ⟨D.reduce (iota := iota) d,
      part_reduce
        (iota := iota) (hinj := hinj) (blocks := blocks)
        (R := R) (D := D) (T := T) (C := C) (TI := TI)
        (hAWC := hAWC) d⟩)
    ⟨
      fun d d' h ↦ D.reduce_injective (iota := iota)
        (congrArg Subtype.val h),
      fun phi ↦ by
        obtain ⟨d, hd, _⟩ := existsUnique_reduce_of_part_eq_trivial
          (iota := iota) (hinj := hinj) (blocks := blocks)
          (R := R) (D := D) (T := T) (C := C) (TI := TI)
          (hAWC := hAWC) phi phi.2
        exact ⟨d, Subtype.ext hd⟩
    ⟩

end Finite

/-! ## The existing literal local reduction endpoint -/

/-- Tie the existing concrete reduction-and-inflation endpoint to a literal
representative of a matched weight.  The equality `hW` ensures that the raw
weight is a representative of the output of the constructed global
equivalence.  The reduction and inflation source remains the exact E1 input
already isolated in `SporadicCompleteCollapseLemma52ConcreteLocal`. -/
theorem matchedWeight_localBrauer_isReduction
    [Fintype (IBr iota)]
    [Fintype (WeightClass (p := p) (K := K) (X := X))]
    [Fintype (GlobalDefectZeroCharacter (p := p) (K := K) (X := X))]
    (TI : TrivialWeightIdentification (p := p) (K := K) (X := X) T)
    (hAWC : NumericalBlockwiseAWC
      (iota := iota) (hinj := hinj) (blocks := blocks) (R := R))
    (phi : IBr iota) (W : CharacterWeight p K X)
    (hW : (Quotient.mk'' (Quotient.mk'' W) :
      WeightClass (p := p) (K := K) (X := X)) =
      globalEquiv (iota := iota) (hinj := hinj) (blocks := blocks)
        (R := R) (D := D) (T := T) (C := C) (TI := TI) (hAWC := hAWC) phi)
    (iotaQuotient : PrimeRegularRootEmbedding p k K
      (NormalizerQuotient W.subgroup))
    (iotaLocal : PrimeRegularRootEmbedding p k K
      (Subgroup.normalizer (W.subgroup : Set X)))
    (hDefectZero :
      ModularRep.PaperProofs.SporadicCompleteCollapseLemma52ConcreteLocal.IsDefectZeroOrdinaryCharacter
        W.localCharacter)
    (E1 :
      ModularRep.PaperProofs.SporadicCompleteCollapseLemma52ConcreteLocal.ConcreteDefectZeroReductionInflation
      (W.subgroup.subgroupOf (Subgroup.normalizer (W.subgroup : Set X)))
      iotaQuotient iotaLocal ⟨W.localCharacter, hDefectZero⟩) :
    (Quotient.mk'' (Quotient.mk'' W) :
        WeightClass (p := p) (K := K) (X := X)) =
        globalEquiv (iota := iota) (hinj := hinj) (blocks := blocks)
          (R := R) (D := D) (T := T) (C := C) (TI := TI) (hAWC := hAWC) phi ∧
      ModularRep.PaperProofs.SporadicCompleteCollapseLemma52ConcreteLocal.IsBrauerReduction
        iotaLocal
        (ModularRep.PaperProofs.SporadicCompleteCollapseLemma52ConcreteLocal.inflateOrdinaryCharacter
          (W.subgroup.subgroupOf (Subgroup.normalizer (W.subgroup : Set X)))
          W.localCharacter)
        E1.localBrauer :=
  ⟨hW, E1.localBrauer_isReductionOf_inflateOrdinary⟩

end ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
