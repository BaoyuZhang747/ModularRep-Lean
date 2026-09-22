import Mathlib.GroupTheory.GroupAction.Basic

/-!
# An abstract interface for manuscript-specific iBAW arguments

This file does not define Brauer characters, blocks, weights, induced blocks,
or modular character triples.  Instead, it records exactly the typed data
that the manuscript constructs from those notions.  Representation theoretic
claims appear as named predicates in a `Context`; subsequent files can prove
that sectorwise or orbitwise constructions preserve all of them.

The distinction between `Candidate` and `Data` is deliberate.  A `Candidate`
contains the partition and an equivariant bijection preserving the induced
block.  A `Data` object additionally certifies the required block equalities
over intermediate groups, compatible extensions, the modular character triple
condition, and the normalisation at the trivial radical class.
-/

namespace Formalisation.IBAW

/-- Equivariance of a predicate on matched global and local objects. -/
def PairPropertyEquivariant {A X Y : Type*} [Group A]
    [MulAction A X] [MulAction A Y] (P : X → Y → Prop) : Prop :=
  ∀ (a : A) (x : X) (y : Y), P x y ↔ P (a • x) (a • y)

/-- The ambient labelled sets and the representation theoretic obligations.

`X` models irreducible Brauer characters and `Y` models conjugacy classes of
weights.  The types `B`, `R`, and `S` model blocks, radical-subgroup classes,
and central character sectors, respectively.  In a concrete instantiation,
`weightBlock` must be the block induced from the local character and
`blockSector` must be the unique central character sector of that block.
The predicate `extensionsOK` must include the required coincidence of the
global and local extensions at `Q = 1`. -/
structure Context (A B R S X Y DZ : Type*) [Group A]
    [MulAction A B] [MulAction A R] [MulAction A S]
    [MulAction A X] [MulAction A Y] [MulAction A DZ] where
  brauerBlock : X → B
  weightBlock : Y → B
  weightRadical : Y → R
  blockSector : B → S
  oneRadical : R
  reduce : DZ → X
  atOne : DZ → Y
  oneRadical_fixed : ∀ a : A, a • oneRadical = oneRadical
  brauerBlock_equivariant : ∀ (a : A) (x : X),
    brauerBlock (a • x) = a • brauerBlock x
  weightBlock_equivariant : ∀ (a : A) (y : Y),
    weightBlock (a • y) = a • weightBlock y
  weightRadical_equivariant : ∀ (a : A) (y : Y),
    weightRadical (a • y) = a • weightRadical y
  blockSector_equivariant : ∀ (a : A) (b : B),
    blockSector (a • b) = a • blockSector b
  reduce_equivariant : ∀ (a : A) (d : DZ), reduce (a • d) = a • reduce d
  atOne_equivariant : ∀ (a : A) (d : DZ), atOne (a • d) = a • atOne d
  reduce_injective : Function.Injective reduce
  atOne_radical : ∀ d : DZ, weightRadical (atOne d) = oneRadical
  atOne_block : ∀ d : DZ, weightBlock (atOne d) = brauerBlock (reduce d)
  atOne_complete : ∀ y : Y, weightRadical y = oneRadical →
    ∃ d : DZ, atOne d = y
  intermediateBlockEqualitiesOK : X → Y → Prop
  extensionsOK : X → Y → Prop
  characterTripleOK : X → Y → Prop
  intermediateBlockEqualities_equivariant :
    PairPropertyEquivariant (A := A) (X := X) (Y := Y)
      intermediateBlockEqualitiesOK
  extensions_equivariant :
    PairPropertyEquivariant (A := A) (X := X) (Y := Y) extensionsOK
  characterTriple_equivariant :
    PairPropertyEquivariant (A := A) (X := X) (Y := Y) characterTripleOK

variable {A B R S X Y DZ : Type*} [Group A]
  [MulAction A B] [MulAction A R] [MulAction A S]
  [MulAction A X] [MulAction A Y] [MulAction A DZ]

/-- A proposed iBAW partition and bijection, before the intermediate-block,
extension, and character-triple obligations have been certified.  The field
`block_preserving` is preservation of the block induced from the local
character. -/
structure Candidate (C : Context A B R S X Y DZ) where
  equiv : X ≃ Y
  equiv_equivariant : ∀ (a : A) (x : X), equiv (a • x) = a • equiv x
  block_preserving : ∀ x : X, C.weightBlock (equiv x) = C.brauerBlock x

/-- A manuscript-level iBAW datum.  Its fields correspond to the partition,
local bijections, preservation of induced blocks, the stronger equalities of
blocks over intermediate groups, compatible extensions, modular character
triples, and the normalisation at the trivial radical class. -/
structure Data (C : Context A B R S X Y DZ) extends Candidate C where
  intermediateBlockEqualities : ∀ x : X,
    C.intermediateBlockEqualitiesOK x (equiv x)
  extensions : ∀ x : X, C.extensionsOK x (equiv x)
  characterTriple : ∀ x : X, C.characterTripleOK x (equiv x)
  normalisation : ∀ d : DZ, equiv (C.reduce d) = C.atOne d

/-- The representation theoretic certification required to upgrade a fixed
candidate to full iBAW data.  In applications these four fields are the
external mathematical work, not consequences of the underlying set
bijection. -/
structure Certification (C : Context A B R S X Y DZ) (W : Candidate C) where
  intermediateBlockEqualities : ∀ x : X,
    C.intermediateBlockEqualitiesOK x (W.equiv x)
  extensions : ∀ x : X, C.extensionsOK x (W.equiv x)
  characterTriple : ∀ x : X, C.characterTripleOK x (W.equiv x)
  normalisation : ∀ d : DZ, W.equiv (C.reduce d) = C.atOne d

namespace Candidate

variable {C : Context A B R S X Y DZ} (W : Candidate C)

/-- Upgrade a candidate using a separate representation theoretic
certification. -/
def certify (H : Certification C W) : Data C where
  toCandidate := W
  intermediateBlockEqualities := H.intermediateBlockEqualities
  extensions := H.extensions
  characterTriple := H.characterTriple
  normalisation := H.normalisation

/-- The radical part of a Brauer character is derived from the radical label
of its image.  It is not independent input. -/
def part (x : X) : R := C.weightRadical (W.equiv x)

/-- The derived radical partition is equivariant. -/
theorem part_equivariant (a : A) (x : X) :
    W.part (a • x) = a • W.part x := by
  simp only [part, W.equiv_equivariant, C.weightRadical_equivariant]

/-- The derived parts form a genuine partition: every Brauer object occurs
in exactly the fibre indexed by its derived radical label. -/
def partitionEquiv : X ≃ Σ r : R, {x : X // W.part x = r} :=
  (Equiv.sigmaFiberEquiv W.part).symm

@[simp]
theorem partitionEquiv_apply (x : X) :
    W.partitionEquiv x = ⟨W.part x, ⟨x, rfl⟩⟩ := rfl

/-- A candidate preserves the central character sector determined by the
block label. -/
theorem sector_preserving (x : X) :
    C.blockSector (C.weightBlock (W.equiv x)) =
      C.blockSector (C.brauerBlock x) := by
  rw [W.block_preserving]

/-- Restriction of the global bijection to one block. -/
def blockEquiv (b : B) :
    {x : X // C.brauerBlock x = b} ≃
      {y : Y // C.weightBlock y = b} where
  toFun x := ⟨W.equiv x, by rw [W.block_preserving, x.property]⟩
  invFun y := ⟨W.equiv.symm y, by
    calc
      C.brauerBlock (W.equiv.symm y) =
          C.weightBlock (W.equiv (W.equiv.symm y)) :=
        (W.block_preserving (W.equiv.symm y)).symm
      _ = C.weightBlock y :=
        congrArg C.weightBlock (W.equiv.apply_symm_apply y)
      _ = b := y.property⟩
  left_inv x := by
    apply Subtype.ext
    exact W.equiv.symm_apply_apply x
  right_inv y := by
    apply Subtype.ext
    exact W.equiv.apply_symm_apply y

/-- Restriction to the part indexed by a block and a radical-subgroup class.
This is the abstract local bijection in the manuscript. -/
def localEquiv (b : B) (r : R) :
    {x : X // C.brauerBlock x = b ∧ W.part x = r} ≃
      {y : Y // C.weightBlock y = b ∧ C.weightRadical y = r} where
  toFun x := ⟨W.equiv x, by
    constructor
    · rw [W.block_preserving, x.property.1]
    · simpa [part] using x.property.2⟩
  invFun y := ⟨W.equiv.symm y, by
    constructor
    · calc
        C.brauerBlock (W.equiv.symm y) =
            C.weightBlock (W.equiv (W.equiv.symm y)) :=
          (W.block_preserving (W.equiv.symm y)).symm
        _ = C.weightBlock y :=
          congrArg C.weightBlock (W.equiv.apply_symm_apply y)
        _ = b := y.property.1
    · simpa [part] using y.property.2⟩
  left_inv x := by
    apply Subtype.ext
    exact W.equiv.symm_apply_apply x
  right_inv y := by
    apply Subtype.ext
    exact W.equiv.apply_symm_apply y

/-- The partition part over a transported block and radical class is carried
to the corresponding transported part. -/
def localActionEquiv (a : A) (b : B) (r : R) :
    {x : X // C.brauerBlock x = b ∧ W.part x = r} ≃
      {x : X // C.brauerBlock x = a • b ∧ W.part x = a • r} where
  toFun x := ⟨a • x, by
    constructor
    · rw [C.brauerBlock_equivariant, x.property.1]
    · rw [W.part_equivariant, x.property.2]⟩
  invFun x := ⟨a⁻¹ • x, by
    constructor
    · rw [C.brauerBlock_equivariant, x.property.1, inv_smul_smul]
    · rw [W.part_equivariant, x.property.2, inv_smul_smul]⟩
  left_inv x := by
    apply Subtype.ext
    change a⁻¹ • (a • (x : X)) = x
    exact inv_smul_smul a (x : X)
  right_inv x := by
    apply Subtype.ext
    change a • (a⁻¹ • (x : X)) = x
    exact smul_inv_smul a (x : X)

end Candidate

namespace Data

variable {C : Context A B R S X Y DZ} (W : Data C)

/-- Forget the certified representation theoretic obligations. -/
abbrev candidate : Candidate C := W.toCandidate

/-- The normalised defect-zero objects belong to the part indexed by the
trivial radical class. -/
theorem part_reduce (d : DZ) : W.toCandidate.part (C.reduce d) = C.oneRadical := by
  rw [Candidate.part, W.normalisation, C.atOne_radical]

/-- The part indexed by the trivial radical consists exactly of the reductions
of the defect-zero objects.  This is the full `Q = 1` normalisation, rather
than only its forward implication. -/
theorem part_eq_one_iff (x : X) :
    W.toCandidate.part x = C.oneRadical ↔ ∃ d : DZ, C.reduce d = x := by
  constructor
  · intro hx
    obtain ⟨d, hd⟩ := C.atOne_complete (W.equiv x) hx
    refine ⟨d, W.equiv.injective ?_⟩
    rw [W.normalisation, hd]
  · rintro ⟨d, rfl⟩
    exact W.part_reduce d

/-- Each Brauer object in the part indexed by the trivial radical is the
reduction of a unique defect-zero object. -/
theorem unique_reduce_of_part_eq_one (x : X)
    (hx : W.toCandidate.part x = C.oneRadical) :
    ∃! d : DZ, C.reduce d = x := by
  obtain ⟨d, hd⟩ := (W.part_eq_one_iff x).mp hx
  exact ⟨d, hd, fun d' hd' => C.reduce_injective (hd'.trans hd.symm)⟩

/-- The reduction map identifies the defect-zero objects with the whole part
indexed by the trivial radical.  Extension compatibility at `Q = 1` is not a
set-theoretic consequence of this equivalence and remains in `extensionsOK`. -/
noncomputable def trivialPartEquiv :
    DZ ≃ {x : X // W.toCandidate.part x = C.oneRadical} :=
  Equiv.ofBijective
    (fun d : DZ => ⟨C.reduce d, W.part_reduce d⟩)
    ⟨
      fun d d' h => C.reduce_injective (congrArg Subtype.val h),
      fun x => by
        obtain ⟨d, hd⟩ := (W.part_eq_one_iff x).mp x.property
        exact ⟨d, Subtype.ext hd⟩
    ⟩

/-- Every matched pair lies in the same central character sector. -/
theorem sector_preserving (x : X) :
    C.blockSector (C.weightBlock (W.equiv x)) =
      C.blockSector (C.brauerBlock x) :=
  W.toCandidate.sector_preserving x

/-- The certified blockwise bijection. -/
abbrev blockEquiv (b : B) := W.toCandidate.blockEquiv b

/-- The certified local bijection indexed by a block and radical class. -/
abbrev localEquiv (b : B) (r : R) := W.toCandidate.localEquiv b r

end Data

end Formalisation.IBAW


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
