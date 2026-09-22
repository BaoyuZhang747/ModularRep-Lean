import Formalisation.IndexedAssembly
import ModularRep.BlockIdempotentDecomposition
import ModularRep.CharacterWeightBlockAssignment
import ModularRep.CharacterWeightRadicalProjection
import ModularRep.CentralCharacterTwist
import ModularRep.IBrBlockAutomorphism

/-!
# Literal carriers for the Fischer calculations

This module contains only the literal character, weight, block, radical, and
central-sector carriers used in the Fischer formalisation, together with their
routine transport maps.  It deliberately contains no An--Dietrich sector
map, block-preserving character-weight equivalence, Q = 1 normalisation,
signature calculation, or iBAW conclusion.  The separate dependency boundary
allows cancellation arguments to import the carriers without importing a
theorem that already supplies the desired block-fibre equivalence.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual

open Formalisation

universe u

variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

noncomputable local instance centerFintype :
    Fintype (Subgroup.center X) :=
  Fintype.ofFinite _

/-- Literal set of blocks: primitive central idempotents of `k[X]`. -/
abbrev ActualBlock :=
  {b : k[X] // IsPrimitiveCentralIdempotent b}

/-- Literal central-sector carrier for the centre of the chosen cover. -/
abbrev CentralSector :=
  Subgroup.center X →* kˣ

/-- Literal global set of weights used in the manuscript. -/
abbrev WeightClass :=
  CharacterWeight.ConjugacyClass (p := p) (K := K) (G := X)

/-- Literal carrier of radical `p`-subgroups. -/
abbrev RadicalSubgroup :=
  CharacterWeight.RadicalSubgroup (p := p) (G := X)

/-- Compatibility name for the reusable right transport of a literal
radical subgroup. -/
def rightTwistRadicalSubgroup
    (Q : RadicalSubgroup (p := p) (X := X)) (alpha : MulAut X) :
    RadicalSubgroup (p := p) (X := X) :=
  CharacterWeight.RadicalSubgroup.rightTwist Q alpha

omit [Fintype X] in
@[simp]
theorem rightTwistRadicalSubgroup_one
    (Q : RadicalSubgroup (p := p) (X := X)) :
    rightTwistRadicalSubgroup Q (1 : MulAut X) = Q := by
  exact CharacterWeight.RadicalSubgroup.rightTwist_one Q

omit [Fintype X] in
theorem rightTwistRadicalSubgroup_mul
    (Q : RadicalSubgroup (p := p) (X := X)) (alpha beta : MulAut X) :
    rightTwistRadicalSubgroup
        (rightTwistRadicalSubgroup Q alpha) beta =
      rightTwistRadicalSubgroup Q (alpha * beta) := by
  exact CharacterWeight.RadicalSubgroup.rightTwist_mul Q alpha beta

omit [Fintype X] in
@[simp]
theorem smul_radicalSubgroup (g : X)
    (Q : RadicalSubgroup (p := p) (X := X)) :
    g • Q = rightTwistRadicalSubgroup Q (MulAut.conj g⁻¹) :=
  CharacterWeight.RadicalSubgroup.smul_eq_rightTwist_conj g Q

/-- Literal conjugacy classes of radical subgroups. -/
abbrev RadicalClass :=
  CharacterWeight.RadicalConjugacyClass (p := p) (G := X)

/-- Compatibility name for the reusable projection from a weight
isomorphism class to its literal radical subgroup. -/
def radicalIsoClass :
    CharacterWeight.IsoClass (p := p) (K := K) (G := X) →
      RadicalSubgroup (p := p) (X := X) :=
  CharacterWeight.radicalSubgroupOfIsoClass

theorem radicalIsoClass_conjugation
    (g : X) (W : CharacterWeight.IsoClass (p := p) (K := K) (G := X)) :
    radicalIsoClass (g • W) = g • radicalIsoClass W := by
  exact CharacterWeight.radicalSubgroupOfIsoClass_conjugation g W

/-- The radical-class projection from the literal weight quotient. -/
def weightRadical :
    WeightClass (p := p) (K := K) (X := X) →
      RadicalClass (p := p) (X := X) :=
  CharacterWeight.radicalClass

omit [Fintype X] in
theorem rightTwistRadicalSubgroup_conjugation
    (alpha : MulAut X) (g : X)
    (Q : RadicalSubgroup (p := p) (X := X)) :
    rightTwistRadicalSubgroup (g • Q) alpha =
      alpha.symm g • rightTwistRadicalSubgroup Q alpha := by
  exact CharacterWeight.RadicalSubgroup.rightTwist_conjugation alpha g Q

/-- Automorphism transport on radical conjugacy classes. -/
def rightTwistRadicalClass (alpha : MulAut X) :
    RadicalClass (p := p) (X := X) → RadicalClass (p := p) (X := X) :=
  CharacterWeight.RadicalConjugacyClass.rightTwist alpha

omit [Fintype X] in
@[simp]
theorem rightTwistRadicalClass_one
    (q : RadicalClass (p := p) (X := X)) :
    rightTwistRadicalClass (p := p) (X := X) (1 : MulAut X) q = q := by
  exact CharacterWeight.RadicalConjugacyClass.rightTwist_one q

omit [Fintype X] in
theorem rightTwistRadicalClass_mul
    (q : RadicalClass (p := p) (X := X)) (alpha beta : MulAut X) :
    rightTwistRadicalClass (p := p) (X := X) beta
        (rightTwistRadicalClass (p := p) (X := X) alpha q) =
      rightTwistRadicalClass (p := p) (X := X) (alpha * beta) q := by
  exact CharacterWeight.RadicalConjugacyClass.rightTwist_mul q alpha beta

theorem radicalIsoClass_rightTwist
    (alpha : MulAut X)
    (W : CharacterWeight.IsoClass (p := p) (K := K) (G := X)) :
    radicalIsoClass
        (CharacterWeight.rightTwistIsoClass
          (p := p) (K := K) (G := X) alpha W) =
      rightTwistRadicalSubgroup (radicalIsoClass W) alpha := by
  exact CharacterWeight.radicalSubgroupOfIsoClass_rightTwist alpha W

theorem weightRadical_rightTwist
    (alpha : MulAut X)
    (w : WeightClass (p := p) (K := K) (X := X)) :
    weightRadical
        (CharacterWeight.rightTwistConjugacyClass
          (p := p) (K := K) (G := X) alpha w) =
      rightTwistRadicalClass alpha (weightRadical w) := by
  exact CharacterWeight.radicalClass_rightTwist alpha w

/-- The literal radical projection commutes with every automorphism. -/
theorem weightRadical_equivariant
    (a : (MulAut X)ᵐᵒᵖ)
    (w : WeightClass (p := p) (K := K) (X := X)) :
    weightRadical (a • w) = a • weightRadical w :=
  CharacterWeight.radicalClass_equivariant a w

/-- The manuscript right action on central characters, encoded as a left
action of the opposite automorphism group. -/
noncomputable instance centralSectorMulAction :
    MulAction (MulAut X)ᵐᵒᵖ (CentralSector (k := k) (X := X)) where
  smul alpha nu :=
    nu.comp (Representation.centerAutomorphism alpha.unop).toMonoidHom
  one_smul nu := by
    ext z
    rfl
  mul_smul alpha beta nu := by
    ext z
    rfl

variable (iota : PrimeRegularRootEmbedding p k K X)
variable (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable {BlockIndex : Type u} [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}
variable (blocks : BlockIdempotentDecomposition blockIdempotent)

/-- Regard an index in a complete block decomposition as its literal
primitive central idempotent. -/
def actualBlockOfIndex (b : BlockIndex) : ActualBlock (k := k) (X := X) :=
  ⟨blockIdempotent b, blocks.primitive b⟩

/-- The literal block containing a function-valued irreducible Brauer
character, obtained from the complete idempotent decomposition. -/
def brauerBlock (phi : IBr iota) : ActualBlock (k := k) (X := X) :=
  actualBlockOfIndex blocks
    (FDRepSimpleClassKZero.irreducibleBrauerCharacterBlock
      iota hinj blocks phi)

/-- The literal block of a Brauer character is transported by the canonical
automorphism action. -/
theorem brauerBlock_transport
    (a : (MulAut X)ᵐᵒᵖ) (phi : IBr iota) :
    brauerBlock iota hinj blocks (a • phi) =
      a • brauerBlock iota hinj blocks phi := by
  unfold brauerBlock actualBlockOfIndex
  exact FDRepSimpleClassKZero.primitiveBlockOfIndex_irreducibleBrauerCharacterBlock_op_smul
    iota hinj blocks a phi

variable [Invertible (Fintype.card (Subgroup.center X) : k)]

/-- The literal central character sector of a primitive block idempotent. -/
def blockSector (b : ActualBlock (k := k) (X := X)) :
    CentralSector (k := k) (X := X) :=
  b.2.centralCharacterSector (Subgroup.center X) le_rfl

/-- The central character sector of a literal block is transported by the
canonical automorphism action. -/
theorem blockSector_transport
    (a : (MulAut X)ᵐᵒᵖ) (b : ActualBlock (k := k) (X := X)) :
    blockSector (k := k) (X := X) (a • b) =
      a • blockSector (k := k) (X := X) b := by
  exact LiteralPrimitiveBlock.rightMulAction_smul_centralCharacterSector a b

/-- A local-block-induction source whose ambient block catalogue is indexed
by the literal primitive idempotents themselves.  The coherence condition
rules out a permutation of the literal block labels in the catalogue. -/
abbrev LiteralCarrierAdapter :=
  {R : CharacterWeight.LocalBlockInductionSource
      (p := p) (k := k) (K := K) (G := X)
      (Block := ActualBlock (k := k) (X := X)) //
    ∀ b : ActualBlock (k := k) (X := X),
      R.operations.ambientBlockData.blockIdempotent b = b.1}

omit [Invertible (Fintype.card (Subgroup.center X) : k)] in
/-- The operations catalogue of a literal carrier transports Brauer support
under every automorphism. The literal-idempotent coherence turns the general
primitive-block transport theorem into equality of the literal block indices
themselves. -/
theorem operationsBrauerSupport
    (R : LiteralCarrierAdapter
      (p := p) (k := k) (K := K) (X := X)) :
    let O := R.1.operations
    letI : Fintype (ActualBlock (k := k) (X := X)) :=
      O.ambientBlockData.fintypeBlock
    ∀ (alpha : (MulAut X)ᵐᵒᵖ) (phi : IBr iota),
      FDRepSimpleClassKZero.irreducibleBrauerCharacterBlock iota hinj
          O.ambientBlockData.blocks (alpha • phi) =
        alpha •
          FDRepSimpleClassKZero.irreducibleBrauerCharacterBlock iota hinj
            O.ambientBlockData.blocks phi := by
  dsimp only
  let O := R.1.operations
  letI : Fintype (ActualBlock (k := k) (X := X)) :=
    O.ambientBlockData.fintypeBlock
  intro alpha phi
  have hprimitive :
      ∀ b : ActualBlock (k := k) (X := X),
        O.ambientBlockData.blocks.primitiveBlockOfIndex b = b := by
    intro b
    apply Subtype.ext
    exact R.2 b
  simpa only [hprimitive] using
    (FDRepSimpleClassKZero.primitiveBlockOfIndex_irreducibleBrauerCharacterBlock_op_smul
        iota hinj O.ambientBlockData.blocks alpha phi)

/-- Compatibility shell retained for the existing Fischer interfaces.  The
routine transport facts are kernel theorems and are not fields of this type. -/
structure RoutineTransportInput
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
    {BlockIndex : Type u} [Fintype BlockIndex]
    {blockIdempotent : BlockIndex → k[X]}
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X)) : Prop where

variable {R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X)}
variable (E1 : RoutineTransportInput iota hinj blocks R)

/-- The constructed induced block together with the literal radical class of
a weight. -/
def weightBlockRadical
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
    (w : WeightClass (p := p) (K := K) (X := X)) :
    ActualBlock (k := k) (X := X) × RadicalClass (p := p) (X := X) :=
  (R.1.weightBlock w, weightRadical w)

omit [CharP k p] [IsAlgClosed k]
  [Invertible (Fintype.card (Subgroup.center X) : k)] in
/-- Local block induction and the literal radical projection have the same
automorphism transport. -/
theorem weightBlockRadical_equivariant
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
    (a : (MulAut X)ᵐᵒᵖ)
    (w : WeightClass (p := p) (K := K) (X := X)) :
    weightBlockRadical R (a • w) = a • weightBlockRadical R w := by
  apply Prod.ext
  · exact R.1.weightBlock_transport a w
  · exact weightRadical_equivariant a w

/-- Radical projection on a fibre of the constructed block assignment. -/
def blockFibreRadical
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
    (b : ActualBlock (k := k) (X := X)) (w : R.1.Fibre b) :
    RadicalClass (p := p) (X := X) :=
  weightRadical w.1

omit [CharP k p] [IsAlgClosed k]
  [Invertible (Fintype.card (Subgroup.center X) : k)] in
/-- The radical projection on a block fibre commutes with the stabiliser
action constructed from local block induction. -/
theorem blockFibreRadical_equivariant
    (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
    (b : ActualBlock (k := k) (X := X))
    (a : MulAction.stabilizer (MulAut X)ᵐᵒᵖ b) (w : R.1.Fibre b) :
    blockFibreRadical R b (a • w) =
      (a : (MulAut X)ᵐᵒᵖ) • blockFibreRadical R b w := by
  unfold blockFibreRadical
  rw [CharacterWeight.LocalBlockInductionSource.fibre_smul_val,
    weightRadical_equivariant]

/-- The sector of a literal Brauer character, through its literal block. -/
def brauerSector (phi : IBr iota) : CentralSector (k := k) (X := X) :=
  blockSector (k := k) (X := X) (brauerBlock iota hinj blocks phi)

/-- The sector of a literal character weight, through its induced block. -/
def weightSector (w : WeightClass (p := p) (K := K) (X := X)) :
    CentralSector (k := k) (X := X) :=
  blockSector (k := k) (X := X) (R.1.weightBlock w)

/-- The literal Brauer-sector map commutes with automorphism transport. -/
theorem brauerSector_equivariant
    (_E1 : RoutineTransportInput iota hinj blocks R)
    (a : (MulAut X)ᵐᵒᵖ) (phi : IBr iota) :
    brauerSector iota hinj blocks (a • phi) =
      a • brauerSector iota hinj blocks phi := by
  unfold brauerSector
  rw [brauerBlock_transport, blockSector_transport]

theorem weightSector_equivariant_actual
    (_E1 : RoutineTransportInput iota hinj blocks R)
    (a : (MulAut X)ᵐᵒᵖ)
    (w : WeightClass (p := p) (K := K) (X := X)) :
    weightSector (R := R) (a • w) = a • weightSector (R := R) w := by
  unfold weightSector
  rw [R.1.weightBlock_transport, blockSector_transport]

end ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
