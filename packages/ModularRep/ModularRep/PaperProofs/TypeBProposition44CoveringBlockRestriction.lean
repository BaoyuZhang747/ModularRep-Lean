import ModularRep.PaperProofs.TypeBProposition44BroueMichelInstantiation
import Mathlib.GroupTheory.GroupAction.SubMulAction.OfStabilizer

/-!
# Restriction to the actual special Clifford blocks covering a Spin block

Covering is the nonzero product of the upstairs primitive idempotent with
the included downstairs primitive idempotent. The inclusion is the actual
Spin kernel inclusion. Tensor characters are trivial on this subgroup,
so the full tensor group stabilizes each covering-block set. The field
actor is the stabilizer of that set, which need not fix the Spin block.

The correspondence argument below is a K restriction of an already derived
global equivalence. Its argument is not an additional published source.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra Pointwise

namespace ModularRep.PaperProofs.TypeBProposition44CoveringBlockRestriction

open ModularRep FDRepSimpleClassKZero
open TypeBCliffordCarriers TypeCConformalActionAdapter TypeCWeightTensorFieldAction
open TypeBSpecialCliffordActionAdapter (brauerCharacterAction)

variable {p ell f n : ℕ} {F K k : Type}
variable [Field F] [Finite F] [CharP F p] [NeZero f] [Finite (Clifford n F)]
variable [Field k]
variable {parameters : OddFieldParameters F p f} (N : NormSource n F)
variable (fs : FieldActionSource n F p f parameters N)

local instance cliffordFintype : Fintype (SpecialClifford n F) := Fintype.ofFinite _

/-- The actual map of group algebras induced by the Spin inclusion. -/
def spinInclusion : k[Spin n F N] →+* k[SpecialClifford n F] :=
  MonoidAlgebra.mapDomainRingHom k (SpinSubgroup n F N).subtype

@[simp]
theorem spinInclusion_single (g : Spin n F N) (r : k) :
    spinInclusion N (MonoidAlgebra.single g r) = MonoidAlgebra.single g.val r :=
  MonoidAlgebra.mapDomain_single

/-- The standard primitive-idempotent formulation of covering. -/
def Covers (B : LiteralPrimitiveBlock k (SpecialClifford n F))
    (b : LiteralPrimitiveBlock k (Spin n F N)) : Prop :=
  B.val * spinInclusion N b.val ≠ 0

/-- The literal union index set, retaining the specified Spin block. -/
def coveringBlocks (b : LiteralPrimitiveBlock k (Spin n F N)) :
    Set (LiteralPrimitiveBlock k (SpecialClifford n F)) :=
  {B | Covers N B b}

/-- Forward transport on the actual downstairs primitive idempotent. -/
def spinBlockField (e : FieldGroup f) (b : LiteralPrimitiveBlock k (Spin n F N)) :
    LiteralPrimitiveBlock k (Spin n F N) :=
  let sigma := MonoidAlgebra.mapDomainRingEquiv k (spinFieldAction n F fs e)
  ⟨sigma b.val, b.property.mapRingEquiv sigma⟩

@[simp]
theorem spinBlockField_one (b : LiteralPrimitiveBlock k (Spin n F N)) :
    spinBlockField N fs 1 b = b := by
  apply Subtype.ext
  change MonoidAlgebra.mapDomainRingEquiv k (spinFieldAction n F fs 1) b.val = b.val
  rw [map_one]
  change MonoidAlgebra.mapDomain (id : Spin n F N → Spin n F N) b.val = b.val
  induction b.val using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [MonoidAlgebra.mapDomain_add, hx, hy]
  | single g r => exact MonoidAlgebra.mapDomain_single

/-- The specified algebra action commutes with the literal Spin inclusion;
the tensor factor disappears because it is trivial on the Spin kernel. -/
theorem sigma_spinInclusion
    (a : ActingGroup (k := k) (SpinSubgroup n F N) fs.action
      (field_spinSubgroup_map n F fs)) (z : k[Spin n F N]) :
    TypeBPhysicalBlockAction.sigma (SpinSubgroup n F N) fs.action
      (field_spinSubgroup_map n F fs) a (spinInclusion N z) =
    spinInclusion N
      (MonoidAlgebra.mapDomainRingEquiv k (spinFieldAction n F fs a.right) z) := by
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single g r =>
      have ht : a.left.val (fs.action a.right g.val) = 1 :=
        a.left.property (field_preserves_spin n F fs a.right g.val g.property)
      have hs := TypeBPhysicalBlockAction.sigma_single (SpinSubgroup n F N)
        fs.action (field_spinSubgroup_map n F fs) a g.val r
      exact (congrArg (TypeBPhysicalBlockAction.sigma (SpinSubgroup n F N)
        fs.action (field_spinSubgroup_map n F fs) a) (spinInclusion_single N g r)).trans
        (hs.trans (by simp only [ht, Units.val_one, mul_one,
          MonoidAlgebra.mapDomainRingEquiv_single, spinInclusion_single, spinFieldAction_coe]))

/-- Covering is transported by the actual tensor/field action upstairs
and the actual field action downstairs. -/
theorem covers_transport
    (a : ActingGroup (k := k) (SpinSubgroup n F N) fs.action
      (field_spinSubgroup_map n F fs))
    (B : LiteralPrimitiveBlock k (SpecialClifford n F))
    (b : LiteralPrimitiveBlock k (Spin n F N)) :
    Covers N (TypeBPhysicalBlockAction.blockTransport (SpinSubgroup n F N)
      fs.action (field_spinSubgroup_map n F fs) a B)
      (spinBlockField N fs a.right b) ↔ Covers N B b := by
  let sigma := TypeBPhysicalBlockAction.sigma (SpinSubgroup n F N) fs.action
    (field_spinSubgroup_map n F fs) a
  change sigma B.val * spinInclusion N
    (MonoidAlgebra.mapDomainRingEquiv k (spinFieldAction n F fs a.right) b.val) ≠ 0 ↔ _
  rw [← sigma_spinInclusion N fs a b.val]
  change sigma B.val * sigma (spinInclusion N b.val) ≠ 0 ↔ _
  rw [← map_mul]
  exact not_congr (sigma.injective.eq_iff' (map_zero sigma))

local instance actualBlockAction :
    MulAction (ActingGroup (k := k) (SpinSubgroup n F N) fs.action
      (field_spinSubgroup_map n F fs)) (LiteralPrimitiveBlock k (SpecialClifford n F)) :=
  TypeBPhysicalBlockAction.blockAction (SpinSubgroup n F N) fs.action
    (field_spinSubgroup_map n F fs)

/-- Stabilizer of the whole set of covering SC blocks. -/
def coveringStabilizer (b : LiteralPrimitiveBlock k (Spin n F N)) :
    Subgroup (ActingGroup (k := k) (SpinSubgroup n F N) fs.action
      (field_spinSubgroup_map n F fs)) :=
  MulAction.stabilizer _ (coveringBlocks N b)

theorem mem_coveringStabilizer_iff
    (b : LiteralPrimitiveBlock k (Spin n F N))
    (a : ActingGroup (k := k) (SpinSubgroup n F N) fs.action
      (field_spinSubgroup_map n F fs)) :
    a ∈ coveringStabilizer N fs b ↔
      ∀ B : LiteralPrimitiveBlock k (SpecialClifford n F), Covers N (a • B) b ↔ Covers N B b := by
  change a • coveringBlocks N b = coveringBlocks N b ↔ _
  constructor
  · intro h B
    have hm := Set.smul_mem_smul_set_iff (a := a) (x := B) (s := coveringBlocks N b)
    rw [h] at hm
    exact hm
  · intro h
    apply Set.ext
    intro B
    constructor
    · rintro ⟨C, hC, rfl⟩
      exact (h C).mpr hC
    · intro hB
      refine ⟨a⁻¹ • B, (h (a⁻¹ • B)).mp ?_, ?_⟩
      · simpa only [smul_inv_smul] using (show Covers N B b from hB)
      · exact smul_inv_smul a B

theorem tensor_mem_coveringStabilizer
    (b : LiteralPrimitiveBlock k (Spin n F N))
    (c : TensorCharacters (k := k) (SpinSubgroup n F N)) :
    SemidirectProduct.inl c ∈ coveringStabilizer N fs b := by
  apply (mem_coveringStabilizer_iff N fs b _).mpr
  intro B
  let a : ActingGroup (k := k) (SpinSubgroup n F N) fs.action
    (field_spinSubgroup_map n F fs) := SemidirectProduct.inl c
  have ht : Covers N (TypeBPhysicalBlockAction.blockTransport (SpinSubgroup n F N)
      fs.action (field_spinSubgroup_map n F fs) a B) (spinBlockField N fs 1 b) ↔
      Covers N B b := covers_transport N fs a B b
  exact (congrArg (fun b' => Covers N
    (TypeBPhysicalBlockAction.blockTransport (SpinSubgroup n F N)
      fs.action (field_spinSubgroup_map n F fs) a B) b' ↔ Covers N B b)
    (spinBlockField_one N fs b)).mp ht

/-- The exact field subgroup stabilizing the covering-block SET. -/
def coveringFieldStabilizer (b : LiteralPrimitiveBlock k (Spin n F N)) :
    Subgroup (FieldGroup f) :=
  (coveringStabilizer N fs b).comap SemidirectProduct.inr

/-- Membership is precisely unrestricted tensor part and field part in
the covering-set stabilizer. No equality with the Spin-block stabilizer is used. -/
theorem mem_coveringStabilizer_iff_right
    (b : LiteralPrimitiveBlock k (Spin n F N))
    (a : ActingGroup (k := k) (SpinSubgroup n F N) fs.action
      (field_spinSubgroup_map n F fs)) :
    a ∈ coveringStabilizer N fs b ↔ a.right ∈ coveringFieldStabilizer N fs b := by
  change a ∈ coveringStabilizer N fs b ↔
    SemidirectProduct.inr a.right ∈ coveringStabilizer N fs b
  exact (congrArg (fun x : ActingGroup (k := k) (SpinSubgroup n F N) fs.action
      (field_spinSubgroup_map n F fs) => x ∈ coveringStabilizer N fs b)
    (SemidirectProduct.mk_eq_inl_mul_inr a.right a.left)).to_iff.trans
      ((coveringStabilizer N fs b).mul_mem_cancel_left
        (tensor_mem_coveringStabilizer N fs b a.left))

section Correspondence

variable [Field K] [CharZero K] [CharP k ell] [IsAlgClosed k]
variable [Fintype (LiteralPrimitiveBlock k (SpecialClifford n F))]
variable (iota : PrimeRegularRootEmbedding ell k K (SpecialClifford n F))
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition
  (fun B : LiteralPrimitiveBlock k (SpecialClifford n F) => B.val))
variable (productFormula : BrauerLinearTensorProductFormula iota)
variable (D : OrdinaryReductionEquiv (k := k) (K := K)
  (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs))
variable (radicalKernel : RadicalKernelLiftInput (p := ell)
  (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D)
variable (blockSource : CharacterWeight.LocalBlockInductionSource
  (p := ell) (k := k) (K := K) (G := SpecialClifford n F)
  (Block := LiteralPrimitiveBlock k (SpecialClifford n F)))

@[instance_reducible]
def actualBrauerAction :
    MulAction (ActingGroup (k := k) (SpinSubgroup n F N) fs.action
      (field_spinSubgroup_map n F fs)) (IBr iota) :=
  brauerCharacterAction (SpinSubgroup n F N) fs.action
    (field_spinSubgroup_map n F fs) iota productFormula

@[instance_reducible]
def actualWeightAction :
    MulAction (ActingGroup (k := k) (SpinSubgroup n F N) fs.action
      (field_spinSubgroup_map n F fs))
      (CharacterWeight.ConjugacyClass (p := ell) (K := K) (G := SpecialClifford n F)) :=
  tensorFieldSemidirectAction (SpinSubgroup n F N) fs.action
    (field_spinSubgroup_map n F fs) D radicalKernel

/-- The actual union of Brauer characters in the covering SC blocks. -/
def brauerCoveringDomain (b : LiteralPrimitiveBlock k (Spin n F N)) :=
  {phi : IBr iota // Covers N (irreducibleBrauerCharacterBlock iota hinj blocks phi) b}

/-- The actual union of weight classes in the same covering SC blocks. -/
def weightCoveringDomain (b : LiteralPrimitiveBlock k (Spin n F N)) :=
  {W : CharacterWeight.ConjugacyClass (p := ell) (K := K) (G := SpecialClifford n F) //
    Covers N (blockSource.weightBlock W) b}

variable (derivedGlobal : IBr iota ≃
  CharacterWeight.ConjugacyClass (p := ell) (K := K) (G := SpecialClifford n F))
variable (derivedBlock : ∀ phi, blockSource.weightBlock (derivedGlobal phi) =
  irreducibleBrauerCharacterBlock iota hinj blocks phi)

/-- Restrict an already derived global map by its specified block equality. -/
def restrict (b : LiteralPrimitiveBlock k (Spin n F N)) :
    brauerCoveringDomain N iota hinj blocks b ≃ weightCoveringDomain N blockSource b :=
  derivedGlobal.subtypeEquiv (fun phi => by rw [derivedBlock phi])

@[simp]
theorem restrict_apply (b : LiteralPrimitiveBlock k (Spin n F N))
    (phi : brauerCoveringDomain N iota hinj blocks b) :
    (restrict N iota hinj blocks blockSource derivedGlobal derivedBlock b phi).val =
      derivedGlobal phi.val := rfl

/-- Restriction preserves each individual upstairs block, not only its union. -/
theorem restrict_block (b : LiteralPrimitiveBlock k (Spin n F N))
    (phi : brauerCoveringDomain N iota hinj blocks b) :
    blockSource.weightBlock
      (restrict N iota hinj blocks blockSource derivedGlobal derivedBlock b phi).val =
      irreducibleBrauerCharacterBlock iota hinj blocks phi.val :=
  derivedBlock phi.val


/-- The covering-union Brauer subtype carries the actual set stabilizer. -/
@[instance_reducible]
def brauerCoveringAction (b : LiteralPrimitiveBlock k (Spin n F N)) :
    MulAction (coveringStabilizer N fs b) (brauerCoveringDomain N iota hinj blocks b) := by
  letI := actualBrauerAction N fs iota productFormula
  refine { smul := fun a phi => ⟨a.val • phi.val, ?_⟩
           one_smul := fun phi => Subtype.ext (one_smul _ _)
           mul_smul := fun a d phi => Subtype.ext (mul_smul a.val d.val phi.val) }
  have hBlock := TypeBPhysicalBlockAction.brauerBlockEquivariant
    (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs)
    iota productFormula hinj blocks a.val phi.val
  exact (congrArg (fun B => Covers N B b) hBlock).mpr
    (((mem_coveringStabilizer_iff N fs b a.val).mp a.property
      (irreducibleBrauerCharacterBlock iota hinj blocks phi.val)).mpr phi.property)

variable (derivedEquivariant :
  letI := actualBrauerAction N fs iota productFormula
  letI := actualWeightAction N fs D radicalKernel
  ∀ (a : ActingGroup (k := k) (SpinSubgroup n F N) fs.action
      (field_spinSubgroup_map n F fs)) (phi : IBr iota),
    derivedGlobal (a • phi) = a • derivedGlobal phi)

include derivedBlock derivedEquivariant in
/-- Weight-block equivariance follows from the checked global correspondence
and its surjectivity; it is not a new local-block source. -/
theorem weightBlock_equivariant :
    letI := actualWeightAction N fs D radicalKernel
    ∀ (a : ActingGroup (k := k) (SpinSubgroup n F N) fs.action
      (field_spinSubgroup_map n F fs))
      (W : CharacterWeight.ConjugacyClass (p := ell) (K := K) (G := SpecialClifford n F)),
      blockSource.weightBlock (a • W) = a • blockSource.weightBlock W := by
  letI := actualBrauerAction N fs iota productFormula
  letI := actualWeightAction N fs D radicalKernel
  intro a W
  obtain ⟨phi, rfl⟩ := derivedGlobal.surjective W
  exact (congrArg blockSource.weightBlock (derivedEquivariant a phi).symm).trans
    ((derivedBlock (a • phi)).trans
      ((TypeBPhysicalBlockAction.brauerBlockEquivariant (SpinSubgroup n F N)
        fs.action (field_spinSubgroup_map n F fs) iota productFormula hinj blocks a phi).trans
        (congrArg (fun B : LiteralPrimitiveBlock k (SpecialClifford n F) => a • B)
          (derivedBlock phi).symm)))

/-- The weight union inherits exactly the same stabilizer action. -/
@[instance_reducible]
def weightCoveringAction (b : LiteralPrimitiveBlock k (Spin n F N)) :
    MulAction (coveringStabilizer N fs b) (weightCoveringDomain N blockSource b) := by
  letI := actualWeightAction N fs D radicalKernel
  refine { smul := fun a W => ⟨a.val • W.val, ?_⟩
           one_smul := fun W => Subtype.ext (one_smul _ _)
           mul_smul := fun a d W => Subtype.ext (mul_smul a.val d.val W.val) }
  have hBlock := weightBlock_equivariant N fs iota hinj blocks productFormula D radicalKernel
    blockSource derivedGlobal derivedBlock derivedEquivariant a.val W.val
  exact (congrArg (fun B => Covers N B b) hBlock).mpr
    (((mem_coveringStabilizer_iff N fs b a.val).mp a.property
      (blockSource.weightBlock W.val)).mpr W.property)

/-- The restricted equivalence is equivariant for the FULL covering-set
stabilizer. Its action on each value is inherited from the global action. -/
theorem restrict_equivariant (b : LiteralPrimitiveBlock k (Spin n F N)) :
    letI := brauerCoveringAction N fs iota hinj blocks productFormula b
    letI := weightCoveringAction N fs iota hinj blocks productFormula D radicalKernel
      blockSource derivedGlobal derivedBlock derivedEquivariant b
    ∀ (a : coveringStabilizer N fs b) (phi : brauerCoveringDomain N iota hinj blocks b),
      restrict N iota hinj blocks blockSource derivedGlobal derivedBlock b (a • phi) =
        a • restrict N iota hinj blocks blockSource derivedGlobal derivedBlock b phi := by
  letI := brauerCoveringAction N fs iota hinj blocks productFormula b
  letI := weightCoveringAction N fs iota hinj blocks productFormula D radicalKernel
    blockSource derivedGlobal derivedBlock derivedEquivariant b
  intro a phi
  exact Subtype.ext (derivedEquivariant a.val phi.val)

end Correspondence
end ModularRep.PaperProofs.TypeBProposition44CoveringBlockRestriction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
