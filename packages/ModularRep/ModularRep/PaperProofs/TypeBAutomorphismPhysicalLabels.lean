import ModularRep.PaperProofs.TypeBPhysicalDecompositionAction
import ModularRep.IBrBlockAutomorphism

/-!
# Actual automorphism transport of specified labels and blocks

The ordinary and Brauer simple generators use the existing literal labels.
Their pullback equations determine the stable-reduction coordinates and the
specified ordinary block through a nonzero actual constituent. No tensor
formula, block-equivariance source or ordinary algebraic closure is supplied.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBAutomorphismPhysicalLabels

open ModularRep ExactGrothendieckGroup FDRepSimpleClassKZero
open FDRepJordanHolderKZero OrdinaryIrreducibleCharacter
open TypeBOrdinaryLabelSplitting TypeBOrdinaryBlockSplitting
open TypeBSpinPrincipalDecompositionBinding (brauerCoordinates brauerCoordinates_simple)

universe u

section Ordinary

variable {K G : Type u} [Field K] [CharZero K] [Group G] [Finite G]

/-- Pure ordinary pullback is the corresponding exact simple-generator twist. -/
theorem ordinaryLabel_twist (chi : Irr K G) (alpha : MulAut G) :
    simpleClassToFDRepKZeroGenerator
        (ordinaryLabel (OrdinaryIrreducibleCharacter.twist K G chi alpha)) =
      twistKZero (k := K) alpha
        (simpleClassToFDRepKZeroGenerator (ordinaryLabel chi)) := by
  simpa only [OrdinaryIrreducibleCharacter.linearTwist_one,
    linearCharacterTwistKZero_one, AddMonoidHom.id_apply] using
    TypeBSpecialCliffordActionSplitting.ordinaryLabel_linearTwist_twist
      chi alpha (1 : G →* Kˣ)

end Ordinary

variable {p : ℕ} {K k G : Type u}
  [Field K] [Field k] [CharZero K] [CharP k p] [IsAlgClosed k]
  [Group G] [Finite G]
  (iota : PrimeRegularRootEmbedding p k K G)
  (hinj : IrreducibleBrauerCharacterInjectivity iota)

/-- The chosen simple label has exactly the prescribed Brauer character. -/
theorem brauer_generator_value (phi : IBr iota) :
    brauerCharacterKZeroHom iota
        (simpleClassToFDRepKZeroGenerator
          ((simpleModuleClassEquivIBr iota hinj).symm phi)) = phi.val := by
  rw [simpleClassToFDRepKZeroGenerator, brauerCharacterKZeroHom_classOf]
  exact congrArg Subtype.val ((simpleModuleClassEquivIBr iota hinj).apply_symm_apply phi)

/-- Pure Brauer pullback agrees with the exact simple-generator twist. -/
theorem brauerLabel_twist (phi : IBr iota) (alpha : MulAut G) :
    simpleClassToFDRepKZeroGenerator
        ((simpleModuleClassEquivIBr iota hinj).symm
          (IrreducibleBrauerCharacter.twist iota phi alpha)) =
      twistKZero (k := k) alpha
        (simpleClassToFDRepKZeroGenerator
          ((simpleModuleClassEquivIBr iota hinj).symm phi)) := by
  apply brauerCharacterKZeroHom_injective iota
  rw [brauer_generator_value]
  have h := DFunLike.congr_fun (brauerCharacterKZeroHom_twist iota alpha)
    (simpleClassToFDRepKZeroGenerator
      ((simpleModuleClassEquivIBr iota hinj).symm phi))
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply] at h
  rw [brauer_generator_value] at h
  exact h.symm

include hinj in
/-- Automorphism pullback permutes the actual Jordan--Holder coordinates. -/
theorem brauerCoordinates_twist (alpha : MulAut G) (x : FDRepKZero k G) :
    brauerCoordinates iota (twistKZero (k := k) alpha x) =
      Finsupp.equivMapDomain
        (MulAction.toPerm (MulOpposite.op alpha)) (brauerCoordinates iota x) := by
  let perm : Equiv.Perm (IBr iota) := MulAction.toPerm (MulOpposite.op alpha)
  let left : FDRepKZero k G →+ (IBr iota →₀ ℤ) :=
    (brauerCoordinates iota).comp (twistKZero (k := k) alpha)
  let right : FDRepKZero k G →+ (IBr iota →₀ ℤ) :=
    (Finsupp.domCongr perm).toAddMonoidHom.comp (brauerCoordinates iota)
  have h : left.comp simpleClassToFDRepKZero =
      right.comp simpleClassToFDRepKZero := by
    apply FreeAbelianGroup.lift_ext
    intro X
    let phi : IBr iota := simpleClassToIBr iota X
    have hphi : (simpleModuleClassEquivIBr iota hinj).symm phi = X :=
      (simpleModuleClassEquivIBr iota hinj).symm_apply_apply X
    have ha := brauerLabel_twist iota hinj phi alpha
    rw [hphi] at ha
    change brauerCoordinates iota
        (twistKZero (k := k) alpha (simpleClassToFDRepKZeroGenerator X)) =
      Finsupp.equivMapDomain perm
        (brauerCoordinates iota (simpleClassToFDRepKZeroGenerator X))
    rw [← ha, brauerCoordinates_simple, brauerCoordinates_simple,
      Finsupp.equivMapDomain_single]
    congr 1
    exact (simpleModuleClassEquivIBr iota hinj).apply_symm_apply
      (IrreducibleBrauerCharacter.twist iota phi alpha)
  calc
    brauerCoordinates iota (twistKZero (k := k) alpha x) =
        left (simpleClassToFDRepKZero (fdRepSimpleJordanHolderHom x)) := by
      rw [simpleClassToFDRepKZero_fdRepSimpleJordanHolderHom]
      rfl
    _ = right (simpleClassToFDRepKZero (fdRepSimpleJordanHolderHom x)) :=
      congrArg (fun f => f (fdRepSimpleJordanHolderHom x)) h
    _ = Finsupp.equivMapDomain
        (MulAction.toPerm (MulOpposite.op alpha)) (brauerCoordinates iota x) := by
      rw [simpleClassToFDRepKZero_fdRepSimpleJordanHolderHom]
      rfl

section Blocks

variable [Fintype (LiteralPrimitiveBlock k G)]
  (blocks : BlockIdempotentDecomposition (fun b : LiteralPrimitiveBlock k G => b.val))

/-- The literal catalogue labels an idempotent by that same idempotent. -/
theorem primitiveBlockOfIndex_eq (b : LiteralPrimitiveBlock k G) :
    blocks.primitiveBlockOfIndex b = b := by
  apply Subtype.ext
  rfl

/-- Brauer pullback transports its actual primitive block by inverse algebra pullback. -/
theorem brauerBlock_twist (phi : IBr iota) (alpha : MulAut G) :
    irreducibleBrauerCharacterBlock iota hinj blocks
        (IrreducibleBrauerCharacter.twist iota phi alpha) =
      LiteralPrimitiveBlock.rightTwistBlock
        (irreducibleBrauerCharacterBlock iota hinj blocks phi) alpha := by
  have h := primitiveBlockOfIndex_irreducibleBrauerCharacterBlock_op_smul
    iota hinj blocks (MulOpposite.op alpha) phi
  rw [primitiveBlockOfIndex_eq, primitiveBlockOfIndex_eq] at h
  exact h

end Blocks

section Reduction

variable {O : Type u} [CommRing O] [IsDomain O] [Algebra O K]
  (Msys : ModularSystem p K O k)
  (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)

include hcompat hinj in
/-- The actual stable-lattice row is transported by the same label permutation. -/
theorem decompositionRow_twist (alpha : MulAut G) (chi : Irr K G) :
    decompositionRow Msys iota (OrdinaryIrreducibleCharacter.twist K G chi alpha) =
      Finsupp.equivMapDomain
        (MulAction.toPerm (MulOpposite.op alpha)) (decompositionRow Msys iota chi) := by
  rw [TypeBPhysicalDecompositionAction.decompositionRow_label Msys iota hcompat,
    TypeBPhysicalDecompositionAction.decompositionRow_label Msys iota hcompat]
  rw [ordinaryLabel_twist, decompositionMapOfStableReduction_twist]
  exact brauerCoordinates_twist iota hinj alpha _

include hcompat hinj in
/-- The actual natural decomposition number is invariant on both pulled-back labels. -/
theorem decompositionNumber_twist (alpha : MulAut G) (chi : Irr K G) (phi : IBr iota) :
    decompositionNumber Msys iota
        (OrdinaryIrreducibleCharacter.twist K G chi alpha)
        (IrreducibleBrauerCharacter.twist iota phi alpha) =
      decompositionNumber Msys iota chi phi := by
  unfold decompositionNumber
  rw [decompositionRow_twist iota hinj Msys hcompat]
  exact congrArg Int.toNat
    (show Finsupp.equivMapDomain (MulAction.toPerm (MulOpposite.op alpha))
      (decompositionRow Msys iota chi)
      ((MulAction.toPerm (MulOpposite.op alpha)) phi) = _ by
        simp only [Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply])

variable [Fintype (LiteralPrimitiveBlock k G)]
  (blocks : BlockIdempotentDecomposition (fun b : LiteralPrimitiveBlock k G => b.val))
  [HasEnoughRootsOfUnity K (Nat.card G)]
  (ordinary : OrdinaryBlockSource Msys iota hinj blocks)

include hcompat in
/-- A nonzero specified constituent determines ordinary-block pullback. -/
theorem ordinaryBlock_twist (chi : Irr K G) (alpha : MulAut G) :
    ordinary.physical.ordinaryBlock (OrdinaryIrreducibleCharacter.twist K G chi alpha) =
      LiteralPrimitiveBlock.rightTwistBlock (ordinary.physical.ordinaryBlock chi) alpha := by
  obtain ⟨phi, hphi⟩ := (ordinary.physical.support_nonempty_and_sound chi).1
  have hn : decompositionNumber Msys iota
      (OrdinaryIrreducibleCharacter.twist K G chi alpha)
      (IrreducibleBrauerCharacter.twist iota phi alpha) ≠ 0 := by
    rw [decompositionNumber_twist iota hinj Msys hcompat]
    exact hphi
  have row_nonzero : ∀ (chi : Irr K G) (phi : IBr iota),
      decompositionNumber Msys iota chi phi ≠ 0 →
      decompositionRow Msys iota chi phi ≠ 0 := by
    intro chi phi h hzero
    apply h
    unfold decompositionNumber
    rw [hzero]
    rfl
  calc
    ordinary.physical.ordinaryBlock (OrdinaryIrreducibleCharacter.twist K G chi alpha) =
        irreducibleBrauerCharacterBlock iota hinj blocks
          (IrreducibleBrauerCharacter.twist iota phi alpha) :=
      (block_of_nonzero_row Msys iota hinj blocks ordinary _ _
        (row_nonzero _ _ hn)).symm
    _ = LiteralPrimitiveBlock.rightTwistBlock
        (irreducibleBrauerCharacterBlock iota hinj blocks phi) alpha :=
      brauerBlock_twist iota hinj blocks phi alpha
    _ = LiteralPrimitiveBlock.rightTwistBlock (ordinary.physical.ordinaryBlock chi) alpha :=
      congrArg (fun b : LiteralPrimitiveBlock k G =>
        LiteralPrimitiveBlock.rightTwistBlock b alpha)
        (block_of_nonzero_row Msys iota hinj blocks ordinary _ _
          (row_nonzero _ _ hphi))

end Reduction

end ModularRep.PaperProofs.TypeBAutomorphismPhysicalLabels


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
