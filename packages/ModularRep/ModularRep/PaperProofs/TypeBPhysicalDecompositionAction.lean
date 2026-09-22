import ModularRep.PaperProofs.TypeBOrdinaryBlockSplitting
import ModularRep.PaperProofs.TypeBSpecialCliffordActionSplitting

/-!
# Specified decomposition rows under the actual tensor and field action

The actual stable-reduction row is transported using the existing exact
reduction naturality and the ordinary/Brauer simple-generator equations.
Nonzero constituents then determine the same specified ordinary block.
No decomposition matrix, blockwise support or equivariance source is added.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBPhysicalDecompositionAction

open ModularRep ExactGrothendieckGroup FDRepSimpleClassKZero
open FDRepJordanHolderKZero OrdinaryIrreducibleCharacter
open TypeBOrdinaryLabelSplitting TypeBOrdinaryBlockSplitting
open TypeBSpinPrincipalDecompositionBinding (brauerCoordinates brauerCoordinates_simple)
open TypeCConformalActionAdapter
open TypeBSpecialCliffordActionAdapter
  (ordinaryCharacterAction brauerCharacterAction ordinaryKZeroAction modularKZeroAction
    OrdinaryLiftReductionCompatible)

universe u

variable {p : ℕ} {K O k G E : Type u}
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharZero K] [CharP k p] [IsAlgClosed k]
  [Group G] [Finite G] [Group E]
  (G0 : Subgroup G) [G0.Normal]
  (field : E →* MulAut G)
  (hinvariant : FieldInvariantSubgroup.IsInvariant G0 field)
  (D : OrdinaryReductionEquiv (k := k) (K := K) G0 field hinvariant)
  (Msys : ModularSystem p K O k)
  (iota : PrimeRegularRootEmbedding p k K G)
  (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
  (hinj : IrreducibleBrauerCharacterInjectivity iota)
  (productFormula : BrauerLinearTensorProductFormula iota)
  (hlift : OrdinaryLiftReductionCompatible G0 field hinvariant D iota)

include hinj in
/-- The exact modular action permutes the actual simple-factor coordinates. -/
theorem brauerCoordinates_action
    (a : ActingGroup (k := k) G0 field hinvariant) (x : FDRepKZero k G) :
    let _ : MulAction (ActingGroup (k := k) G0 field hinvariant) (IBr iota) :=
      brauerCharacterAction G0 field hinvariant iota productFormula
    brauerCoordinates iota (modularKZeroAction (k := k) G0 field hinvariant a x) =
      Finsupp.equivMapDomain (MulAction.toPerm a) (brauerCoordinates iota x) := by
  dsimp only
  letI := brauerCharacterAction G0 field hinvariant iota productFormula
  let left : FDRepKZero k G →+ (IBr iota →₀ ℤ) :=
    (brauerCoordinates iota).comp
      (modularKZeroAction (k := k) G0 field hinvariant a).toAddMonoidHom
  let right : FDRepKZero k G →+ (IBr iota →₀ ℤ) :=
    (Finsupp.domCongr (MulAction.toPerm a)).toAddMonoidHom.comp
      (brauerCoordinates iota)
  have h : left.comp simpleClassToFDRepKZero =
      right.comp simpleClassToFDRepKZero := by
    apply FreeAbelianGroup.lift_ext
    intro X
    let phi : IBr iota := simpleClassToIBr iota X
    have hphi : (simpleModuleClassEquivIBr iota hinj).symm phi = X :=
      (simpleModuleClassEquivIBr iota hinj).symm_apply_apply X
    have ha := TypeBSpecialCliffordActionSplitting.brauerLabel_action
      G0 field hinvariant iota hinj productFormula a phi
    dsimp only at ha
    rw [hphi] at ha
    change brauerCoordinates iota
        (modularKZeroAction (k := k) G0 field hinvariant a
          (simpleClassToFDRepKZeroGenerator X)) =
      Finsupp.equivMapDomain (MulAction.toPerm a)
        (brauerCoordinates iota (simpleClassToFDRepKZeroGenerator X))
    rw [← ha, brauerCoordinates_simple, brauerCoordinates_simple,
      Finsupp.equivMapDomain_single]
    congr 1
    exact (simpleModuleClassEquivIBr iota hinj).apply_symm_apply (a • phi)
  calc
    brauerCoordinates iota (modularKZeroAction (k := k) G0 field hinvariant a x) =
        left (simpleClassToFDRepKZero (fdRepSimpleJordanHolderHom x)) := by
      rw [simpleClassToFDRepKZero_fdRepSimpleJordanHolderHom]
      rfl
    _ = right (simpleClassToFDRepKZero (fdRepSimpleJordanHolderHom x)) :=
      congrArg (fun f => f (fdRepSimpleJordanHolderHom x)) h
    _ = Finsupp.equivMapDomain (MulAction.toPerm a) (brauerCoordinates iota x) := by
      rw [simpleClassToFDRepKZero_fdRepSimpleJordanHolderHom]
      rfl

/-- The specified row uses the same ordinary simple generator as the action. -/
theorem decompositionRow_label (chi : Irr K G) :
    decompositionRow Msys iota chi = brauerCoordinates iota
      (decompositionMapOfStableReduction Msys iota hcompat
        (simpleClassToFDRepKZeroGenerator (ordinaryLabel chi))) := by
  rw [decompositionRow_exact Msys iota hcompat]
  have hlabel : simpleClassToFDRepKZeroGenerator (ordinaryLabel chi) =
      classOf (FDRep K G) (representation chi) :=
    classOf_iso (FDRep K G)
      (simpleClassOfIrreducibleFDRepIso (representation chi)
        (representation_irreducible chi))
  rw [hlabel]

include hcompat hinj hlift in
/-- Exact row naturality for the SAME tensor lift, field and modular root. -/
theorem decompositionRow_action
    (a : ActingGroup (k := k) G0 field hinvariant) (chi : Irr K G) :
    let _ : MulAction (ActingGroup (k := k) G0 field hinvariant) (Irr K G) :=
      ordinaryCharacterAction G0 field hinvariant D
    let _ : MulAction (ActingGroup (k := k) G0 field hinvariant) (IBr iota) :=
      brauerCharacterAction G0 field hinvariant iota productFormula
    decompositionRow Msys iota (a • chi) =
      Finsupp.equivMapDomain (MulAction.toPerm a) (decompositionRow Msys iota chi) := by
  dsimp only
  letI := ordinaryCharacterAction G0 field hinvariant D
  letI := brauerCharacterAction G0 field hinvariant iota productFormula
  rw [decompositionRow_label Msys iota hcompat,
    decompositionRow_label Msys iota hcompat]
  rw [TypeBSpecialCliffordActionSplitting.ordinaryLabel_action G0 field hinvariant D]
  rw [TypeBSpecialCliffordActionSplitting.decompositionNatural
    G0 field hinvariant D Msys iota hcompat productFormula hlift]
  exact brauerCoordinates_action G0 field hinvariant iota hinj productFormula a _

include hcompat hinj hlift in
/-- The actual natural decomposition numbers are invariant on transported labels. -/
theorem decompositionNumber_action
    (a : ActingGroup (k := k) G0 field hinvariant) (chi : Irr K G) (phi : IBr iota) :
    let _ : MulAction (ActingGroup (k := k) G0 field hinvariant) (Irr K G) :=
      ordinaryCharacterAction G0 field hinvariant D
    let _ : MulAction (ActingGroup (k := k) G0 field hinvariant) (IBr iota) :=
      brauerCharacterAction G0 field hinvariant iota productFormula
    decompositionNumber Msys iota (a • chi) (a • phi) =
      decompositionNumber Msys iota chi phi := by
  dsimp only
  letI := ordinaryCharacterAction G0 field hinvariant D
  letI := brauerCharacterAction G0 field hinvariant iota productFormula
  unfold decompositionNumber
  rw [decompositionRow_action G0 field hinvariant D Msys iota hcompat hinj
    productFormula hlift]
  exact congrArg Int.toNat
    (show Finsupp.equivMapDomain (MulAction.toPerm a)
      (decompositionRow Msys iota chi) ((MulAction.toPerm a) phi) = _ by
        simp only [Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply])

variable [Fintype (LiteralPrimitiveBlock k G)]
  [MulAction (ActingGroup (k := k) G0 field hinvariant) (LiteralPrimitiveBlock k G)]
  (blocks : BlockIdempotentDecomposition (fun b : LiteralPrimitiveBlock k G => b.val))
  [HasEnoughRootsOfUnity K (Nat.card G)]
  (ordinary : OrdinaryBlockSource Msys iota hinj blocks)

include hcompat hlift in
/-- Specified ordinary-block equivariance is determined by a nonzero constituent
and the actual Brauer-block transport. It is not an additional source field. -/
theorem ordinaryBlock_equivariant_of_brauer
    (hBrBlock : BrauerBlockEquivariant G0 field hinvariant iota productFormula
      (irreducibleBrauerCharacterBlock iota hinj blocks)) :
    OrdinaryBlockEquivariant G0 field hinvariant D ordinary.physical.ordinaryBlock := by
  letI := ordinaryCharacterAction G0 field hinvariant D
  letI := brauerCharacterAction G0 field hinvariant iota productFormula
  intro a chi
  obtain ⟨phi, hphi⟩ := (ordinary.physical.support_nonempty_and_sound chi).1
  have hn : decompositionNumber Msys iota (a • chi) (a • phi) ≠ 0 := by
    rw [decompositionNumber_action G0 field hinvariant D Msys iota hcompat hinj
      productFormula hlift]
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
    ordinary.physical.ordinaryBlock (a • chi) =
        irreducibleBrauerCharacterBlock iota hinj blocks (a • phi) :=
      (block_of_nonzero_row Msys iota hinj blocks ordinary _ _
        (row_nonzero _ _ hn)).symm
    _ = a • irreducibleBrauerCharacterBlock iota hinj blocks phi := hBrBlock a phi
    _ = a • ordinary.physical.ordinaryBlock chi :=
      congrArg (fun b : LiteralPrimitiveBlock k G => a • b)
        (block_of_nonzero_row Msys iota hinj blocks ordinary _ _
          (row_nonzero _ _ hphi))

end ModularRep.PaperProofs.TypeBPhysicalDecompositionAction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
