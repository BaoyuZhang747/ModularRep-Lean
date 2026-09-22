import ModularRep.DecompositionBasicSetBridge

open scoped MonoidAlgebra

namespace ModularRep.BlockFibreRestriction

open ExactGrothendieckGroup
open FDRepSimpleClassKZero
open DecompositionBasicSetBridge

universe u

variable {X Y I : Type u}

def blockFibreSet (block : X → I) (i : I) : Set X :=
  {x | block x = i}

abbrev BlockFibre (block : X → I) (i : I) :=
  blockFibreSet block i

noncomputable def supportedEquivMonoidAlgebra (s : Set X) :
    MonoidAlgebra.supported ℤ ℤ s ≃ₗ[ℤ] MonoidAlgebra ℤ s :=
  (MonoidAlgebra.supportedEquivFinsupp (R := ℤ) (S := ℤ) s).trans
    (MonoidAlgebra.coeffLinearEquiv ℤ).symm

structure BlockDiagonalLinearEquiv
    (blockX : X → I) (blockY : Y → I)
    (d : MonoidAlgebra ℤ X ≃ₗ[ℤ] MonoidAlgebra ℤ Y) : Prop where
  map_supported : ∀ (i : I) (v : MonoidAlgebra ℤ X),
    v ∈ MonoidAlgebra.supported ℤ ℤ (blockFibreSet blockX i) →
      d v ∈ MonoidAlgebra.supported ℤ ℤ (blockFibreSet blockY i)
  symm_map_supported : ∀ (i : I) (v : MonoidAlgebra ℤ Y),
    v ∈ MonoidAlgebra.supported ℤ ℤ (blockFibreSet blockY i) →
      d.symm v ∈ MonoidAlgebra.supported ℤ ℤ (blockFibreSet blockX i)

noncomputable def restrictSupportedLinearEquiv
    (blockX : X → I) (blockY : Y → I)
    (d : MonoidAlgebra ℤ X ≃ₗ[ℤ] MonoidAlgebra ℤ Y)
    (hd : BlockDiagonalLinearEquiv blockX blockY d) (i : I) :
    MonoidAlgebra.supported ℤ ℤ (blockFibreSet blockX i) ≃ₗ[ℤ]
      MonoidAlgebra.supported ℤ ℤ (blockFibreSet blockY i) where
  toFun v := ⟨d v.1, hd.map_supported i v.1 v.2⟩
  invFun v := ⟨d.symm v.1, hd.symm_map_supported i v.1 v.2⟩
  left_inv v := by
    apply Subtype.ext
    exact d.symm_apply_apply v.1
  right_inv v := by
    apply Subtype.ext
    exact d.apply_symm_apply v.1
  map_add' x y := by
    apply Subtype.ext
    exact d.map_add x.1 y.1
  map_smul' n x := by
    apply Subtype.ext
    exact d.map_smul n x.1

noncomputable def restrictBlockLinearEquiv
    (blockX : X → I) (blockY : Y → I)
    (d : MonoidAlgebra ℤ X ≃ₗ[ℤ] MonoidAlgebra ℤ Y)
    (hd : BlockDiagonalLinearEquiv blockX blockY d) (i : I) :
    MonoidAlgebra ℤ (BlockFibre blockX i) ≃ₗ[ℤ]
      MonoidAlgebra ℤ (BlockFibre blockY i) :=
  (supportedEquivMonoidAlgebra (blockFibreSet blockX i)).symm |>.trans
    (restrictSupportedLinearEquiv blockX blockY d hd i) |>.trans
      (supportedEquivMonoidAlgebra (blockFibreSet blockY i))

noncomputable def blockFibreInclusion
    (block : X → I) (i : I) :
    MonoidAlgebra ℤ (BlockFibre block i) →ₗ[ℤ] MonoidAlgebra ℤ X :=
  (Submodule.subtype
      (MonoidAlgebra.supported ℤ ℤ (blockFibreSet block i))).comp
    (supportedEquivMonoidAlgebra (blockFibreSet block i)).symm.toLinearMap

theorem blockFibreInclusion_injective
    (block : X → I) (i : I) :
    Function.Injective (blockFibreInclusion block i) := by
  intro x y hxy
  apply (supportedEquivMonoidAlgebra
    (blockFibreSet block i)).symm.injective
  apply Subtype.val_injective
  exact hxy

@[simp]
theorem blockFibreInclusion_single
    (block : X → I) (i : I) (x : BlockFibre block i) :
    blockFibreInclusion block i (MonoidAlgebra.single x 1) =
      MonoidAlgebra.single x.1 1 := by
  apply MonoidAlgebra.coeff_injective
  change
    (((Finsupp.supportedEquivFinsupp
        (M := ℤ) (R := ℤ) (blockFibreSet block i)).symm
      (Finsupp.single x 1) : X →₀ ℤ)) =
        Finsupp.single x.1 1
  exact Finsupp.supportedEquivFinsupp_symm_single
    (M := ℤ) (R := ℤ) (blockFibreSet block i) x (1 : ℤ)

theorem blockFibreInclusion_restrictBlockLinearEquiv
    (blockX : X → I) (blockY : Y → I)
    (d : MonoidAlgebra ℤ X ≃ₗ[ℤ] MonoidAlgebra ℤ Y)
    (hd : BlockDiagonalLinearEquiv blockX blockY d) (i : I)
    (v : MonoidAlgebra ℤ (BlockFibre blockX i)) :
    blockFibreInclusion blockY i
        (restrictBlockLinearEquiv blockX blockY d hd i v) =
      d (blockFibreInclusion blockX i v) := by
  simp [blockFibreInclusion, restrictBlockLinearEquiv,
    restrictSupportedLinearEquiv]

variable {A : Type u} [Group A] [MulAction A X] [MulAction A Y]

/-- The action induced on a block fibre when the block label is invariant. -/
@[instance_reducible]
def blockFibreMulAction (block : X → I)
    (hblock : ∀ (a : A) (x : X), block (a • x) = block x)
    (i : I) : MulAction A (BlockFibre block i) where
  smul a x := ⟨a • x.1, (hblock a x.1).trans x.2⟩
  one_smul x := by
    apply Subtype.ext
    exact one_smul A x.1
  mul_smul a b x := by
    apply Subtype.ext
    exact mul_smul a b x.1

/-- Inclusion of a block fibre into the full permutation module commutes
with the induced action. -/
theorem blockFibreInclusion_action
    (block : X → I)
    (hblock : ∀ (a : A) (x : X), block (a • x) = block x)
    (i : I) (a : A) (v : MonoidAlgebra ℤ (BlockFibre block i)) :
    let _ : MulAction A (BlockFibre block i) :=
      blockFibreMulAction block hblock i
    blockFibreInclusion block i
        (Representation.ofMulAction ℤ A (BlockFibre block i) a v) =
      Representation.ofMulAction ℤ A X a
        (blockFibreInclusion block i v) := by
  let _ : MulAction A (BlockFibre block i) :=
    blockFibreMulAction block hblock i
  let lhs : MonoidAlgebra ℤ (BlockFibre block i) →ₗ[ℤ]
      MonoidAlgebra ℤ X :=
    (blockFibreInclusion block i).comp
      (Representation.ofMulAction ℤ A (BlockFibre block i) a)
  let rhs : MonoidAlgebra ℤ (BlockFibre block i) →ₗ[ℤ]
      MonoidAlgebra ℤ X :=
    (Representation.ofMulAction ℤ A X a).comp
      (blockFibreInclusion block i)
  have hlr : lhs = rhs := by
    apply MonoidAlgebra.lhom_ext'
    intro x
    apply LinearMap.ext_ring
    simp [lhs, rhs]
    rfl
  exact DFunLike.congr_fun hlr v

/-- Equivariance of an ambient block diagonal equivalence is inherited by
its restriction to each invariant block fibre. -/
theorem restrictBlockLinearEquiv_equivariant
    (blockX : X → I) (blockY : Y → I)
    (d : MonoidAlgebra ℤ X ≃ₗ[ℤ] MonoidAlgebra ℤ Y)
    (hd : BlockDiagonalLinearEquiv blockX blockY d)
    (hblockX : ∀ (a : A) (x : X), blockX (a • x) = blockX x)
    (hblockY : ∀ (a : A) (y : Y), blockY (a • y) = blockY y)
    (hintertwines : ∀ (a : A) (v : MonoidAlgebra ℤ X),
      d (Representation.ofMulAction ℤ A X a v) =
        Representation.ofMulAction ℤ A Y a (d v))
    (i : I) :
    let _ : MulAction A (BlockFibre blockX i) :=
      blockFibreMulAction blockX hblockX i
    let _ : MulAction A (BlockFibre blockY i) :=
      blockFibreMulAction blockY hblockY i
    ∀ (a : A) (v : MonoidAlgebra ℤ (BlockFibre blockX i)),
      restrictBlockLinearEquiv blockX blockY d hd i
          (Representation.ofMulAction ℤ A (BlockFibre blockX i) a v) =
        Representation.ofMulAction ℤ A (BlockFibre blockY i) a
          (restrictBlockLinearEquiv blockX blockY d hd i v) := by
  dsimp only
  intro a v
  apply blockFibreInclusion_injective blockY i
  rw [blockFibreInclusion_restrictBlockLinearEquiv,
    blockFibreInclusion_action blockX hblockX,
    hintertwines,
    blockFibreInclusion_action blockY hblockY,
    blockFibreInclusion_restrictBlockLinearEquiv]

variable {F G : Type u} [Field F] [Group G] [Finite G]

/-- Relabelling by a block fibre and then passing to exact `K₀` is the same
as first including the fibre in the full free module. -/
theorem labelledSimpleClassKZero_blockFibre
    (block : X → I) (i : I)
    (label : X → SimpleModuleClass F[G])
    (v : MonoidAlgebra ℤ (BlockFibre block i)) :
    labelledSimpleClassKZero (fun x : BlockFibre block i ↦ label x.1) v =
      labelledSimpleClassKZero label (blockFibreInclusion block i v) := by
  let lhs : MonoidAlgebra ℤ (BlockFibre block i) →ₗ[ℤ] FDRepKZero F G :=
    (labelledSimpleClassKZero
      (fun x : BlockFibre block i ↦ label x.1)).toIntLinearMap
  let rhs : MonoidAlgebra ℤ (BlockFibre block i) →ₗ[ℤ] FDRepKZero F G :=
    (labelledSimpleClassKZero label).toIntLinearMap.comp
      (blockFibreInclusion block i)
  have hlr : lhs = rhs := by
    apply MonoidAlgebra.lhom_ext'
    intro x
    apply LinearMap.ext_ring
    simp [lhs, rhs]
  exact DFunLike.congr_fun hlr v

variable {K k : Type u} [Field K] [Field k]
variable {decomposition : FDRepKZero K G →+ FDRepKZero k G}

/-- A block diagonal global integral basic set restricts to a specified block
fibre.  No restricted equivalence is supplied as input. -/
noncomputable def restrictRestrictedIntegralBasicSet
    (D : RestrictedIntegralBasicSet
      (K := K) (k := k) (G := G) (Basic := X) (Brauer := Y)
      decomposition)
    (blockX : X → I) (blockY : Y → I)
    (hd : BlockDiagonalLinearEquiv blockX blockY D.linearEquiv)
    (i : I) :
    RestrictedIntegralBasicSet
      (K := K) (k := k) (G := G)
      (Basic := BlockFibre blockX i) (Brauer := BlockFibre blockY i)
      decomposition where
  ordinaryLabel x := D.ordinaryLabel x.1
  ordinaryLabel_injective :=
    D.ordinaryLabel_injective.comp Subtype.val_injective
  modularLabel y := D.modularLabel y.1
  modularLabel_injective :=
    D.modularLabel_injective.comp Subtype.val_injective
  linearEquiv := restrictBlockLinearEquiv
    blockX blockY D.linearEquiv hd i
  restricts_decomposition v := by
    calc
      labelledSimpleClassKZero
          (fun y : BlockFibre blockY i ↦ D.modularLabel y.1)
          (restrictBlockLinearEquiv
            blockX blockY D.linearEquiv hd i v) =
          labelledSimpleClassKZero D.modularLabel
            (blockFibreInclusion blockY i
              (restrictBlockLinearEquiv
                blockX blockY D.linearEquiv hd i v)) :=
        labelledSimpleClassKZero_blockFibre
          blockY i D.modularLabel _
      _ = labelledSimpleClassKZero D.modularLabel
          (D.linearEquiv (blockFibreInclusion blockX i v)) := by
        rw [blockFibreInclusion_restrictBlockLinearEquiv]
      _ = decomposition
          (labelledSimpleClassKZero D.ordinaryLabel
            (blockFibreInclusion blockX i v)) :=
        D.restricts_decomposition _
      _ = decomposition
          (labelledSimpleClassKZero
            (fun x : BlockFibre blockX i ↦ D.ordinaryLabel x.1) v) := by
        rw [labelledSimpleClassKZero_blockFibre]

/-- The action on a block fibre is the restriction of the ambient action on
its labels. -/
def BlockFibreActionCompatible
    (block : X → I) (i : I)
    [MulAction A (BlockFibre block i)] : Prop :=
  ∀ (a : A) (x : BlockFibre block i), (a • x).1 = a • x.1

variable {blockX : X → I} {blockY : Y → I} {i : I}
variable [MulAction A (BlockFibre blockX i)]
variable [MulAction A (BlockFibre blockY i)]

/-- Compatible exact-`K₀` actions on a global integral basic set restrict to
compatible actions on each stable block fibre. -/
noncomputable def restrictLabelledKZeroActionData
    (D : RestrictedIntegralBasicSet
      (K := K) (k := k) (G := G) (Basic := X) (Brauer := Y)
      decomposition)
    (hd : BlockDiagonalLinearEquiv blockX blockY D.linearEquiv)
    (hact : LabelledKZeroActionData (A := A) D)
    (hX : BlockFibreActionCompatible (A := A) blockX i)
    (hY : BlockFibreActionCompatible (A := A) blockY i) :
    LabelledKZeroActionData (A := A)
      (restrictRestrictedIntegralBasicSet D blockX blockY hd i) where
  ordinaryAction := hact.ordinaryAction
  modularAction := hact.modularAction
  ordinary_single a x := by
    simpa only [restrictRestrictedIntegralBasicSet,
      labelledSimpleClassKZero_single, hX a x] using
        hact.ordinary_single a x.1
  modular_single a y := by
    simpa only [restrictRestrictedIntegralBasicSet,
      labelledSimpleClassKZero_single, hY a y] using
        hact.modular_single a y.1

/-- Exact-`K₀` naturality on the global basic set makes the restricted block
matrix equivariant. -/
theorem matrixEquivariant_restrictBlock_of_kZero_naturality
    (D : RestrictedIntegralBasicSet
      (K := K) (k := k) (G := G) (Basic := X) (Brauer := Y)
      decomposition)
    (hd : BlockDiagonalLinearEquiv blockX blockY D.linearEquiv)
    (hact : LabelledKZeroActionData (A := A) D)
    (hnatural : DecompositionNatural (A := A) decomposition
      hact.ordinaryAction hact.modularAction)
    (hX : BlockFibreActionCompatible (A := A) blockX i)
    (hY : BlockFibreActionCompatible (A := A) blockY i) :
    IntegralBasicSetBridge.MatrixEquivariant (A := A)
      (restrictRestrictedIntegralBasicSet
        D blockX blockY hd i).linearEquiv.toLinearMap :=
  matrixEquivariant_of_kZero_naturality
    (restrictRestrictedIntegralBasicSet D blockX blockY hd i)
    (restrictLabelledKZeroActionData D hd hact hX hY) hnatural

/-- The block restriction followed by the Conlon and Burnside steps gives an
equivariant bijection on the fixed block fibre. -/
theorem equivariantSetEquiv_restrictBlock_of_kZero_naturality
    {conlonPrime : ℕ} [Fact conlonPrime.Prime]
    [Finite A] [Finite X] [Finite Y]
    (D : RestrictedIntegralBasicSet
      (K := K) (k := k) (G := G) (Basic := X) (Brauer := Y)
      decomposition)
    (hd : BlockDiagonalLinearEquiv blockX blockY D.linearEquiv)
    (hact : LabelledKZeroActionData (A := A) D)
    (hnatural : DecompositionNatural (A := A) decomposition
      hact.ordinaryAction hact.modularAction)
    (hX : BlockFibreActionCompatible (A := A) blockX i)
    (hY : BlockFibreActionCompatible (A := A) blockY i)
    (ambientHypoelementary :
      IntegralBasicSetBridge.IsPHypoelementary conlonPrime A)
    (conlon : PaperProofs.ConlonBasicSet.PadicConlonMarkDetection.{u, u}
      (p := conlonPrime) (A := A))
    (burnside :
      PaperProofs.ConlonBasicSet.PublishedBurnsideMarkInjectivity.{u, u}
        (A := A)) :
    ∃ e : BlockFibre blockX i ≃ BlockFibre blockY i,
      ∀ (a : A) (x : BlockFibre blockX i), e (a • x) = a • e x :=
  equivariantSetEquiv_of_kZero_naturality
    (restrictRestrictedIntegralBasicSet D blockX blockY hd i)
    (restrictLabelledKZeroActionData D hd hact hX hY) hnatural
    ambientHypoelementary conlon burnside

end ModularRep.BlockFibreRestriction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
