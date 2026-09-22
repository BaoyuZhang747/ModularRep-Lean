import ModularRep.PaperProofs.TypeBConformalDualCarriers
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
The standard projective conformal action on the literal matrix Sp4.

The coordinate matrix is fixed before the routine E1 form dictionary is
introduced. Its two clauses say only that multiplier-one matrices preserve
the standard form and that every matrix preserving that form occurs.
The dictionary relates the displayed two-half form to mathlib's symplectic
matrix convention; the transpose-first and transpose-last identities are
equivalent by SymplecticGroup.mem_iff', not definitionally identical.
Injectivity, the group equivalence, normal conjugation, and descent through
all scalar matrices are deductions. No character action, finite group
equivalence, diagonal image, or stabilizer statement is sourced.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBLeviReturnB2MatrixAction

open TypeBConformalDualCarriers

universe u

variable (F : Type u) [Field F]

abbrev Coordinate := Fin 2 ⊕ Fin 2
abbrev MatrixSp4 := Matrix.symplecticGroup (Fin 2) F
abbrev Kernel := (multiplier F 2).ker

/-- The fixed passage from four coordinates to the two coordinate halves. -/
def coordinates : (Coordinate → F) ≃ₗ[F] SymplecticSpace F 2 :=
  LinearEquiv.sumArrowLequivProdArrow (Fin 2) (Fin 2) F F

/-- The same linear similitude written in four coordinates. -/
def coordinateLinear : CSp F 2 →*
    ((Coordinate → F) ≃ₗ[F] (Coordinate → F)) where
  toFun g := (coordinates F).trans ((linearPart F 2 g).trans (coordinates F).symm)
  map_one' := by
    ext v
    simp [LinearEquiv.trans_apply]
  map_mul' g h := by
    ext v
    simp [LinearEquiv.trans_apply]

/-- Its literal coordinate matrix, using the standard basis. -/
def coordinateMatrix : CSp F 2 →* Matrix Coordinate Coordinate F :=
  LinearMap.toMatrixAlgEquiv'.toMonoidHom.comp
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (coordinateLinear F))

@[simp] theorem coordinateMatrix_entry (g : CSp F 2) (i j : Coordinate) :
    coordinateMatrix F g i j = coordinateLinear F g (Pi.single j 1) i := rfl

theorem coordinateMatrix_mulVec (g : CSp F 2) (v : Coordinate → F) :
    (coordinateMatrix F g).mulVec v = coordinateLinear F g v :=
  LinearMap.toMatrix'_mulVec (coordinateLinear F g).toLinearMap v

/-- The standard form dictionary at this already specified coordinate map.
Its specified interpretation is routine E1/U; it contains no chosen action. -/
structure MatrixKernelSource : Prop where
  symplectic : ∀ g : Kernel F,
    coordinateMatrix F g.val ∈ Matrix.symplecticGroup (Fin 2) F
  complete : ∀ x : MatrixSp4 F, ∃ g : Kernel F,
    coordinateMatrix F g.val = x.val

variable {F}

def kernelToSp (source : MatrixKernelSource F) : Kernel F →* MatrixSp4 F where
  toFun g := ⟨coordinateMatrix F g.val, source.symplectic g⟩
  map_one' := Subtype.ext (map_one (coordinateMatrix F))
  map_mul' g h := Subtype.ext (map_mul (coordinateMatrix F) g.val h.val)

@[simp] theorem kernelToSp_value (source : MatrixKernelSource F) (g : Kernel F) :
    (kernelToSp source g).val = coordinateMatrix F g.val := rfl

theorem kernelToSp_injective (source : MatrixKernelSource F) :
    Function.Injective (kernelToSp source) := by
  intro g h heq
  have hmatrix : coordinateMatrix F g.val = coordinateMatrix F h.val :=
    congrArg Subtype.val heq
  have hlinear : coordinateLinear F g.val = coordinateLinear F h.val := by
    apply LinearEquiv.ext
    intro v
    exact (coordinateMatrix_mulVec F g.val v).symm.trans
      ((congrArg (fun M : Matrix Coordinate Coordinate F => M.mulVec v) hmatrix).trans
        (coordinateMatrix_mulVec F h.val v))
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · apply LinearEquiv.ext
    intro v
    have hv := congrArg
      (fun L : (Coordinate → F) ≃ₗ[F] (Coordinate → F) =>
        coordinates F (L ((coordinates F).symm v))) hlinear
    simpa [coordinateLinear, LinearEquiv.trans_apply] using hv
  · exact g.property.trans h.property.symm

theorem kernelToSp_surjective (source : MatrixKernelSource F) :
    Function.Surjective (kernelToSp source) := by
  intro x
  obtain ⟨g, hg⟩ := source.complete x
  exact ⟨g, Subtype.ext hg⟩

/-- The equivalence is constructed from the fixed matrix map. -/
def kernelEquiv (source : MatrixKernelSource F) : Kernel F ≃* MatrixSp4 F :=
  MulEquiv.ofBijective (kernelToSp source)
    ⟨kernelToSp_injective source, kernelToSp_surjective source⟩

@[simp] theorem kernelEquiv_value (source : MatrixKernelSource F) (g : Kernel F) :
    (kernelEquiv source g).val = coordinateMatrix F g.val := rfl

/-- Actual conjugation on the multiplier kernel, in matrix coordinates. -/
def cspAction (source : MatrixKernelSource F) : CSp F 2 →* MulAut (MatrixSp4 F) :=
  (MulAut.congr (kernelEquiv source)).toMonoidHom.comp
    (MulAut.conjNormal (H := (multiplier F 2).ker))

theorem cspAction_matrix (source : MatrixKernelSource F)
    (g : CSp F 2) (x : MatrixSp4 F) :
    (cspAction source g x).val =
      coordinateMatrix F g * x.val * coordinateMatrix F g⁻¹ := by
  have hx := kernelEquiv_value source ((kernelEquiv source).symm x)
  rw [MulEquiv.apply_symm_apply] at hx
  change coordinateMatrix F
    (g * ((kernelEquiv source).symm x).val * g⁻¹) = _
  rw [map_mul, map_mul, ← hx]

theorem cspAction_kernel (source : MatrixKernelSource F) (x : Kernel F) :
    cspAction source x.val = MulAut.conj (kernelEquiv source x) := by
  apply MulEquiv.ext
  intro y
  change kernelEquiv source
    (MulAut.conjNormal x.val ((kernelEquiv source).symm y)) =
      kernelEquiv source x * y * (kernelEquiv source x)⁻¹
  have hx : MulAut.conjNormal x.val ((kernelEquiv source).symm y) =
      x * (kernelEquiv source).symm y * x⁻¹ := Subtype.ext rfl
  rw [hx, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem cspAction_scalar (source : MatrixKernelSource F) (z : Fˣ) :
    cspAction source (scalar F 2 z) = 1 := by
  have hscalar :
      MulAut.conjNormal (H := (multiplier F 2).ker) (scalar F 2 z) = 1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change scalar F 2 z * x.val * (scalar F 2 z)⁻¹ = x.val
    rw [scalar_commute, mul_inv_cancel_right]
  change MulAut.congr (kernelEquiv source)
    (MulAut.conjNormal (scalar F 2 z)) = 1
  rw [hscalar, map_one]

theorem scalarSubgroup_le_action_ker (source : MatrixKernelSource F) :
    scalarSubgroup F 2 ≤ (cspAction source).ker := by
  rintro g ⟨z, rfl⟩
  exact cspAction_scalar source z

/-- Descent by the full scalar subgroup; no projective lift is chosen. -/
def pcspAction (source : MatrixKernelSource F) : PCSp F 2 →* MulAut (MatrixSp4 F) :=
  QuotientGroup.lift (scalarSubgroup F 2) (cspAction source)
    (scalarSubgroup_le_action_ker source)

@[simp] theorem pcspAction_mk (source : MatrixKernelSource F) (g : CSp F 2) :
    pcspAction source (QuotientGroup.mk' (scalarSubgroup F 2) g) =
      cspAction source g := rfl

theorem pcspAction_mk_matrix (source : MatrixKernelSource F)
    (g : CSp F 2) (x : MatrixSp4 F) :
    (pcspAction source (QuotientGroup.mk' (scalarSubgroup F 2) g) x).val =
      coordinateMatrix F g * x.val * coordinateMatrix F g⁻¹ :=
  cspAction_matrix source g x

end ModularRep.PaperProofs.TypeBLeviReturnB2MatrixAction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
