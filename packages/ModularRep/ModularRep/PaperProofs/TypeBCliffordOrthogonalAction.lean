import ModularRep.PaperProofs.TypeBCliffordCarriers
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-!
# Literal special Clifford conjugation on the split quadratic space

The vector embedding has an explicit linear left inverse: the displayed
split quadratic form is the diagonal of a displayed bilinear form, so the
checked Clifford change-of-form equivalence identifies its vector copy
with the vector copy in the exterior algebra. This works without a
characteristic restriction or an external injectivity assumption.

The existing setwise vector-normalizer condition then makes the actual
Clifford conjugation an invertible linear map of the same vector space.
The Clifford square relation proves preservation of the same split form.
No Lipschitz closure, Mathlib spinGroup identification, special-orthogonal
image, Omega image, determinant statement or source certificate is used.
-/

noncomputable section
set_option autoImplicit false

open scoped Pointwise

namespace ModularRep.PaperProofs.TypeBCliffordOrthogonalAction

open TypeBCliffordCarriers

universe u

variable (n : ℕ) (F : Type u) [Field F]

/-- The literal ordered coordinate product as a bilinear form. -/
def coordinateBilin (i j : Coordinate n) : LinearMap.BilinForm F (Vector n F) :=
  (LinearMap.mul F F).compl₁₂ (LinearMap.proj i) (LinearMap.proj j)

@[simp] theorem coordinateBilin_apply (i j : Coordinate n) (v w : Vector n F) :
    coordinateBilin n F i j v w = v i * w j := rfl

/-- A bilinear form whose diagonal is exactly the displayed split form.
It need not be symmetric, and no division by two is involved. -/
def splitBilin : LinearMap.BilinForm F (Vector n F) :=
  coordinateBilin n F none none +
    ∑ i : Fin n, coordinateBilin n F (some (Sum.inl i)) (some (Sum.inr i))

@[simp] theorem splitBilin_apply (v w : Vector n F) :
    splitBilin n F v w = v none * w none +
      ∑ i : Fin n, v (some (Sum.inl i)) * w (some (Sum.inr i)) := by
  simp [splitBilin]

theorem splitBilin_toQuadraticMap :
    (splitBilin n F).toQuadraticMap = splitForm n F := by
  ext v
  simp

theorem exteriorChangeForm :
    (-splitBilin n F).toQuadraticMap = (0 : QuadraticForm F (Vector n F)) - splitForm n F := by
  rw [LinearMap.BilinMap.toQuadraticMap_neg, splitBilin_toQuadraticMap, zero_sub]

/-- The canonical change-of-form equivalence for this explicit bilinear
form. It fixes every vector and every scalar. -/
def exteriorEquiv : Clifford n F ≃ₗ[F] ExteriorAlgebra F (Vector n F) :=
  CliffordAlgebra.changeFormEquiv (exteriorChangeForm n F)

@[simp] theorem exteriorEquiv_iota (v : Vector n F) :
    exteriorEquiv n F (CliffordAlgebra.ι (splitForm n F) v) = ExteriorAlgebra.ι F v :=
  CliffordAlgebra.changeForm_ι (exteriorChangeForm n F) v

@[simp] theorem exteriorEquiv_algebraMap (a : F) :
    exteriorEquiv n F (algebraMap F (Clifford n F) a) =
      algebraMap F (ExteriorAlgebra F (Vector n F)) a :=
  CliffordAlgebra.changeForm_algebraMap (exteriorChangeForm n F) a

/-- A literal linear left inverse for the Clifford vector embedding. -/
def vectorProjection : Clifford n F →ₗ[F] Vector n F :=
  ExteriorAlgebra.ιInv.comp (exteriorEquiv n F).toLinearMap

@[simp] theorem vectorProjection_iota (v : Vector n F) :
    vectorProjection n F (CliffordAlgebra.ι (splitForm n F) v) = v := by
  change ExteriorAlgebra.ιInv
    (exteriorEquiv n F (CliffordAlgebra.ι (splitForm n F) v)) = v
  rw [exteriorEquiv_iota]
  exact ExteriorAlgebra.ι_leftInverse v

theorem iota_injective : Function.Injective (CliffordAlgebra.ι (splitForm n F)) :=
  (show Function.LeftInverse (vectorProjection n F)
    (CliffordAlgebra.ι (splitForm n F)) from vectorProjection_iota n F).injective

theorem clifford_nontrivial : Nontrivial (Clifford n F) :=
  (exteriorEquiv n F).symm.injective.nontrivial

theorem algebraMap_injective : Function.Injective (algebraMap F (Clifford n F)) := by
  letI := clifford_nontrivial n F
  exact (algebraMap F (Clifford n F)).injective

/-- Conjugation on the actual Clifford algebra, as algebra automorphisms. -/
def algebraAction : SpecialClifford n F →* (Clifford n F ≃ₐ[F] Clifford n F) :=
  (MulSemiringAction.toAlgAut (ConjAct (Clifford n F)ˣ) F (Clifford n F)).comp
    (ConjAct.toConjAct.toMonoidHom.comp (toCliffordUnit n F))

@[simp] theorem algebraAction_apply (g : SpecialClifford n F) (x : Clifford n F) :
    algebraAction n F g x =
      toClifford n F g * x * toClifford n F (g⁻¹) := rfl

/-- This uses exactly the defining setwise vector normalizer, including
its actual conjugation action. -/
theorem algebraAction_iota_mem (g : SpecialClifford n F) (v : Vector n F) :
    algebraAction n F g (CliffordAlgebra.ι (splitForm n F) v) ∈ vectorImage n F := by
  have hv : CliffordAlgebra.ι (splitForm n F) v ∈ vectorImage n F := ⟨v, rfl⟩
  have image_mem : ConjAct.toConjAct g.val • CliffordAlgebra.ι (splitForm n F) v ∈
      ConjAct.toConjAct g.val • vectorImage n F :=
    Set.smul_mem_smul_set_iff.mpr hv
  rw [(specialClifford_membership n F g).2] at image_mem
  exact image_mem

/-- The induced vector map is an actual composition of linear maps. -/
def vectorMap (g : SpecialClifford n F) : Vector n F →ₗ[F] Vector n F :=
  (vectorProjection n F).comp
    ((algebraAction n F g).toLinearMap.comp (CliffordAlgebra.ι (splitForm n F)))

theorem iota_vectorMap (g : SpecialClifford n F) (v : Vector n F) :
    CliffordAlgebra.ι (splitForm n F) (vectorMap n F g v) =
      algebraAction n F g (CliffordAlgebra.ι (splitForm n F) v) := by
  obtain ⟨w, hw⟩ := algebraAction_iota_mem n F g v
  change CliffordAlgebra.ι (splitForm n F)
    (vectorProjection n F (algebraAction n F g (CliffordAlgebra.ι (splitForm n F) v))) = _
  rw [← hw, vectorProjection_iota]

@[simp] theorem vectorMap_one (v : Vector n F) : vectorMap n F 1 v = v := by
  apply iota_injective n F
  rw [iota_vectorMap, map_one]
  rfl

theorem vectorMap_mul (g h : SpecialClifford n F) (v : Vector n F) :
    vectorMap n F (g * h) v = vectorMap n F g (vectorMap n F h v) := by
  apply iota_injective n F
  rw [iota_vectorMap, iota_vectorMap, iota_vectorMap, map_mul]
  rfl

/-- The inverse is induced by the inverse of the same Clifford element. -/
def vectorEquiv (g : SpecialClifford n F) : Vector n F ≃ₗ[F] Vector n F :=
  { vectorMap n F g with
    invFun := vectorMap n F (g⁻¹)
    left_inv := fun v => by
      change vectorMap n F (g⁻¹) (vectorMap n F g v) = v
      rw [← vectorMap_mul, inv_mul_cancel, vectorMap_one]
    right_inv := fun v => by
      change vectorMap n F g (vectorMap n F (g⁻¹) v) = v
      rw [← vectorMap_mul, mul_inv_cancel, vectorMap_one] }

/-- The literal group action in the general linear group of the vector space. -/
def linearAction : SpecialClifford n F →* (Vector n F ≃ₗ[F] Vector n F) where
  toFun := vectorEquiv n F
  map_one' := by
    apply LinearEquiv.ext
    exact vectorMap_one n F
  map_mul' g h := by
    apply LinearEquiv.ext
    exact vectorMap_mul n F g h

/-- The source's defining equation, with inverse in the actual special
Clifford carrier so that its field-action formula applies directly. -/
theorem iota_action (g : SpecialClifford n F) (v : Vector n F) :
    CliffordAlgebra.ι (splitForm n F) (linearAction n F g v) =
      toClifford n F g * CliffordAlgebra.ι (splitForm n F) v * toClifford n F (g⁻¹) :=
  (iota_vectorMap n F g v).trans (algebraAction_apply n F g _)

@[simp] theorem action_one (v : Vector n F) : linearAction n F 1 v = v :=
  vectorMap_one n F v

theorem action_mul (g h : SpecialClifford n F) (v : Vector n F) :
    linearAction n F (g * h) v = linearAction n F g (linearAction n F h v) :=
  vectorMap_mul n F g h v

@[simp] theorem action_inv_apply (g : SpecialClifford n F) (v : Vector n F) :
    linearAction n F (g⁻¹) (linearAction n F g v) = v :=
  (vectorEquiv n F g).left_inv v

/-- Preservation of the literal split quadratic form follows by squaring
the conjugated vector and using injectivity of the actual scalar map. -/
theorem preserves_splitForm (g : SpecialClifford n F) (v : Vector n F) :
    splitForm n F (linearAction n F g v) = splitForm n F v := by
  apply algebraMap_injective n F
  calc
    algebraMap F (Clifford n F) (splitForm n F (linearAction n F g v)) =
        CliffordAlgebra.ι (splitForm n F) (linearAction n F g v) *
          CliffordAlgebra.ι (splitForm n F) (linearAction n F g v) :=
      (CliffordAlgebra.ι_sq_scalar (splitForm n F) (linearAction n F g v)).symm
    _ = algebraAction n F g (CliffordAlgebra.ι (splitForm n F) v) *
        algebraAction n F g (CliffordAlgebra.ι (splitForm n F) v) := by
      rw [show CliffordAlgebra.ι (splitForm n F) (linearAction n F g v) =
        algebraAction n F g (CliffordAlgebra.ι (splitForm n F) v) from iota_vectorMap n F g v]
    _ = algebraAction n F g
        (CliffordAlgebra.ι (splitForm n F) v * CliffordAlgebra.ι (splitForm n F) v) :=
      (map_mul (algebraAction n F g) _ _).symm
    _ = algebraAction n F g (algebraMap F (Clifford n F) (splitForm n F v)) :=
      congrArg (algebraAction n F g) (CliffordAlgebra.ι_sq_scalar (splitForm n F) v)
    _ = algebraMap F (Clifford n F) (splitForm n F v) :=
      (algebraAction n F g).commutes (splitForm n F v)

/-- The same action bundled as an isometry of the same quadratic form. -/
def quadraticIsometry (g : SpecialClifford n F) :
    (splitForm n F).IsometryEquiv (splitForm n F) where
  __ := linearAction n F g
  map_app' := preserves_splitForm n F g

@[simp] theorem quadraticIsometry_apply (g : SpecialClifford n F) (v : Vector n F) :
    quadraticIsometry n F g v = linearAction n F g v := rfl

end ModularRep.PaperProofs.TypeBCliffordOrthogonalAction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
