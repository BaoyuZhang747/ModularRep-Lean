import ModularRep.PaperProofs.TypeBSpecialCliffordActionSplitting
import ModularRep.PaperProofs.TypeBCentralKernelBrauerBlocks
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# The actual tensor and field action on primitive block idempotents

For a = (lambda,e), the group algebra automorphism sends the basis element
[h] to lambda(field e h) [field e h]. This is the inverse of the algebra
pullback occurring in the existing inverse-tensor/inverse-field character
action. Primitive transport and Brauer-block equivariance are deductions
from that cancellation and the actual supporting irreducible module.

No action, block equivariance, support callback or new source field is an
input. Ordinary decomposition-row and ordinary-block transport are separate.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBPhysicalBlockAction

open ModularRep FDRepSimpleClassKZero
open TypeCConformalActionAdapter
open TypeBCentralKernelBlockSource

universe u
variable {k G : Type u} [Field k] [Group G]

/-- Multiplicative weighted group basis for an actual modular linear character. -/
def weightedBasis (lambda : G →* kˣ) : G →* k[G] where
  toFun g := MonoidAlgebra.single g (lambda g : k)
  map_one' := by simp [MonoidAlgebra.one_def]
  map_mul' g h := by simp [MonoidAlgebra.single_mul_single]

/-- Scale every group basis element by its actual linear character value. -/
def tensorAlgHom (lambda : G →* kˣ) : k[G] →ₐ[k] k[G] :=
  MonoidAlgebra.lift k k[G] G (weightedBasis lambda)

@[simp]
theorem tensorAlgHom_single (lambda : G →* kˣ) (g : G) (r : k) :
    tensorAlgHom lambda (MonoidAlgebra.single g r) =
      MonoidAlgebra.single g (r * (lambda g : k)) := by
  simp [tensorAlgHom, weightedBasis, MonoidAlgebra.lift_single]

/-- The coefficient formula fixes both the scalar and the unchanged basis index. -/
theorem tensorAlgHom_coeff (lambda : G →* kˣ) (x : k[G]) (g : G) :
    (tensorAlgHom lambda x).coeff g = (lambda g : k) * x.coeff g := by
  classical
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy, mul_add]
  | single h r =>
      by_cases hh : h = g
      · subst h
        simp [mul_comm]
      · simp [hh, Ne.symm hh]

theorem tensorAlgHom_one_apply (x : k[G]) :
    tensorAlgHom (1 : G →* kˣ) x = x := by
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro g
  simp [tensorAlgHom_coeff]

theorem tensorAlgHom_mul_apply (lambda mu : G →* kˣ) (x : k[G]) :
    tensorAlgHom lambda (tensorAlgHom mu x) = tensorAlgHom (lambda * mu) x := by
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro g
  simp only [tensorAlgHom_coeff, MonoidHom.mul_apply, Units.val_mul, mul_assoc]

/-- Tensor basis scaling is a ring automorphism, with inverse inverse-character scaling. -/
def tensorRingEquiv (lambda : G →* kˣ) : k[G] ≃+* k[G] :=
  { (tensorAlgHom lambda).toRingHom with
    invFun := tensorAlgHom lambda⁻¹
    left_inv := by
      intro x
      change tensorAlgHom lambda⁻¹ (tensorAlgHom lambda x) = x
      have h : (lambda⁻¹ * lambda : G →* kˣ) = 1 := by
        apply MonoidHom.ext
        intro g
        change (lambda g)⁻¹ * lambda g = 1
        exact inv_mul_cancel _
      rw [tensorAlgHom_mul_apply, h, tensorAlgHom_one_apply]
    right_inv := by
      intro x
      change tensorAlgHom lambda (tensorAlgHom lambda⁻¹ x) = x
      have h : (lambda * lambda⁻¹ : G →* kˣ) = 1 := by
        apply MonoidHom.ext
        intro g
        change lambda g * (lambda g)⁻¹ = 1
        exact mul_inv_cancel _
      rw [tensorAlgHom_mul_apply, h, tensorAlgHom_one_apply] }

@[simp]
theorem tensorRingEquiv_single (lambda : G →* kˣ) (g : G) (r : k) :
    tensorRingEquiv lambda (MonoidAlgebra.single g r) =
      MonoidAlgebra.single g (r * (lambda g : k)) :=
  tensorAlgHom_single lambda g r

theorem tensorRingEquiv_coeff (lambda : G →* kˣ) (x : k[G]) (g : G) :
    (tensorRingEquiv lambda x).coeff g = (lambda g : k) * x.coeff g :=
  tensorAlgHom_coeff lambda x g

/-- Scaling the algebra basis cancels the inverse linear character representation twist. -/
theorem tensor_cancel {V : Type u} [AddCommGroup V] [Module k V]
    (rho : Representation k G V) (lambda : G →* kˣ) (x : k[G]) :
    (rho.linearCharacterTwist lambda⁻¹).asAlgebraHom (tensorRingEquiv lambda x) =
      rho.asAlgebraHom x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single g r =>
      rw [tensorRingEquiv_single, Representation.asAlgebraHom_single,
        Representation.asAlgebraHom_single]
      change (r * (lambda g : k)) • ((lambda⁻¹ g : k) • rho g) = r • rho g
      simp [smul_smul, mul_assoc]

section ActualActor

variable [Finite G]
variable {E : Type u} [Group E]
variable (G0 : Subgroup G) [G0.Normal]
variable (field : E →* MulAut G)
variable (hinvariant : FieldInvariantSubgroup.IsInvariant G0 field)

/-- Forward field transport followed by actual modular tensor scaling. -/
def sigma (a : ActingGroup (k := k) G0 field hinvariant) : k[G] ≃+* k[G] :=
  (MonoidAlgebra.mapDomainRingEquiv k (field a.right)).trans
    (tensorRingEquiv a.left.val)

@[simp]
theorem sigma_single (a : ActingGroup (k := k) G0 field hinvariant) (h : G) (r : k) :
    sigma G0 field hinvariant a (MonoidAlgebra.single h r) =
      MonoidAlgebra.single (field a.right h) (r * (a.left.val (field a.right h) : k)) := by
  simp [sigma]

/-- The inverse in the coefficient index is exactly the existing character convention. -/
theorem sigma_coeff (a : ActingGroup (k := k) G0 field hinvariant) (x : k[G]) (g : G) :
    (sigma G0 field hinvariant a x).coeff g =
      (a.left.val g : k) * x.coeff (field a.right⁻¹ g) := by
  change (tensorRingEquiv a.left.val
    (MonoidAlgebra.mapDomainRingEquiv k (field a.right) x)).coeff g = _
  rw [tensorRingEquiv_coeff, MonoidAlgebra.coeff_mapDomainRingEquiv,
    Finsupp.equivMapDomain_apply]
  simp only [map_inv]
  rfl

theorem sigma_one (x : k[G]) :
    sigma G0 field hinvariant (1 : ActingGroup (k := k) G0 field hinvariant) x = x := by
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro g
  rw [sigma_coeff]
  simp

theorem sigma_mul (a b : ActingGroup (k := k) G0 field hinvariant) (x : k[G]) :
    sigma G0 field hinvariant (a * b) x =
      sigma G0 field hinvariant a (sigma G0 field hinvariant b x) := by
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro g
  rw [sigma_coeff, sigma_coeff, sigma_coeff]
  have hleft : ((a * b).left.val g : k) =
      (a.left.val g : k) * (b.left.val (field a.right⁻¹ g) : k) := by
    rw [SemidirectProduct.mul_left]
    rfl
  rw [hleft, SemidirectProduct.mul_right, mul_inv_rev, map_mul]
  change ((a.left.val g : k) * (b.left.val (field a.right⁻¹ g) : k)) *
      x.coeff (field b.right⁻¹ (field a.right⁻¹ g)) =
    (a.left.val g : k) * ((b.left.val (field a.right⁻¹ g) : k) *
      x.coeff (field b.right⁻¹ (field a.right⁻¹ g)))
  exact mul_assoc _ _ _

/-- The actual primitive idempotent image, before installing its action. -/
def blockTransport (a : ActingGroup (k := k) G0 field hinvariant)
    (b : LiteralPrimitiveBlock k G) : LiteralPrimitiveBlock k G :=
  ⟨sigma G0 field hinvariant a b.val, b.property.mapRingEquiv (sigma G0 field hinvariant a)⟩

@[simp]
theorem blockTransport_val (a : ActingGroup (k := k) G0 field hinvariant)
    (b : LiteralPrimitiveBlock k G) :
    (blockTransport G0 field hinvariant a b).val = sigma G0 field hinvariant a b.val := rfl

/-- Canonical tensor/field action on the literal primitive blocks. -/
@[instance_reducible]
def blockAction : MulAction (ActingGroup (k := k) G0 field hinvariant)
    (LiteralPrimitiveBlock k G) where
  smul := blockTransport G0 field hinvariant
  one_smul b := Subtype.ext (sigma_one G0 field hinvariant b.val)
  mul_smul a b x := Subtype.ext (sigma_mul G0 field hinvariant a b x.val)

theorem blockAction_smul_coeff (a : ActingGroup (k := k) G0 field hinvariant)
    (b : LiteralPrimitiveBlock k G) (g : G) :
    letI : MulAction (ActingGroup (k := k) G0 field hinvariant)
      (LiteralPrimitiveBlock k G) := blockAction (k := k) G0 field hinvariant
    (a • b).val.coeff g = (a.left.val g : k) * b.val.coeff (field a.right⁻¹ g) :=
  sigma_coeff G0 field hinvariant a b.val g

/-- The defining cancellation square on the SAME actual representation. -/
theorem sigma_cancel {V : Type u} [AddCommGroup V] [Module k V]
    (rho : Representation k G V) (a : ActingGroup (k := k) G0 field hinvariant)
    (x : k[G]) :
    ((rho.twist (field a.right⁻¹)).linearCharacterTwist a.left.val⁻¹).asAlgebraHom
        (sigma G0 field hinvariant a x) = rho.asAlgebraHom x := by
  change ((rho.twist (field a.right⁻¹)).linearCharacterTwist a.left.val⁻¹).asAlgebraHom
    (tensorRingEquiv a.left.val
      (MonoidAlgebra.mapDomainRingEquiv k (field a.right) x)) = _
  rw [tensor_cancel]
  simpa using
    Representation.twist_asAlgebraHom_mapDomainRingEquiv_symm_apply rho (field a.right⁻¹) x

section Brauer

variable {p : ℕ} {K : Type u}
variable [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable (iota : PrimeRegularRootEmbedding p k K G)
variable (productFormula : BrauerLinearTensorProductFormula iota)

/-- Transport actual supporting modules, using the existing tensor formula
only to identify their actual function-valued Brauer characters. -/
theorem supported_transport
    (a : ActingGroup (k := k) G0 field hinvariant)
    (b : LiteralPrimitiveBlock k G) (phi : IBr iota)
    (support : Supported iota b phi) :
    Supported iota (blockTransport G0 field hinvariant a b)
      (IrreducibleBrauerCharacter.linearTwist iota productFormula
        (IrreducibleBrauerCharacter.twist iota phi (field a.right⁻¹)) a.left.val⁻¹) := by
  obtain ⟨V, hV, hchar, hsupp⟩ := support
  let Vfield : FDRep k G := FDRep.of (Representation.twist V.ρ (field a.right⁻¹))
  let W : FDRep k G := FDRep.of (Representation.linearCharacterTwist Vfield.ρ a.left.val⁻¹)
  have hW : Representation.IsIrreducible W.ρ :=
    (hV.twist (field a.right⁻¹)).linearCharacterTwist a.left.val⁻¹
  refine ⟨W, hW, ?_, ?_⟩
  · change PrimeRegularClassFunction.pointwiseMul (iota.liftedLinearCharacter a.left.val⁻¹)
      (phi.val.twist (field a.right⁻¹)) =
        Representation.brauerCharacterOfRootEmbedding
          (Representation.linearCharacterTwist Vfield.ρ a.left.val⁻¹) iota
    rw [productFormula Vfield a.left.val⁻¹]
    change PrimeRegularClassFunction.pointwiseMul _ (phi.val.twist (field a.right⁻¹)) =
      PrimeRegularClassFunction.pointwiseMul _
        (Representation.brauerCharacterOfRootEmbedding (Representation.twist V.ρ (field a.right⁻¹)) iota)
    rw [Representation.brauerCharacterOfRootEmbedding_twist, ← hchar]
  · change (Representation.linearCharacterTwist
      (Representation.twist V.ρ (field a.right⁻¹)) a.left.val⁻¹).asAlgebraHom
      (sigma G0 field hinvariant a b.val) = 1
    rw [sigma_cancel, hsupp]

variable [Fintype (LiteralPrimitiveBlock k G)]
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition (fun b : LiteralPrimitiveBlock k G => b.val))

/-- The existing Brauer block compatibility predicate is a theorem for the
constructed specified primitive-block action. -/
theorem brauerBlockEquivariant :
    letI : MulAction (ActingGroup (k := k) G0 field hinvariant)
      (LiteralPrimitiveBlock k G) := blockAction (k := k) G0 field hinvariant
    BrauerBlockEquivariant G0 field hinvariant iota productFormula
      (irreducibleBrauerCharacterBlock iota hinj blocks) := by
  letI : MulAction (ActingGroup (k := k) G0 field hinvariant)
    (LiteralPrimitiveBlock k G) := blockAction (k := k) G0 field hinvariant
  intro a phi
  change irreducibleBrauerCharacterBlock iota hinj blocks
      (IrreducibleBrauerCharacter.linearTwist iota productFormula
        (IrreducibleBrauerCharacter.twist iota phi (field a.right⁻¹)) a.left.val⁻¹) =
    blockTransport G0 field hinvariant a (irreducibleBrauerCharacterBlock iota hinj blocks phi)
  have hs : Supported iota (irreducibleBrauerCharacterBlock iota hinj blocks phi) phi := by
    apply (TypeBCentralKernelBrauerBlocks.supported_iff_block iota blocks _ phi).mpr
    rfl
  have ht := supported_transport G0 field hinvariant iota productFormula a
    (irreducibleBrauerCharacterBlock iota hinj blocks phi) phi hs
  exact (TypeBCentralKernelBrauerBlocks.supported_iff_block iota blocks _ _).mp ht

end Brauer
end ActualActor

end ModularRep.PaperProofs.TypeBPhysicalBlockAction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
