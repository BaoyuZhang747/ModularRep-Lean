import ModularRep.BrauerLinearCharacterTensorAction
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Linear Brauer characters trivial on a normal subgroup

For a subgroup `N` of `G`, this file defines the group of modular linear
characters of `G` that are trivial on `N`.  When `N` is normal, it identifies
that group canonically with the linear characters of `G/N`.  A field action
preserving `N` acts on this subgroup, and the tensor-and-field action on the
actual function-valued `IBr` carrier restricts to the resulting semidirect
product.

The file does not identify `G`, `N`, or the field action with a particular
finite reductive group.  It proves no block or Lusztig-series stability.
-/

noncomputable section

namespace ModularRep

universe u v

variable {p : ℕ} {k G A : Type u} {K : Type v}
variable [Field k] [Field K] [Group G] [Finite G]
variable [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group A]

/-- The modular linear characters of `G` that are trivial on `N`. -/
def linearCharactersTrivialOn (N : Subgroup G) : Subgroup (G →* kˣ) where
  carrier lambda := N ≤ lambda.ker
  one_mem' := by
    intro n hn
    simp
  mul_mem' := by
    intro lambda mu hlambda hmu n hn
    change (lambda n * mu n : kˣ) = 1
    rw [hlambda hn, hmu hn, one_mul]
  inv_mem' := by
    intro lambda hlambda n hn
    change (lambda n)⁻¹ = 1
    rw [hlambda hn, inv_one]

namespace LinearCharactersTrivialOn

variable (N : Subgroup G)

@[simp]
theorem mem_iff (lambda : G →* kˣ) :
    lambda ∈ linearCharactersTrivialOn (k := k) N ↔ N ≤ lambda.ker :=
  Iff.rfl

/-- A modular linear character trivial on a normal subgroup is exactly a
modular linear character of the quotient. -/
def quotientMulEquiv [N.Normal] :
    linearCharactersTrivialOn (k := k) N ≃*
      (G ⧸ N →* kˣ) where
  toFun lambda := QuotientGroup.lift N lambda.1 lambda.2
  invFun lambda :=
    ⟨lambda.comp (QuotientGroup.mk' N), by
      intro n hn
      change lambda (QuotientGroup.mk' N n) = 1
      calc
        lambda (QuotientGroup.mk' N n) = lambda 1 :=
          congrArg lambda ((QuotientGroup.eq_one_iff n).mpr hn)
        _ = 1 := map_one lambda⟩
  left_inv lambda := by
    apply Subtype.ext
    ext g
    rfl
  right_inv lambda := by
    ext g
    rfl
  map_mul' lambda mu := by
    ext g
    rfl

@[simp]
theorem quotientMulEquiv_mk_apply [N.Normal]
    (lambda : linearCharactersTrivialOn (k := k) N) (g : G) :
    quotientMulEquiv (k := k) N lambda (QuotientGroup.mk' N g) =
      lambda.1 g :=
  rfl

/-- The source-shaped assertion that every automorphism in `field` preserves
the specified subgroup. -/
def IsFieldStable (field : A →* MulAut G) : Prop :=
  ∀ (a : A) (g : G), g ∈ N → field a g ∈ N

variable {N}

/-- Pullback by a field automorphism restricts to the linear characters that
are trivial on a field-stable subgroup. -/
def precompMulEquiv
    (field : A →* MulAut G)
    (hstable : IsFieldStable N field) (a : A) :
    linearCharactersTrivialOn (k := k) N ≃*
      linearCharactersTrivialOn (k := k) N where
  toFun lambda :=
    ⟨lambda.1.comp (field a⁻¹).toMonoidHom, by
      intro n hn
      change lambda.1 (field a⁻¹ n) = 1
      exact lambda.2 (hstable a⁻¹ n hn)⟩
  invFun lambda :=
    ⟨lambda.1.comp (field a).toMonoidHom, by
      intro n hn
      change lambda.1 (field a n) = 1
      exact lambda.2 (hstable a n hn)⟩
  left_inv lambda := by
    apply Subtype.ext
    ext g
    simp
  right_inv lambda := by
    apply Subtype.ext
    ext g
    simp
  map_mul' lambda mu := by
    apply Subtype.ext
    ext g
    rfl

@[simp]
theorem precompMulEquiv_apply
    (field : A →* MulAut G)
    (hstable : IsFieldStable N field) (a : A)
    (lambda : linearCharactersTrivialOn (k := k) N) (g : G) :
    (precompMulEquiv (k := k) field hstable a lambda).1 g =
      lambda.1 (field a⁻¹ g) :=
  rfl

/-- The field action on modular linear characters trivial on `N`. -/
def fieldAction
    (field : A →* MulAut G)
    (hstable : IsFieldStable N field) :
    A →* MulAut (linearCharactersTrivialOn (k := k) N) where
  toFun a := precompMulEquiv (k := k) field hstable a
  map_one' := by
    ext lambda g
    simp [precompMulEquiv]
  map_mul' a b := by
    ext lambda g
    simp [precompMulEquiv, mul_inv_rev]

end LinearCharactersTrivialOn

namespace IrreducibleBrauerCharacter

variable {N : Subgroup G}

/-- Restriction of the inverse tensor action to linear characters trivial on
`N`. -/
@[instance_reducible]
def inverseTrivialTensorAction
    (iota : PrimeRegularRootEmbedding p k K G)
    (productFormula : BrauerLinearTensorProductFormula iota) :
    MulAction (linearCharactersTrivialOn (k := k) N) (IBr iota) := by
  let _ : MulAction (G →* kˣ) (IBr iota) :=
    inverseTensorAction iota productFormula
  exact MulAction.compHom (IBr iota)
    (linearCharactersTrivialOn (k := k) N).subtype

/-- The restricted tensor action and the automorphism action satisfy the
semidirect compatibility law for a field-stable subgroup. -/
theorem trivialTensorField_semidirectCompatible
    (iota : PrimeRegularRootEmbedding p k K G)
    (productFormula : BrauerLinearTensorProductFormula iota)
    (field : A →* MulAut G)
    (hstable : LinearCharactersTrivialOn.IsFieldStable N field) :
    @Formalisation.SemidirectActionCompatible
      (linearCharactersTrivialOn (k := k) N) A (IBr iota) _ _
      (inverseTrivialTensorAction iota productFormula)
      (inverseAutomorphismAction iota field)
      (LinearCharactersTrivialOn.fieldAction (k := k) field hstable) := by
  intro a lambda phi
  apply Subtype.ext
  ext g
  rfl

/-- The literal tensor-and-field action for modular linear characters trivial
on `N`. -/
@[instance_reducible]
def trivialTensorFieldSemidirectAction
    (iota : PrimeRegularRootEmbedding p k K G)
    (productFormula : BrauerLinearTensorProductFormula iota)
    (field : A →* MulAut G)
    (hstable : LinearCharactersTrivialOn.IsFieldStable N field) :
    MulAction
      (linearCharactersTrivialOn (k := k) N ⋊[
        LinearCharactersTrivialOn.fieldAction (k := k) field hstable] A)
      (IBr iota) := by
  exact @Formalisation.semidirectMulAction
    (linearCharactersTrivialOn (k := k) N) A (IBr iota) _ _
    (inverseTrivialTensorAction iota productFormula)
    (inverseAutomorphismAction iota field)
    (LinearCharactersTrivialOn.fieldAction (k := k) field hstable)
    (trivialTensorField_semidirectCompatible iota productFormula field hstable)

/-- Elementwise formula for the restricted combined action. -/
theorem trivialTensorFieldSemidirectAction_apply
    (iota : PrimeRegularRootEmbedding p k K G)
    (productFormula : BrauerLinearTensorProductFormula iota)
    (field : A →* MulAut G)
    (hstable : LinearCharactersTrivialOn.IsFieldStable N field)
    (a : linearCharactersTrivialOn (k := k) N ⋊[LinearCharactersTrivialOn.fieldAction
      (k := k) field hstable] A)
    (phi : IBr iota) :
    let _ : MulAction
        (linearCharactersTrivialOn (k := k) N ⋊[LinearCharactersTrivialOn.fieldAction
          (k := k) field hstable] A)
        (IBr iota) :=
      trivialTensorFieldSemidirectAction iota productFormula field hstable
    a • phi = linearTwist iota productFormula
      (twist iota phi (field a.right⁻¹)) a.left.1⁻¹ := by
  rfl

end IrreducibleBrauerCharacter

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
