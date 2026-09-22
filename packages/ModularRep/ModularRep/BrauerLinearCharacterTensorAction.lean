import ModularRep.IBrSimpleModuleClass
import ModularRep.LinearCharacterTensorAction

/-!
# Tensoring irreducible Brauer characters by linear characters

This file constructs the action of linear characters on irreducible Brauer
characters `IBr` by tensor product. It assumes the standard formula for
the Brauer character of a tensor product: the pointwise product of the
Brauer characters of its factors. The required case is stated as
`BrauerLinearTensorProductFormula`; see Navarro, Theorem (2.23), p. 33.

No block, Lusztig-series, or inductive Alperin weight conclusion occurs here.
-/

noncomputable section

namespace ModularRep

universe u v

variable {p : ℕ} {k G : Type u} {K : Type v}
variable [Field k] [Field K] [Group G] [Finite G]
variable [CharP k p] [IsAlgClosed k] [CharZero K]

namespace PrimeRegularClassFunction

/-- Pointwise multiplication of prime regular class functions. -/
def pointwiseMul
    (f q : PrimeRegularClassFunction K G p) :
    PrimeRegularClassFunction K G p where
  toFun g := f g * q g
  map_conj x g := by rw [f.map_conj x g, q.map_conj x g]

@[simp]
theorem pointwiseMul_apply
    (f q : PrimeRegularClassFunction K G p)
    (g : PrimeRegularElement (G := G) p) :
    pointwiseMul f q g = f g * q g :=
  rfl

end PrimeRegularClassFunction

namespace PrimeRegularRootEmbedding

/-- The value of a modular linear character on a prime regular element,
regarded as one of the roots on which the chosen root embedding is defined. -/
def linearCharacterRoot
    (iota : PrimeRegularRootEmbedding p k K G)
    (lambda : G →* kˣ)
    (g : PrimeRegularElement (G := G) p) :
    rootsOfUnity (primeRegularExponent p G) k := by
  letI : NeZero (primeRegularExponent p G) :=
    ⟨(primeRegularExponent_pos p G).ne'⟩
  apply rootsOfUnity.mkOfPowEq ((lambda g.1 : k))
  have hg := g.pow_primeRegularExponent_eq_one iota.prime
  change (lambda g.1 : k) ^ primeRegularExponent p G = 1
  have hmap := congrArg (fun z : kˣ ↦ (z : k)) (congrArg lambda hg)
  simpa using hmap

@[simp]
theorem coe_linearCharacterRoot
    (iota : PrimeRegularRootEmbedding p k K G)
    (lambda : G →* kˣ)
    (g : PrimeRegularElement (G := G) p) :
    ((((iota.linearCharacterRoot lambda g :
        rootsOfUnity (primeRegularExponent p G) k) : kˣ) : k)) =
      (lambda g.1 : k) :=
  rfl

/-- The characteristic-zero lift of a modular linear character on prime
regular elements. -/
def liftedLinearCharacter
    (iota : PrimeRegularRootEmbedding p k K G)
    (lambda : G →* kˣ) : PrimeRegularClassFunction K G p where
  toFun g := iota.liftRoot (iota.linearCharacterRoot lambda g)
  map_conj x g := by
    apply congrArg iota.liftRoot
    apply Subtype.ext
    apply Units.ext
    change (lambda (x * g.1 * x⁻¹) : k) = (lambda g.1 : k)
    simp

@[simp]
theorem liftedLinearCharacter_apply
    (iota : PrimeRegularRootEmbedding p k K G)
    (lambda : G →* kˣ)
    (g : PrimeRegularElement (G := G) p) :
    iota.liftedLinearCharacter lambda g =
      iota.liftRoot (iota.linearCharacterRoot lambda g) :=
  rfl

@[simp]
theorem liftedLinearCharacter_one
    (iota : PrimeRegularRootEmbedding p k K G) :
    iota.liftedLinearCharacter (1 : G →* kˣ) =
      PrimeRegularClassFunction.ofFunction (p := p) (1 : G → K)
        (fun _ _ ↦ rfl) := by
  ext g
  change iota.liftRoot (iota.linearCharacterRoot 1 g) = 1
  change (((iota.toMulEquiv (iota.linearCharacterRoot 1 g) :
    rootsOfUnity (primeRegularExponent p G) K) : Kˣ) : K) = 1
  have hroot : iota.linearCharacterRoot (1 : G →* kˣ) g = 1 := by
    apply Subtype.ext
    apply Units.ext
    rfl
  rw [hroot, map_one]
  rfl

@[simp]
theorem liftedLinearCharacter_mul
    (iota : PrimeRegularRootEmbedding p k K G)
    (lambda mu : G →* kˣ) :
    iota.liftedLinearCharacter (lambda * mu) =
      PrimeRegularClassFunction.pointwiseMul
        (iota.liftedLinearCharacter lambda)
        (iota.liftedLinearCharacter mu) := by
  ext g
  change iota.liftRoot (iota.linearCharacterRoot (lambda * mu) g) =
    iota.liftRoot (iota.linearCharacterRoot lambda g) *
      iota.liftRoot (iota.linearCharacterRoot mu g)
  have hroot :
      iota.linearCharacterRoot (lambda * mu) g =
        iota.linearCharacterRoot lambda g *
          iota.linearCharacterRoot mu g := by
    apply Subtype.ext
    apply Units.ext
    rfl
  rw [hroot]
  change (((iota.toMulEquiv
    (iota.linearCharacterRoot lambda g *
      iota.linearCharacterRoot mu g) :
      rootsOfUnity (primeRegularExponent p G) K) : Kˣ) : K) = _
  rw [map_mul]
  rfl

@[simp]
theorem liftedLinearCharacter_twist
    (iota : PrimeRegularRootEmbedding p k K G)
    (lambda : G →* kˣ) (alpha : MulAut G) :
    (iota.liftedLinearCharacter lambda).twist alpha =
      iota.liftedLinearCharacter (lambda.comp alpha.toMonoidHom) := by
  ext g
  rfl

end PrimeRegularRootEmbedding

/-- The assumed tensor product formula: tensoring a modular representation
by a linear character multiplies its Brauer character by the lifted
linear character. This is the case with a one dimensional factor in
Navarro, Theorem (2.23), p. 33. -/
def BrauerLinearTensorProductFormula
    (iota : PrimeRegularRootEmbedding p k K G) : Prop :=
  ∀ (V : FDRep k G) (lambda : G →* kˣ),
    Representation.brauerCharacterOfRootEmbedding
        (Representation.linearCharacterTwist V.ρ lambda) iota =
      PrimeRegularClassFunction.pointwiseMul
        (iota.liftedLinearCharacter lambda)
        (Representation.brauerCharacterOfRootEmbedding V.ρ iota)

namespace IrreducibleBrauerCharacter

/-- Tensor a function-valued irreducible Brauer character by a modular
linear character. -/
def linearTwist
    (iota : PrimeRegularRootEmbedding p k K G)
    (productFormula : BrauerLinearTensorProductFormula iota)
    (phi : IBr iota) (lambda : G →* kˣ) : IBr iota := by
  refine ⟨PrimeRegularClassFunction.pointwiseMul
      (iota.liftedLinearCharacter lambda) phi.1, ?_⟩
  rcases phi.2 with ⟨V, hV, hphi⟩
  refine ⟨FDRep.of (Representation.linearCharacterTwist V.ρ lambda),
    hV.linearCharacterTwist lambda, ?_⟩
  rw [FDRep.of_ρ', productFormula V lambda, hphi]

@[simp]
theorem linearTwist_val
    (iota : PrimeRegularRootEmbedding p k K G)
    (productFormula : BrauerLinearTensorProductFormula iota)
    (phi : IBr iota) (lambda : G →* kˣ) :
    (linearTwist iota productFormula phi lambda).1 =
      PrimeRegularClassFunction.pointwiseMul
        (iota.liftedLinearCharacter lambda) phi.1 :=
  rfl

@[simp]
theorem linearTwist_apply
    (iota : PrimeRegularRootEmbedding p k K G)
    (productFormula : BrauerLinearTensorProductFormula iota)
    (phi : IBr iota) (lambda : G →* kˣ)
    (g : PrimeRegularElement (G := G) p) :
    (linearTwist iota productFormula phi lambda).1 g =
      iota.liftedLinearCharacter lambda g * phi.1 g :=
  rfl

@[simp]
theorem linearTwist_one
    (iota : PrimeRegularRootEmbedding p k K G)
    (productFormula : BrauerLinearTensorProductFormula iota)
    (phi : IBr iota) :
    linearTwist iota productFormula phi (1 : G →* kˣ) = phi := by
  apply Subtype.ext
  ext g
  change iota.liftedLinearCharacter (1 : G →* kˣ) g * phi.1 g = phi.1 g
  have hone : iota.liftedLinearCharacter (1 : G →* kˣ) g = 1 := by
    change iota.liftRoot (iota.linearCharacterRoot 1 g) = 1
    have hroot : iota.linearCharacterRoot (1 : G →* kˣ) g = 1 := by
      apply Subtype.ext
      apply Units.ext
      rfl
    rw [hroot]
    change ((((iota.toMulEquiv 1 :
      rootsOfUnity (primeRegularExponent p G) K) : Kˣ) : K)) = 1
    rw [map_one]
    rfl
  rw [hone, one_mul]

@[simp]
theorem linearTwist_mul
    (iota : PrimeRegularRootEmbedding p k K G)
    (productFormula : BrauerLinearTensorProductFormula iota)
    (phi : IBr iota) (lambda mu : G →* kˣ) :
    linearTwist iota productFormula
        (linearTwist iota productFormula phi lambda) mu =
      linearTwist iota productFormula phi (lambda * mu) := by
  apply Subtype.ext
  ext g
  change iota.liftedLinearCharacter mu g *
      (iota.liftedLinearCharacter lambda g * phi.1 g) =
    iota.liftedLinearCharacter (lambda * mu) g * phi.1 g
  rw [PrimeRegularRootEmbedding.liftedLinearCharacter_mul]
  change _ =
    (iota.liftedLinearCharacter lambda g *
      iota.liftedLinearCharacter mu g) * phi.1 g
  ring

/-- Tensoring and automorphism pullback commute after pulling back the
linear character by the same automorphism. -/
theorem twist_linearTwist
    (iota : PrimeRegularRootEmbedding p k K G)
    (productFormula : BrauerLinearTensorProductFormula iota)
    (phi : IBr iota) (lambda : G →* kˣ) (alpha : MulAut G) :
    twist iota (linearTwist iota productFormula phi lambda) alpha =
      linearTwist iota productFormula (twist iota phi alpha)
        (lambda.comp alpha.toMonoidHom) := by
  apply Subtype.ext
  ext g
  rfl

variable {A : Type u} [Group A]

/-- Tensoring by modular linear characters as a left action encoding the
manuscript's right action. -/
@[instance_reducible]
def inverseTensorAction
    (iota : PrimeRegularRootEmbedding p k K G)
    (productFormula : BrauerLinearTensorProductFormula iota) :
    MulAction (G →* kˣ) (IBr iota) where
  smul lambda phi := linearTwist iota productFormula phi lambda⁻¹
  one_smul phi := by
    apply Subtype.ext
    ext g
    change iota.liftedLinearCharacter ((1 : G →* kˣ)⁻¹) g *
      phi.1 g = phi.1 g
    have hone :
        iota.liftedLinearCharacter ((1 : G →* kˣ)⁻¹) g = 1 := by
      change iota.liftRoot (iota.linearCharacterRoot (1 : G →* kˣ)⁻¹ g) = 1
      have hroot :
          iota.linearCharacterRoot (1 : G →* kˣ)⁻¹ g = 1 := by
        apply Subtype.ext
        apply Units.ext
        simp
      rw [hroot]
      change ((((iota.toMulEquiv 1 :
        rootsOfUnity (primeRegularExponent p G) K) : Kˣ) : K)) = 1
      rw [map_one]
      rfl
    rw [hone, one_mul]
  mul_smul lambda mu phi := by
    change linearTwist iota productFormula phi (lambda * mu)⁻¹ =
      linearTwist iota productFormula
        (linearTwist iota productFormula phi mu⁻¹) lambda⁻¹
    calc
      linearTwist iota productFormula phi (lambda * mu)⁻¹ =
          linearTwist iota productFormula phi (mu⁻¹ * lambda⁻¹) := by
            exact congrArg (linearTwist iota productFormula phi)
              (mul_inv_rev lambda mu)
      _ = linearTwist iota productFormula
          (linearTwist iota productFormula phi mu⁻¹) lambda⁻¹ :=
        (linearTwist_mul iota productFormula phi mu⁻¹ lambda⁻¹).symm

/-- Automorphism pullback as a left action encoding the manuscript's right
action. -/
@[instance_reducible]
def inverseAutomorphismAction
    (iota : PrimeRegularRootEmbedding p k K G)
    (field : A →* MulAut G) : MulAction A (IBr iota) where
  smul a phi := twist iota phi (field a⁻¹)
  one_smul phi := by
    change twist iota phi (field (1 : A)⁻¹) = phi
    rw [inv_one, map_one]
    exact twist_refl iota phi
  mul_smul a b phi := by
    change twist iota phi (field (a * b)⁻¹) =
      twist iota (twist iota phi (field b⁻¹)) (field a⁻¹)
    rw [mul_inv_rev, map_mul]
    exact (twist_mul iota phi (field b⁻¹) (field a⁻¹)).symm

/-- The actual Brauer tensor and automorphism actions satisfy the
semidirect compatibility identity. -/
theorem tensorField_semidirectCompatible
    (iota : PrimeRegularRootEmbedding p k K G)
    (productFormula : BrauerLinearTensorProductFormula iota)
    (field : A →* MulAut G) :
    @Formalisation.SemidirectActionCompatible
      (G →* kˣ) A (IBr iota) _ _
      (inverseTensorAction iota productFormula)
      (inverseAutomorphismAction iota field)
      (OrdinaryIrreducibleCharacter.linearCharacterFieldAction
        (k := k) field) := by
  intro a lambda phi
  apply Subtype.ext
  ext g
  rfl

/-- The semidirect product action of linear characters and automorphisms on
the set of irreducible Brauer characters. -/
@[instance_reducible]
def tensorFieldSemidirectAction
    (iota : PrimeRegularRootEmbedding p k K G)
    (productFormula : BrauerLinearTensorProductFormula iota)
    (field : A →* MulAut G) :
    MulAction
      ((G →* kˣ) ⋊[OrdinaryIrreducibleCharacter.linearCharacterFieldAction
          (k := k) field] A)
      (IBr iota) := by
  exact @Formalisation.semidirectMulAction
    (G →* kˣ) A (IBr iota) _ _
    (inverseTensorAction iota productFormula)
    (inverseAutomorphismAction iota field)
    (OrdinaryIrreducibleCharacter.linearCharacterFieldAction
      (k := k) field)
    (tensorField_semidirectCompatible iota productFormula field)

/-- Elementwise formula for the combined Brauer-character action. -/
theorem tensorFieldSemidirectAction_apply
    (iota : PrimeRegularRootEmbedding p k K G)
    (productFormula : BrauerLinearTensorProductFormula iota)
    (field : A →* MulAut G)
    (a : (G →* kˣ) ⋊[OrdinaryIrreducibleCharacter.linearCharacterFieldAction
        (k := k) field] A)
    (phi : IBr iota) :
    let _ : MulAction
        ((G →* kˣ) ⋊[OrdinaryIrreducibleCharacter.linearCharacterFieldAction
            (k := k) field] A)
        (IBr iota) :=
      tensorFieldSemidirectAction iota productFormula field
    a • phi = linearTwist iota productFormula
      (twist iota phi (field a.right⁻¹)) a.left⁻¹ := by
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
