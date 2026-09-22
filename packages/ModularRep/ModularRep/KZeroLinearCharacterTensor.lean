import ModularRep.BrauerDecompositionMap
import ModularRep.LinearCharacterTensorAction

/-!
# Linear character tensoring on exact Grothendieck groups

This file constructs the operation induced on exact `K₀` by tensoring a
finite dimensional representation with a one dimensional representation.  It
then proves the character formula for that operation.  No block, basic-set, or
equivariant-bijection conclusion is assumed here.
-/

noncomputable section

open CategoryTheory

namespace ModularRep

universe u v

namespace FDRep

variable {k G : Type u} [Field k] [Group G]

/-- Tensor every object and morphism of `FDRep` by a fixed linear character.
The underlying vector space and linear map are unchanged. -/
noncomputable def linearCharacterTwistFunctor (lambda : G →* kˣ) :
    FDRep k G ⥤ FDRep k G where
  obj V := FDRep.of (Representation.linearCharacterTwist V.ρ lambda)
  map {V W} f :=
    { hom := FGModuleCat.ofHom f.hom.hom.hom
      comm := by
        intro g
        ext x
        change f.hom.hom.hom ((lambda g : k) • V.ρ g x) =
          (lambda g : k) • W.ρ g (f.hom.hom.hom x)
        rw [map_smul]
        exact congrArg (fun y ↦ (lambda g : k) • y)
          (ConcreteCategory.congr_hom (f.comm g) x) }
  map_id V := by
    ext x
    rfl
  map_comp f g := by
    ext x
    rfl

@[simp]
theorem linearCharacterTwistFunctor_obj_rho
    (lambda : G →* kˣ) (V : FDRep k G) :
    ((linearCharacterTwistFunctor lambda).obj V).ρ =
      Representation.linearCharacterTwist V.ρ lambda :=
  rfl

/-- Tensoring with a linear character is an autoequivalence, with inverse
given by tensoring with the inverse character. -/
noncomputable def linearCharacterTwistEquivalence (lambda : G →* kˣ) :
    FDRep k G ≌ FDRep k G where
  functor := linearCharacterTwistFunctor lambda
  inverse := linearCharacterTwistFunctor lambda⁻¹
  unitIso := NatIso.ofComponents (fun V ↦ by
    refine Action.mkIso
      (LinearEquiv.toFGModuleCatIso (LinearEquiv.refl k V)) (fun g ↦ ?_)
    ext x
    change V.ρ g x = (lambda⁻¹ g : k) • ((lambda g : k) • V.ρ g x)
    simp [smul_smul])
  counitIso := NatIso.ofComponents (fun V ↦ by
    refine Action.mkIso
      (LinearEquiv.toFGModuleCatIso (LinearEquiv.refl k V)) (fun g ↦ ?_)
    ext x
    change (lambda g : k) • ((lambda⁻¹ g : k) • V.ρ g x) = V.ρ g x
    simp [smul_smul])

@[simp]
theorem linearCharacterTwistEquivalence_functor_obj_rho
    (lambda : G →* kˣ) (V : FDRep k G) :
    ((linearCharacterTwistEquivalence lambda).functor.obj V).ρ =
      Representation.linearCharacterTwist V.ρ lambda :=
  rfl

end FDRep

open ExactGrothendieckGroup

variable {k G : Type u} [Field k] [Group G]

/-- Tensoring by a linear character on the exact Grothendieck group.  This
is induced by the actual exact autoequivalence of `FDRep`. -/
noncomputable def linearCharacterTwistKZero (lambda : G →* kˣ) :
    FDRepKZero k G →+ FDRepKZero k G :=
  ExactGrothendieckGroup.map
    (FDRep.linearCharacterTwistEquivalence lambda).functor

@[simp]
theorem linearCharacterTwistKZero_classOf
    (lambda : G →* kˣ) (V : FDRep k G) :
    linearCharacterTwistKZero lambda (classOf (FDRep k G) V) =
      classOf (FDRep k G)
        (FDRep.of (Representation.linearCharacterTwist V.ρ lambda)) :=
  ExactGrothendieckGroup.map_classOf
    (FDRep.linearCharacterTwistEquivalence lambda).functor V

/-- Tensoring by the trivial linear character acts trivially on exact
`K₀`. -/
theorem linearCharacterTwistKZero_one :
    linearCharacterTwistKZero (1 : G →* kˣ) =
      AddMonoidHom.id (FDRepKZero k G) := by
  apply ExactGrothendieckGroup.hom_ext
  intro V
  rw [linearCharacterTwistKZero_classOf]
  change classOf (FDRep k G)
      (FDRep.of (Representation.linearCharacterTwist V.ρ 1)) =
    classOf (FDRep k G) V
  rw [Representation.linearCharacterTwist_one]
  exact classOf_iso (FDRep k G) (fdRepOfRhoIso V)

/-- Successive tensor twists multiply their linear characters. -/
theorem linearCharacterTwistKZero_mul
    (lambda mu : G →* kˣ) :
    (linearCharacterTwistKZero mu).comp
        (linearCharacterTwistKZero lambda) =
      linearCharacterTwistKZero (lambda * mu) := by
  apply ExactGrothendieckGroup.hom_ext
  intro V
  rw [AddMonoidHom.comp_apply, linearCharacterTwistKZero_classOf,
    linearCharacterTwistKZero_classOf,
    linearCharacterTwistKZero_classOf]
  change classOf (FDRep k G)
      (FDRep.of
        ((Representation.linearCharacterTwist V.ρ lambda).linearCharacterTwist mu)) =
    classOf (FDRep k G)
      (FDRep.of (Representation.linearCharacterTwist V.ρ (lambda * mu)))
  rw [Representation.linearCharacterTwist_mul]

namespace PrimeRegularClassFunction

variable {p : ℕ} {K : Type u} [Field K]

/-- Restriction of a linear character to the prime regular elements. -/
def ofLinearCharacter (p : ℕ) (lambda : G →* Kˣ) :
    PrimeRegularClassFunction K G p where
  toFun g := (lambda g.1 : K)
  map_conj x g := by simp

@[simp]
theorem ofLinearCharacter_apply
    (p : ℕ) (lambda : G →* Kˣ)
    (g : PrimeRegularElement (G := G) p) :
    ofLinearCharacter p lambda g = (lambda g.1 : K) :=
  rfl

/-- Left multiplication by a fixed class function as an additive
homomorphism. -/
def leftMultiplyAddHom (f : PrimeRegularClassFunction K G p) :
    PrimeRegularClassFunction K G p →+
      PrimeRegularClassFunction K G p where
  toFun q :=
    { toFun := fun g ↦ f g * q g
      map_conj := fun x g ↦ by rw [f.map_conj x g, q.map_conj x g] }
  map_zero' := by ext g; simp
  map_add' q r := by ext g; simp [mul_add]

@[simp]
theorem leftMultiplyAddHom_apply
    (f q : PrimeRegularClassFunction K G p)
    (g : PrimeRegularElement (G := G) p) :
    leftMultiplyAddHom f q g = f g * q g :=
  rfl

end PrimeRegularClassFunction

variable {p : ℕ} {K : Type u} [Field K]

/-- The ordinary-character homomorphism on exact `K₀` intertwines
linear character tensoring with pointwise multiplication. -/
theorem ordinaryCharacterKZero_linearCharacterTwist
    (lambda : G →* Kˣ) :
    (ordinaryCharacterKZero (K := K) (G := G) p).comp
        (linearCharacterTwistKZero lambda) =
      (PrimeRegularClassFunction.leftMultiplyAddHom
        (PrimeRegularClassFunction.ofLinearCharacter p lambda)).comp
        (ordinaryCharacterKZero (K := K) (G := G) p) := by
  apply ExactGrothendieckGroup.hom_ext
  intro V
  rw [AddMonoidHom.comp_apply, linearCharacterTwistKZero_classOf,
    ordinaryCharacterKZero_classOf, AddMonoidHom.comp_apply,
    ordinaryCharacterKZero_classOf]
  ext g
  exact Representation.character_linearCharacterTwist V.ρ lambda g.1

/-- The left action on exact `K₀` which encodes the manuscript's right
tensor action. -/
noncomputable def inverseLinearCharacterTwistKZeroRepresentation :
    Representation ℤ (G →* kˣ) (FDRepKZero k G) where
  toFun lambda :=
    (linearCharacterTwistKZero (Inv.inv lambda)).toIntLinearMap
  map_one' := by
    apply LinearMap.toAddMonoidHom_injective
    change linearCharacterTwistKZero (Inv.inv (1 : G →* kˣ)) =
      AddMonoidHom.id (FDRepKZero k G)
    have hone : (1 : G →* kˣ)⁻¹ = (1 : G →* kˣ) := by
      ext g
      simp
    rw [hone]
    apply linearCharacterTwistKZero_one
  map_mul' lambda mu := by
    apply LinearMap.toAddMonoidHom_injective
    change linearCharacterTwistKZero (Inv.inv (lambda * mu)) =
      (linearCharacterTwistKZero (Inv.inv lambda)).comp
        (linearCharacterTwistKZero (Inv.inv mu))
    have hinv : (lambda * mu)⁻¹ =
        mu⁻¹ * lambda⁻¹ := mul_inv_rev lambda mu
    rw [hinv]
    exact (linearCharacterTwistKZero_mul (k := k) (G := G)
      (Inv.inv mu) (Inv.inv lambda)).symm

@[simp]
theorem inverseLinearCharacterTwistKZeroRepresentation_apply
    (lambda : G →* kˣ) (x : FDRepKZero k G) :
    inverseLinearCharacterTwistKZeroRepresentation lambda x =
      linearCharacterTwistKZero (Inv.inv lambda) x :=
  rfl

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
