import ModularRep.KZeroLinearCharacterDecomposition

/-!
# Tensor and automorphism actions on exact Grothendieck groups

This file combines the exact `K₀` action from linear character tensoring
with automorphism pullback.  The compatibility is proved from a natural
isomorphism of the underlying exact functors, rather than assumed on labels.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ModularRep

open ExactGrothendieckGroup

universe u

namespace ExactGrothendieckGroup

variable {k G : Type u} [Field k] [Group G]

/-- Exact `K₀` maps respect composition of exact endofunctors. -/
theorem map_comp_fdRep
    (F H : FDRep k G ⥤ FDRep k G)
    [CategoryTheory.Functor.PreservesZeroMorphisms F] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F]
    [CategoryTheory.Functor.PreservesZeroMorphisms H] [PreservesFiniteLimits H]
    [PreservesFiniteColimits H]
    [PreservesFiniteLimits (F ⋙ H)] [PreservesFiniteColimits (F ⋙ H)] :
    (map H).comp (map F) = map (F ⋙ H) := by
  apply hom_ext
  intro V
  rw [AddMonoidHom.comp_apply, map_classOf, map_classOf, map_classOf]
  rfl

/-- Naturally isomorphic exact endofunctors induce the same endomorphism
of exact `K₀`. -/
theorem map_eq_of_natIso_fdRep
    (F H : FDRep k G ⥤ FDRep k G)
    [CategoryTheory.Functor.PreservesZeroMorphisms F] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F]
    [CategoryTheory.Functor.PreservesZeroMorphisms H] [PreservesFiniteLimits H]
    [PreservesFiniteColimits H]
    (e : F ≅ H) :
    map F = map H := by
  apply hom_ext
  intro V
  rw [map_classOf, map_classOf]
  exact classOf_iso (FDRep k G) (e.app V)

end ExactGrothendieckGroup

namespace FDRep

variable {k G : Type u} [Field k] [Group G]

/-- Tensoring and automorphism pullback commute as exact functors after
pulling back the linear character. -/
noncomputable def linearCharacterTwistTwistIso
    (lambda : G →* kˣ) (alpha : MulAut G) :
    (linearCharacterTwistEquivalence lambda).functor ⋙
        (twistEquivalence k G alpha).functor ≅
      (twistEquivalence k G alpha).functor ⋙
        (linearCharacterTwistEquivalence
          (lambda.comp alpha.toMonoidHom)).functor :=
  NatIso.ofComponents (fun V ↦ by
    refine Action.mkIso
      (LinearEquiv.toFGModuleCatIso (LinearEquiv.refl k V)) (fun g ↦ ?_)
    ext x
    rfl)

end FDRep

variable {k G : Type u} [Field k] [Group G]

/-- Automorphism pullback and linear character tensoring commute on exact
`K₀`, with the linear character pulled back by the same automorphism. -/
theorem twistKZero_linearCharacterTwistKZero
    (lambda : G →* kˣ) (alpha : MulAut G) :
    (twistKZero (k := k) alpha).comp
        (linearCharacterTwistKZero lambda) =
      (linearCharacterTwistKZero
        (lambda.comp alpha.toMonoidHom)).comp
        (twistKZero (k := k) alpha) := by
  calc
    (twistKZero (k := k) alpha).comp
        (linearCharacterTwistKZero lambda) =
        ExactGrothendieckGroup.map
          ((FDRep.linearCharacterTwistEquivalence lambda).functor ⋙
            (FDRep.twistEquivalence k G alpha).functor) :=
      ExactGrothendieckGroup.map_comp_fdRep _ _
    _ = ExactGrothendieckGroup.map
          ((FDRep.twistEquivalence k G alpha).functor ⋙
            (FDRep.linearCharacterTwistEquivalence
              (lambda.comp alpha.toMonoidHom)).functor) :=
      ExactGrothendieckGroup.map_eq_of_natIso_fdRep _ _
        (FDRep.linearCharacterTwistTwistIso lambda alpha)
    _ = (linearCharacterTwistKZero
          (lambda.comp alpha.toMonoidHom)).comp
          (twistKZero (k := k) alpha) :=
      (ExactGrothendieckGroup.map_comp_fdRep _ _).symm

variable {A : Type u} [Group A]

/-- The left field action on exact `K₀` which encodes the manuscript's
right automorphism action. -/
noncomputable def inverseFieldTwistKZeroRepresentation
    (field : A →* MulAut G) :
    Representation ℤ A (FDRepKZero k G) where
  toFun a := (twistKZero (k := k) (field a⁻¹)).toIntLinearMap
  map_one' := by
    apply LinearMap.toAddMonoidHom_injective
    change twistKZero (k := k) (field (1 : A)⁻¹) =
      AddMonoidHom.id (FDRepKZero k G)
    rw [inv_one, map_one]
    exact twistKZero_refl (k := k) (G := G)
  map_mul' a b := by
    apply LinearMap.toAddMonoidHom_injective
    change twistKZero (k := k) (field (a * b)⁻¹) =
      (twistKZero (k := k) (field a⁻¹)).comp
        (twistKZero (k := k) (field b⁻¹))
    rw [mul_inv_rev, map_mul]
    exact (twistKZero_comp (k := k) (G := G)
      (field a⁻¹) (field b⁻¹)).symm

@[simp]
theorem inverseFieldTwistKZeroRepresentation_apply
    (field : A →* MulAut G) (a : A) (x : FDRepKZero k G) :
    inverseFieldTwistKZeroRepresentation (k := k) field a x =
      twistKZero (k := k) (field a⁻¹) x :=
  rfl

/-- The exact `K₀` tensor and field actions satisfy the compatibility
identity for the same semidirect product as the character actions. -/
theorem inverseTensorFieldKZero_compatible
    (field : A →* MulAut G) (a : A) (lambda : G →* kˣ)
    (x : FDRepKZero k G) :
    inverseFieldTwistKZeroRepresentation (k := k) field a
        (inverseLinearCharacterTwistKZeroRepresentation lambda x) =
      inverseLinearCharacterTwistKZeroRepresentation
        (OrdinaryIrreducibleCharacter.linearCharacterFieldAction
          (k := k) field a lambda)
        (inverseFieldTwistKZeroRepresentation (k := k) field a x) := by
  let alpha : MulAut G := field a⁻¹
  have hinv :
      (OrdinaryIrreducibleCharacter.linearCharacterFieldAction
          (k := k) field a lambda)⁻¹ =
        lambda⁻¹.comp alpha.toMonoidHom := by
    ext g
    rfl
  change twistKZero (k := k) alpha
      (linearCharacterTwistKZero lambda⁻¹ x) =
    linearCharacterTwistKZero
      (OrdinaryIrreducibleCharacter.linearCharacterFieldAction
        (k := k) field a lambda)⁻¹
      (twistKZero (k := k) alpha x)
  rw [hinv]
  exact DFunLike.congr_fun
    (twistKZero_linearCharacterTwistKZero
      (k := k) (G := G) lambda⁻¹ alpha) x

/-- The exact `K₀` representation of the tensor and field semidirect
product.  It is constructed from the actual exact autoequivalences, not from
an action on character labels. -/
noncomputable def tensorFieldKZeroRepresentation
    (field : A →* MulAut G) :
    Representation ℤ
      ((G →* kˣ) ⋊[
        OrdinaryIrreducibleCharacter.linearCharacterFieldAction
          (k := k) field] A)
      (FDRepKZero k G) where
  toFun z :=
    inverseLinearCharacterTwistKZeroRepresentation z.left *
      inverseFieldTwistKZeroRepresentation (k := k) field z.right
  map_one' := by
    change
      inverseLinearCharacterTwistKZeroRepresentation (1 : G →* kˣ) *
        inverseFieldTwistKZeroRepresentation (k := k) field (1 : A) = 1
    rw [map_one, map_one]
    exact one_mul _
  map_mul' z w := by
    ext x
    change
      inverseLinearCharacterTwistKZeroRepresentation
          ((z * w).left)
          (inverseFieldTwistKZeroRepresentation (k := k) field
            ((z * w).right) x) =
        inverseLinearCharacterTwistKZeroRepresentation z.left
          (inverseFieldTwistKZeroRepresentation (k := k) field z.right
            (inverseLinearCharacterTwistKZeroRepresentation w.left
              (inverseFieldTwistKZeroRepresentation (k := k) field
                w.right x)))
    rw [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
      map_mul, map_mul]
    change
      inverseLinearCharacterTwistKZeroRepresentation z.left
          (inverseLinearCharacterTwistKZeroRepresentation
            (OrdinaryIrreducibleCharacter.linearCharacterFieldAction
              (k := k) field z.right w.left)
            (inverseFieldTwistKZeroRepresentation (k := k) field z.right
              (inverseFieldTwistKZeroRepresentation (k := k) field w.right x))) =
        inverseLinearCharacterTwistKZeroRepresentation z.left
          (inverseFieldTwistKZeroRepresentation (k := k) field z.right
            (inverseLinearCharacterTwistKZeroRepresentation w.left
              (inverseFieldTwistKZeroRepresentation (k := k) field
                w.right x)))
    congr 1
    exact (inverseTensorFieldKZero_compatible
      (k := k) field z.right w.left
        (inverseFieldTwistKZeroRepresentation (k := k) field w.right x)).symm

@[simp]
theorem tensorFieldKZeroRepresentation_apply
    (field : A →* MulAut G)
    (z : (G →* kˣ) ⋊[OrdinaryIrreducibleCharacter.linearCharacterFieldAction
        (k := k) field] A)
    (x : FDRepKZero k G) :
    tensorFieldKZeroRepresentation (k := k) field z x =
      linearCharacterTwistKZero z.left⁻¹
        (twistKZero (k := k) (field z.right⁻¹) x) :=
  rfl

variable {D : Type u} [Group D]

/-- Map an abstract diagonal-and-field semidirect product to the literal
semidirect product of linear characters and field automorphisms.  The sole
compatibility premise says that the selected linear characters are stable
under the prescribed field action. -/
def linearCharacterSemidirectMap
    (phi : A →* MulAut D) (field : A →* MulAut G)
    (linearCharacter : D →* (G →* kˣ))
    (hfield : ∀ a : A,
      linearCharacter.comp (phi a).toMonoidHom =
        (OrdinaryIrreducibleCharacter.linearCharacterFieldAction
          (k := k) field a).toMonoidHom.comp linearCharacter) :
    D ⋊[phi] A →*
      (G →* kˣ) ⋊[
        OrdinaryIrreducibleCharacter.linearCharacterFieldAction
          (k := k) field] A :=
  SemidirectProduct.map linearCharacter (MonoidHom.id A) (by
    intro a
    simpa using hfield a)

/-- Pull back the literal tensor-and-field `K₀` representation along a
selected group of linear characters. -/
noncomputable def tensorFieldKZeroRepresentationOf
    (phi : A →* MulAut D) (field : A →* MulAut G)
    (linearCharacter : D →* (G →* kˣ))
    (hfield : ∀ a : A,
      linearCharacter.comp (phi a).toMonoidHom =
        (OrdinaryIrreducibleCharacter.linearCharacterFieldAction
          (k := k) field a).toMonoidHom.comp linearCharacter) :
    Representation ℤ (D ⋊[phi] A) (FDRepKZero k G) :=
  (tensorFieldKZeroRepresentation (k := k) field).pullback
    (linearCharacterSemidirectMap phi field linearCharacter hfield)

@[simp]
theorem tensorFieldKZeroRepresentationOf_apply
    (phi : A →* MulAut D) (field : A →* MulAut G)
    (linearCharacter : D →* (G →* kˣ))
    (hfield : ∀ a : A,
      linearCharacter.comp (phi a).toMonoidHom =
        (OrdinaryIrreducibleCharacter.linearCharacterFieldAction
          (k := k) field a).toMonoidHom.comp linearCharacter)
    (z : D ⋊[phi] A) (x : FDRepKZero k G) :
    tensorFieldKZeroRepresentationOf
        phi field linearCharacter hfield z x =
      linearCharacterTwistKZero (linearCharacter z.left)⁻¹
        (twistKZero (k := k) (field z.right⁻¹) x) :=
  rfl

variable {p : ℕ} {K O : Type u}
variable [Field K] [CommRing O] [IsDomain O] [Algebra O K]
variable [Finite G] [CharP k p] [IsAlgClosed k] [CharZero K]

/-- The exact decomposition map intertwines the tensor-and-field
representations attached to any compatible ordinary and modular families of
linear characters.  The premises concern only the source-specific choice of
those families and their field action; no blockwise bijection is assumed. -/
theorem decompositionMapOfStableReduction_tensorFieldKZeroRepresentationOf
    (Msys : ModularSystem p K O k)
    (iota : PrimeRegularRootEmbedding p k K G)
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (productFormula : BrauerLinearTensorProductFormula iota)
    (phi : A →* MulAut D) (field : A →* MulAut G)
    (linearCharacterK : D →* (G →* Kˣ))
    (linearCharacterk : D →* (G →* kˣ))
    (hfieldK : ∀ a : A,
      linearCharacterK.comp (phi a).toMonoidHom =
        (OrdinaryIrreducibleCharacter.linearCharacterFieldAction
          (k := K) field a).toMonoidHom.comp linearCharacterK)
    (hfieldk : ∀ a : A,
      linearCharacterk.comp (phi a).toMonoidHom =
        (OrdinaryIrreducibleCharacter.linearCharacterFieldAction
          (k := k) field a).toMonoidHom.comp linearCharacterk)
    (hlinear : ∀ d : D,
      LinearCharacterReductionCompatible iota
        (linearCharacterK d) (linearCharacterk d))
    (z : D ⋊[phi] A) (x : FDRepKZero K G) :
    decompositionMapOfStableReduction Msys iota hcompat
        (tensorFieldKZeroRepresentationOf
          phi field linearCharacterK hfieldK z x) =
      tensorFieldKZeroRepresentationOf
        phi field linearCharacterk hfieldk z
        (decompositionMapOfStableReduction Msys iota hcompat x) := by
  rw [tensorFieldKZeroRepresentationOf_apply,
    tensorFieldKZeroRepresentationOf_apply]
  have hz : LinearCharacterReductionCompatible iota
      (linearCharacterK z.left)⁻¹ (linearCharacterk z.left)⁻¹ := by
    simpa using hlinear z.left⁻¹
  exact decompositionMapOfStableReduction_linearCharacterTwist_twist
    Msys iota hcompat productFormula
      (linearCharacterK z.left)⁻¹ (linearCharacterk z.left)⁻¹ hz
      (field z.right⁻¹) x

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
