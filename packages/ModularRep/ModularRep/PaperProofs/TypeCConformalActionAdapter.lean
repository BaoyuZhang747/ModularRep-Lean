import ModularRep.BrauerQuotientLinearCharacterAction

/-!
# The conformal tensor and field action in Proposition 3.11

This file specialises the generic tensor action to the source-shaped group
used in the odd-field conformal argument.  If `G0` is a normal subgroup of
`G`, the tensor subgroup is the group of modular linear characters of `G`
that are trivial on `G0`.  Lean identifies this group, including its field
action, with the linear characters of `G / G0`.

For ordinary characters the manuscript uses the ordinary linear characters
whose reductions give those modular quotient characters.  Their existence
and field compatibility are kept in the explicit structure
`OrdinaryReductionEquiv`; they are not attributed to the ordinary tensor
formula alone.  From this structure Lean constructs the actual combined
ordinary tensor and field action.

Finally, separate source-shaped stability assertions are used to restrict the
constructed actions to the ordinary Lusztig-series part of one block and to
the Brauer characters of that block.  The acting group is the literal
stabiliser of the block in the tensor and field semidirect product.  No
blockwise bijection, decomposition-map naturality, Conlon conclusion, or
inductive condition is an input or conclusion of this file.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeCConformalActionAdapter

universe u

open OrdinaryIrreducibleCharacter

variable {p : ℕ} {k K G E Block : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Finite G] [Group E]

abbrev TensorCharacters (G0 : Subgroup G) :=
  linearCharactersTrivialOn (k := k) G0

namespace FieldInvariantSubgroup

/-- Exact preservation of a subgroup by every member of the supplied field
automorphism group. -/
def IsInvariant (G0 : Subgroup G) (field : E →* MulAut G) : Prop :=
  ∀ e : E, G0.map (field e).toMonoidHom = G0

/-- Setwise invariance implies the elementwise stability needed to pull back
quotient characters. -/
theorem isFieldStable
    (G0 : Subgroup G) (field : E →* MulAut G)
    (hinvariant : IsInvariant G0 field) :
    LinearCharactersTrivialOn.IsFieldStable G0 field := by
  intro e g hg
  rw [← hinvariant e]
  exact ⟨g, hg, rfl⟩

end FieldInvariantSubgroup

section QuotientAction

variable (G0 : Subgroup G) [G0.Normal]
variable (field : E →* MulAut G)
variable (hinvariant : FieldInvariantSubgroup.IsInvariant G0 field)

/-- The automorphism induced on `G / G0` by a field automorphism preserving
`G0`. -/
def quotientFieldMulEquiv (e : E) : MulAut (G ⧸ G0) where
  toFun := QuotientGroup.map G0 G0 (field e).toMonoidHom (by
    intro g hg
    exact FieldInvariantSubgroup.isFieldStable G0 field hinvariant e g hg)
  invFun := QuotientGroup.map G0 G0 (field e⁻¹).toMonoidHom (by
    intro g hg
    exact FieldInvariantSubgroup.isFieldStable G0 field hinvariant e⁻¹ g hg)
  left_inv q := by
    refine Quotient.inductionOn q ?_
    intro g
    change QuotientGroup.mk' G0 (field e⁻¹ (field e g)) =
      QuotientGroup.mk' G0 g
    simp
  right_inv q := by
    refine Quotient.inductionOn q ?_
    intro g
    change QuotientGroup.mk' G0 (field e (field e⁻¹ g)) =
      QuotientGroup.mk' G0 g
    simp
  map_mul' q r := by
    exact map_mul _ q r

@[simp]
theorem quotientFieldMulEquiv_mk (e : E) (g : G) :
    quotientFieldMulEquiv G0 field hinvariant e (QuotientGroup.mk' G0 g) =
      QuotientGroup.mk' G0 (field e g) :=
  rfl

/-- The induced field action on the quotient group. -/
def quotientField : E →* MulAut (G ⧸ G0) where
  toFun := quotientFieldMulEquiv G0 field hinvariant
  map_one' := by
    apply DFunLike.ext
    intro q
    refine Quotient.inductionOn q ?_
    intro g
    change QuotientGroup.mk' G0 (field (1 : E) g) =
      QuotientGroup.mk' G0 g
    simp
  map_mul' e f := by
    apply DFunLike.ext
    intro q
    refine Quotient.inductionOn q ?_
    intro g
    change QuotientGroup.mk' G0 (field (e * f) g) =
      QuotientGroup.mk' G0 (field e (field f g))
    simp

@[simp]
theorem quotientField_mk (e : E) (g : G) :
    quotientField G0 field hinvariant e (QuotientGroup.mk' G0 g) =
      QuotientGroup.mk' G0 (field e g) :=
  rfl

/-- The canonical identification between characters trivial on `G0` and
characters of `G/G0` intertwines the two field actions. -/
theorem quotientMulEquiv_field_equivariant
    (e : E) (lambda : TensorCharacters (k := k) G0) :
    LinearCharactersTrivialOn.quotientMulEquiv (k := k) G0
        (LinearCharactersTrivialOn.fieldAction (k := k)
          field (FieldInvariantSubgroup.isFieldStable G0 field hinvariant)
          e lambda) =
      OrdinaryIrreducibleCharacter.linearCharacterFieldAction
        (k := k) (quotientField G0 field hinvariant) e
        (LinearCharactersTrivialOn.quotientMulEquiv (k := k) G0 lambda) := by
  ext g
  rfl

/-- The whole tensor and field semidirect product is canonically the
corresponding semidirect product formed from quotient characters. -/
def quotientTensorFieldMulEquiv :
    TensorCharacters (k := k) G0 ⋊[
        LinearCharactersTrivialOn.fieldAction (k := k)
          field (FieldInvariantSubgroup.isFieldStable G0 field hinvariant)] E ≃*
      (G ⧸ G0 →* kˣ) ⋊[
        OrdinaryIrreducibleCharacter.linearCharacterFieldAction
          (k := k) (quotientField G0 field hinvariant)] E :=
  SemidirectProduct.congr
    (LinearCharactersTrivialOn.quotientMulEquiv (k := k) G0)
    (MulEquiv.refl E)
    (fun e ↦ by
      ext lambda g
      rfl)

@[simp]
theorem quotientTensorFieldMulEquiv_left
    (a : TensorCharacters (k := k) G0 ⋊[
      LinearCharactersTrivialOn.fieldAction (k := k)
        field (FieldInvariantSubgroup.isFieldStable G0 field hinvariant)] E) :
    (quotientTensorFieldMulEquiv G0 field hinvariant a).left =
      LinearCharactersTrivialOn.quotientMulEquiv (k := k) G0 a.left :=
  rfl

@[simp]
theorem quotientTensorFieldMulEquiv_right
    (a : TensorCharacters (k := k) G0 ⋊[
      LinearCharactersTrivialOn.fieldAction (k := k)
        field (FieldInvariantSubgroup.isFieldStable G0 field hinvariant)] E) :
    (quotientTensorFieldMulEquiv G0 field hinvariant a).right = a.right :=
  rfl

end QuotientAction

section OrdinaryLift

variable (G0 : Subgroup G) [G0.Normal]
variable (field : E →* MulAut G)
variable (hinvariant : FieldInvariantSubgroup.IsInvariant G0 field)

/-- Exact source-shaped input identifying the ordinary linear characters
used for tensoring with the modular quotient characters.  In the manuscript,
the ordinary side is the `ell'` part of `Irr(G/G0)`, while the modular side is
`IBr(G/G0)`.  The field-equivariance clause is part of the cited
identification; no decomposition-map naturality is included here. -/
structure OrdinaryReductionEquiv where
  ordinaryTensorCharacters : Subgroup (G →* Kˣ)
  ordinaryToBrauer :
    ordinaryTensorCharacters ≃* TensorCharacters (k := k) G0
  field_stable : ∀ (e : E) (lambda : ordinaryTensorCharacters),
    lambda.1.comp (field e⁻¹).toMonoidHom ∈ ordinaryTensorCharacters
  field_equivariant : ∀ (e : E) (lambda : ordinaryTensorCharacters),
    ordinaryToBrauer ⟨
        lambda.1.comp (field e⁻¹).toMonoidHom,
        field_stable e lambda
      ⟩ =
      LinearCharactersTrivialOn.fieldAction (k := k)
        field (FieldInvariantSubgroup.isFieldStable G0 field hinvariant)
        e (ordinaryToBrauer lambda)

namespace OrdinaryReductionEquiv

variable (D : OrdinaryReductionEquiv (k := k) (K := K) G0 field hinvariant)

/-- Lift a modular quotient character to the ordinary tensor character
selected by the cited reduction isomorphism. -/
def lift : TensorCharacters (k := k) G0 →* (G →* Kˣ) :=
  D.ordinaryTensorCharacters.subtype.comp D.ordinaryToBrauer.symm.toMonoidHom

@[simp]
theorem lift_apply (lambda : TensorCharacters (k := k) G0) (g : G) :
    lift (G0 := G0) (field := field) (hinvariant := hinvariant) D lambda g =
      (D.ordinaryToBrauer.symm lambda).1 g :=
  rfl

/-- The lifted ordinary tensor character has the same field transport as
the modular quotient character. -/
theorem lift_field_equivariant
    (e : E) (lambda : TensorCharacters (k := k) G0) :
    lift (G0 := G0) (field := field) (hinvariant := hinvariant) D
        (LinearCharactersTrivialOn.fieldAction (k := k)
          field (FieldInvariantSubgroup.isFieldStable G0 field hinvariant)
          e lambda) =
      (lift (G0 := G0) (field := field) (hinvariant := hinvariant) D lambda).comp
        (field e⁻¹).toMonoidHom := by
  apply MonoidHom.ext
  intro g
  have h := D.field_equivariant e (D.ordinaryToBrauer.symm lambda)
  have hsub :
      (⟨(D.ordinaryToBrauer.symm lambda).1.comp
          (field e⁻¹).toMonoidHom,
        D.field_stable e (D.ordinaryToBrauer.symm lambda)⟩ :
          D.ordinaryTensorCharacters) =
        D.ordinaryToBrauer.symm
          (LinearCharactersTrivialOn.fieldAction (k := k)
            field (FieldInvariantSubgroup.isFieldStable G0 field hinvariant)
            e lambda) := by
    apply D.ordinaryToBrauer.injective
    simpa using h
  exact congrArg (fun mu : D.ordinaryTensorCharacters ↦ (mu.1 g : Kˣ)) hsub.symm

/-- Tensoring ordinary irreducible characters by the lifted quotient
characters, with the inverse convention encoding the manuscript's right
action. -/
@[instance_reducible]
def inverseTensorAction :
    MulAction (TensorCharacters (k := k) G0) (Irr K G) := by
  let _ : MulAction (G →* Kˣ) (Irr K G) :=
    OrdinaryIrreducibleCharacter.inverseTensorAction
  exact MulAction.compHom (Irr K G)
    (lift (G0 := G0) (field := field) (hinvariant := hinvariant) D)

/-- Compatibility of the actual ordinary tensor action with field
automorphisms. -/
theorem tensorField_semidirectCompatible :
    @Formalisation.SemidirectActionCompatible
      (TensorCharacters (k := k) G0) E (Irr K G) _ _
      (inverseTensorAction (G0 := G0) (field := field)
        (hinvariant := hinvariant) D)
      (OrdinaryIrreducibleCharacter.inverseFieldAction (k := K) field)
      (LinearCharactersTrivialOn.fieldAction (k := k)
        field (FieldInvariantSubgroup.isFieldStable G0 field hinvariant)) := by
  intro e lambda chi
  change
    OrdinaryIrreducibleCharacter.twist K G
        (OrdinaryIrreducibleCharacter.linearTwist chi
          ((lift (G0 := G0) (field := field) (hinvariant := hinvariant) D)
            lambda)⁻¹)
        (field e⁻¹) =
      OrdinaryIrreducibleCharacter.linearTwist
        (OrdinaryIrreducibleCharacter.twist K G chi (field e⁻¹))
        ((lift (G0 := G0) (field := field) (hinvariant := hinvariant) D)
          ((LinearCharactersTrivialOn.fieldAction (k := k)
            field (FieldInvariantSubgroup.isFieldStable G0 field hinvariant))
            e lambda))⁻¹
  rw [OrdinaryIrreducibleCharacter.twist_linearTwist]
  congr 1
  rw [map_inv, lift_field_equivariant (G0 := G0) (field := field)
    (hinvariant := hinvariant) D]
  ext g
  simp

/-- The combined ordinary action of the quotient-character tensor group and
the field group. -/
@[instance_reducible]
def tensorFieldSemidirectAction :
    MulAction
      (TensorCharacters (k := k) G0 ⋊[
        LinearCharactersTrivialOn.fieldAction (k := k)
          field (FieldInvariantSubgroup.isFieldStable G0 field hinvariant)] E)
      (Irr K G) := by
  exact @Formalisation.semidirectMulAction
    (TensorCharacters (k := k) G0) E (Irr K G) _ _
    (inverseTensorAction (G0 := G0) (field := field)
      (hinvariant := hinvariant) D)
    (OrdinaryIrreducibleCharacter.inverseFieldAction (k := K) field)
    (LinearCharactersTrivialOn.fieldAction (k := k)
      field (FieldInvariantSubgroup.isFieldStable G0 field hinvariant))
    (tensorField_semidirectCompatible (G0 := G0) (field := field)
      (hinvariant := hinvariant) D)

/-- Elementwise formula for the combined ordinary action. -/
theorem tensorFieldSemidirectAction_apply
    (a : TensorCharacters (k := k) G0 ⋊[
      LinearCharactersTrivialOn.fieldAction (k := k)
        field (FieldInvariantSubgroup.isFieldStable G0 field hinvariant)] E)
    (chi : Irr K G) :
    let _ : MulAction
        (TensorCharacters (k := k) G0 ⋊[
          LinearCharactersTrivialOn.fieldAction (k := k)
            field (FieldInvariantSubgroup.isFieldStable G0 field hinvariant)] E)
        (Irr K G) := tensorFieldSemidirectAction (G0 := G0)
          (field := field) (hinvariant := hinvariant) D
    a • chi = OrdinaryIrreducibleCharacter.linearTwist
      (OrdinaryIrreducibleCharacter.twist K G chi (field a.right⁻¹))
      (lift (G0 := G0) (field := field) (hinvariant := hinvariant) D a.left)⁻¹ := by
  rfl

end OrdinaryReductionEquiv

end OrdinaryLift

section StableCarriers

variable (G0 : Subgroup G) [G0.Normal]
variable (field : E →* MulAut G)
variable (hinvariant : FieldInvariantSubgroup.IsInvariant G0 field)

abbrev ActingGroup :=
  TensorCharacters (k := k) G0 ⋊[
    LinearCharactersTrivialOn.fieldAction (k := k)
      field (FieldInvariantSubgroup.isFieldStable G0 field hinvariant)] E

/-- The ordinary labels in the selected Lusztig-series union and block. -/
def OrdinarySeriesBlockFibre
    (series : Irr K G → Prop) (ordinaryBlock : Irr K G → Block)
    (block : Block) :=
  {chi : Irr K G // series chi ∧ ordinaryBlock chi = block}

/-- The irreducible Brauer characters in the selected block. -/
def BrauerBlockFibre
    (iota : PrimeRegularRootEmbedding p k K G)
    (brauerBlock : IBr iota → Block) (block : Block) :=
  {phi : IBr iota // brauerBlock phi = block}

/-- Exact source-shaped stability of the ordinary Lusztig-series union under
the already constructed tensor and field action. -/
def OrdinarySeriesStable
    (D : OrdinaryReductionEquiv (k := k) (K := K) G0 field hinvariant)
    (series : Irr K G → Prop) : Prop :=
  let _ : MulAction (ActingGroup (k := k) G0 field hinvariant) (Irr K G) :=
    OrdinaryReductionEquiv.tensorFieldSemidirectAction (G0 := G0)
      (field := field) (hinvariant := hinvariant) D
  ∀ (a : ActingGroup (k := k) G0 field hinvariant) (chi : Irr K G),
    series chi → series (a • chi)

/-- Stability of the ordinary Lusztig-series union under tensoring by the
ordinary lifts of quotient Brauer characters.  This is the tensor part of
the source input, stated separately from field stability. -/
def OrdinarySeriesTensorStable
    (D : OrdinaryReductionEquiv (k := k) (K := K) G0 field hinvariant)
    (series : Irr K G → Prop) : Prop :=
  ∀ (lambda : TensorCharacters (k := k) G0) (chi : Irr K G),
    series chi →
      series (OrdinaryIrreducibleCharacter.linearTwist chi
        (OrdinaryReductionEquiv.lift (G0 := G0) (field := field)
          (hinvariant := hinvariant) D lambda)⁻¹)

/-- Stability of the ordinary Lusztig-series union under the inverse field
action which encodes the manuscript's right convention. -/
def OrdinarySeriesFieldStable
    (series : Irr K G → Prop) : Prop :=
  ∀ (e : E) (chi : Irr K G), series chi →
    series (OrdinaryIrreducibleCharacter.twist K G chi (field e⁻¹))

/-- The separately cited tensor and field stability assertions imply
stability under the literal semidirect product action. -/
theorem ordinarySeriesStable_of_tensor_and_field
    (D : OrdinaryReductionEquiv (k := k) (K := K) G0 field hinvariant)
    (series : Irr K G → Prop)
    (htensor : OrdinarySeriesTensorStable G0 field hinvariant D series)
    (hfield : OrdinarySeriesFieldStable (K := K) field series) :
    OrdinarySeriesStable G0 field hinvariant D series := by
  letI : MulAction (ActingGroup (k := k) G0 field hinvariant) (Irr K G) :=
    OrdinaryReductionEquiv.tensorFieldSemidirectAction (G0 := G0)
      (field := field) (hinvariant := hinvariant) D
  intro a chi hchi
  rw [OrdinaryReductionEquiv.tensorFieldSemidirectAction_apply
    (G0 := G0) (field := field) (hinvariant := hinvariant) D]
  exact htensor a.left
    (OrdinaryIrreducibleCharacter.twist K G chi (field a.right⁻¹))
    (hfield a.right chi hchi)

/-- Exact compatibility of the ordinary block map with the tensor and field
action. -/
def OrdinaryBlockEquivariant
    (D : OrdinaryReductionEquiv (k := k) (K := K) G0 field hinvariant)
    [MulAction (ActingGroup (k := k) G0 field hinvariant) Block]
    (ordinaryBlock : Irr K G → Block) : Prop :=
  let _ : MulAction (ActingGroup (k := k) G0 field hinvariant) (Irr K G) :=
    OrdinaryReductionEquiv.tensorFieldSemidirectAction (G0 := G0)
      (field := field) (hinvariant := hinvariant) D
  ∀ (a : ActingGroup (k := k) G0 field hinvariant) (chi : Irr K G),
    ordinaryBlock (a • chi) = a • ordinaryBlock chi

/-- Exact compatibility of the Brauer block map with the actual modular
tensor and field action. -/
def BrauerBlockEquivariant
    (iota : PrimeRegularRootEmbedding p k K G)
    (productFormula : BrauerLinearTensorProductFormula iota)
    [MulAction (ActingGroup (k := k) G0 field hinvariant) Block]
    (brauerBlock : IBr iota → Block) : Prop :=
  let _ : MulAction (ActingGroup (k := k) G0 field hinvariant) (IBr iota) :=
    IrreducibleBrauerCharacter.trivialTensorFieldSemidirectAction
      iota productFormula field
        (FieldInvariantSubgroup.isFieldStable G0 field hinvariant)
  ∀ (a : ActingGroup (k := k) G0 field hinvariant) (phi : IBr iota),
    brauerBlock (a • phi) = a • brauerBlock phi

/-- The actual ordinary tensor and field action restricts to the
Lusztig-series part of a block under the literal stabiliser of that block. -/
@[instance_reducible]
def ordinarySeriesBlockStabilizerAction
    (D : OrdinaryReductionEquiv (k := k) (K := K) G0 field hinvariant)
    [MulAction (ActingGroup (k := k) G0 field hinvariant) Block]
    (series : Irr K G → Prop) (ordinaryBlock : Irr K G → Block)
    (block : Block)
    (hseries : OrdinarySeriesStable G0 field hinvariant D series)
    (hblock : OrdinaryBlockEquivariant G0 field hinvariant D ordinaryBlock) :
    MulAction
      (MulAction.stabilizer (ActingGroup (k := k) G0 field hinvariant) block)
      (OrdinarySeriesBlockFibre series ordinaryBlock block) := by
  letI : MulAction (ActingGroup (k := k) G0 field hinvariant) (Irr K G) :=
    OrdinaryReductionEquiv.tensorFieldSemidirectAction (G0 := G0)
      (field := field) (hinvariant := hinvariant) D
  exact {
    smul := fun a chi ↦
      ⟨(a.1 • chi.1),
        hseries a.1 chi.1 chi.2.1,
        by
          rw [hblock a.1 chi.1, chi.2.2]
          exact a.2⟩
    one_smul := by
      intro chi
      apply Subtype.ext
      exact one_smul _ chi.1
    mul_smul := by
      intro a b chi
      apply Subtype.ext
      exact mul_smul a.1 b.1 chi.1 }

/-- The actual modular tensor and field action restricts to the Brauer
characters in a block under the same literal block stabiliser. -/
@[instance_reducible]
def brauerBlockStabilizerAction
    (iota : PrimeRegularRootEmbedding p k K G)
    (productFormula : BrauerLinearTensorProductFormula iota)
    [MulAction (ActingGroup (k := k) G0 field hinvariant) Block]
    (brauerBlock : IBr iota → Block) (block : Block)
    (hblock : BrauerBlockEquivariant G0 field hinvariant iota
      productFormula brauerBlock) :
    MulAction
      (MulAction.stabilizer (ActingGroup (k := k) G0 field hinvariant) block)
      (BrauerBlockFibre iota brauerBlock block) := by
  letI : MulAction (ActingGroup (k := k) G0 field hinvariant) (IBr iota) :=
    IrreducibleBrauerCharacter.trivialTensorFieldSemidirectAction
      iota productFormula field
        (FieldInvariantSubgroup.isFieldStable G0 field hinvariant)
  exact {
    smul := fun a phi ↦
      ⟨(a.1 • phi.1), by
        rw [hblock a.1 phi.1, phi.2]
        exact a.2⟩
    one_smul := by
      intro phi
      apply Subtype.ext
      exact one_smul _ phi.1
    mul_smul := by
      intro a b phi
      apply Subtype.ext
      exact mul_smul a.1 b.1 phi.1 }

end StableCarriers

end ModularRep.PaperProofs.TypeCConformalActionAdapter


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
