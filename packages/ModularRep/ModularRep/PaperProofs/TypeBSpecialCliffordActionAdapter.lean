import ModularRep.KZeroLinearCharacterSemidirect
import ModularRep.OrdinaryIrrSimpleModuleClass
import ModularRep.PaperProofs.TypeCConformalActionAdapter
import ModularRep.DecompositionBasicSetBridge
import ModularRep.PaperProofs.OddConformalProposition311Relative

/-!
# Tensor and field actions for the special Clifford group

This file instantiates the actual tensor and field actions occurring in
Lemma 4.2 for an ambient finite group `M` with a normal subgroup `G0`.  In
the manuscript these are the finite special Clifford group and its Spin
derived subgroup.  Their structural identification is deliberately not
reproved here.

The tensor factor is the literal group of modular linear characters of `M`
trivial on `G0`; the field factor acts by pullback.  Lean constructs the
combined actions on function-valued `Irr`, function-valued `IBr`, and both
exact Grothendieck groups.  It proves naturality of the exact decomposition
map from ordinary/modular linear character compatibility, the tensor product
formula for Brauer characters, and automorphism naturality.  It also
restricts the two character actions to a selected block fibre.

No equivariant basic-set bijection, Conlon conclusion, BAW condition, or
iBAW condition is an input or conclusion.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBSpecialCliffordActionAdapter

open ModularRep.DecompositionBasicSetBridge
open ModularRep.ExactGrothendieckGroup
open ModularRep.FDRepSimpleClassKZero
open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs.TypeCConformalActionAdapter
open ModularRep.PaperProofs.OddConformalProposition311Relative

universe u

variable {p : ℕ} {K O k M E Block : Type u}
variable [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
variable [CharZero K] [IsAlgClosed K] [CharP k p] [IsAlgClosed k]
variable [Group M] [Finite M] [Group E]

abbrev TensorCharacters (G0 : Subgroup M) :=
  TypeCConformalActionAdapter.TensorCharacters (k := k) G0

abbrev ActingGroup
    (G0 : Subgroup M) [G0.Normal]
    (field : E →* MulAut M)
    (hinvariant : FieldInvariantSubgroup.IsInvariant G0 field) :=
  TypeCConformalActionAdapter.ActingGroup
    (k := k) G0 field hinvariant

section SemidirectMaps

variable (G0 : Subgroup M) [G0.Normal]
variable (field : E →* MulAut M)
variable (hinvariant : FieldInvariantSubgroup.IsInvariant G0 field)

abbrev OrdinaryReductionEquiv :=
  TypeCConformalActionAdapter.OrdinaryReductionEquiv
    (k := k) (K := K) G0 field hinvariant

/-- The homomorphism from the manuscript's tensor and field group to the
full ordinary linear character semidirect product. -/
def ordinarySemidirectMap
    (D : OrdinaryReductionEquiv (k := k) (K := K)
      G0 field hinvariant) :
    ActingGroup (k := k) G0 field hinvariant →*
      ((M →* Kˣ) ⋊[
        OrdinaryIrreducibleCharacter.linearCharacterFieldAction
          (k := K) field] E) :=
  SemidirectProduct.map
    (OrdinaryReductionEquiv.lift (G0 := G0) (field := field)
      (hinvariant := hinvariant) D)
    (MonoidHom.id E) (by
      intro e
      apply MonoidHom.ext
      intro lambda
      change
        OrdinaryReductionEquiv.lift (G0 := G0) (field := field)
            (hinvariant := hinvariant) D
            ((LinearCharactersTrivialOn.fieldAction (k := k)
              field (FieldInvariantSubgroup.isFieldStable G0 field hinvariant))
              e lambda) =
          (OrdinaryReductionEquiv.lift (G0 := G0) (field := field)
            (hinvariant := hinvariant) D lambda).comp
              (field e⁻¹).toMonoidHom
      exact OrdinaryReductionEquiv.lift_field_equivariant
        (G0 := G0) (field := field) (hinvariant := hinvariant) D e lambda)

@[simp]
theorem ordinarySemidirectMap_left
    (D : OrdinaryReductionEquiv (k := k) (K := K)
      G0 field hinvariant)
    (a : ActingGroup (k := k) G0 field hinvariant) :
    (ordinarySemidirectMap G0 field hinvariant D a).left =
      OrdinaryReductionEquiv.lift (G0 := G0) (field := field)
        (hinvariant := hinvariant) D a.left :=
  rfl

@[simp]
theorem ordinarySemidirectMap_right
    (D : OrdinaryReductionEquiv (k := k) (K := K)
      G0 field hinvariant)
    (a : ActingGroup (k := k) G0 field hinvariant) :
    (ordinarySemidirectMap G0 field hinvariant D a).right = a.right :=
  rfl

/-- The corresponding homomorphism to the full modular
linear character semidirect product. -/
def modularSemidirectMap :
    ActingGroup (k := k) G0 field hinvariant →*
      ((M →* kˣ) ⋊[
        OrdinaryIrreducibleCharacter.linearCharacterFieldAction
          (k := k) field] E) :=
  SemidirectProduct.map
    (linearCharactersTrivialOn (k := k) G0).subtype
    (MonoidHom.id E) (by
      intro e
      ext lambda g
      rfl)

@[simp]
theorem modularSemidirectMap_left
    (a : ActingGroup (k := k) G0 field hinvariant) :
    (modularSemidirectMap (k := k) G0 field hinvariant a).left = a.left.1 :=
  rfl

@[simp]
theorem modularSemidirectMap_right
    (a : ActingGroup (k := k) G0 field hinvariant) :
    (modularSemidirectMap (k := k) G0 field hinvariant a).right = a.right :=
  rfl

end SemidirectMaps

section ActualActions

variable (G0 : Subgroup M) [G0.Normal]
variable (field : E →* MulAut M)
variable (hinvariant : FieldInvariantSubgroup.IsInvariant G0 field)
variable (D : OrdinaryReductionEquiv (k := k) (K := K)
  G0 field hinvariant)

/-- The actual action on ordinary irreducible characters. -/
@[instance_reducible]
def ordinaryCharacterAction :
    MulAction (ActingGroup (k := k) G0 field hinvariant) (Irr K M) :=
  OrdinaryReductionEquiv.tensorFieldSemidirectAction
    (G0 := G0) (field := field) (hinvariant := hinvariant) D

/-- The actual action on irreducible Brauer characters. -/
@[instance_reducible]
def brauerCharacterAction
    (iota : PrimeRegularRootEmbedding p k K M)
    (productFormula : BrauerLinearTensorProductFormula iota) :
    MulAction (ActingGroup (k := k) G0 field hinvariant) (IBr iota) :=
  IrreducibleBrauerCharacter.trivialTensorFieldSemidirectAction
    iota productFormula field
      (FieldInvariantSubgroup.isFieldStable G0 field hinvariant)

/-- The exact `K₀` action on ordinary representations. -/
def ordinaryKZeroAction :
    Representation ℤ (ActingGroup (k := k) G0 field hinvariant)
      (FDRepKZero K M) :=
  (tensorFieldKZeroRepresentation (k := K) field).pullback
    (ordinarySemidirectMap G0 field hinvariant D)

/-- The exact `K₀` action on modular representations. -/
def modularKZeroAction :
    Representation ℤ (ActingGroup (k := k) G0 field hinvariant)
      (FDRepKZero k M) :=
  (tensorFieldKZeroRepresentation (k := k) field).pullback
    (modularSemidirectMap (k := k) G0 field hinvariant)

@[simp]
theorem ordinaryKZeroAction_apply
    (a : ActingGroup (k := k) G0 field hinvariant)
    (x : FDRepKZero K M) :
    ordinaryKZeroAction G0 field hinvariant D a x =
      linearCharacterTwistKZero
        (OrdinaryReductionEquiv.lift (G0 := G0) (field := field)
          (hinvariant := hinvariant) D a.left)⁻¹
        (twistKZero (k := K) (field a.right⁻¹) x) :=
  rfl

@[simp]
theorem modularKZeroAction_apply
    (a : ActingGroup (k := k) G0 field hinvariant)
    (x : FDRepKZero k M) :
    modularKZeroAction (k := k) G0 field hinvariant a x =
      linearCharacterTwistKZero a.left.1⁻¹
        (twistKZero (k := k) (field a.right⁻¹) x) :=
  rfl

/-- The ordinary lift selected by `D` and the modular quotient character
have the same values on the `p`-regular elements.  This is the exact
source-shaped compatibility needed by the decomposition map. -/
def OrdinaryLiftReductionCompatible
    (iota : PrimeRegularRootEmbedding p k K M) : Prop :=
  ∀ lambda : TensorCharacters (k := k) G0,
    LinearCharacterReductionCompatible iota
      (OrdinaryReductionEquiv.lift (G0 := G0) (field := field)
        (hinvariant := hinvariant) D lambda) lambda.1

/-- The exact decomposition homomorphism commutes with the constructed
tensor and field action.  Decomposition naturality is a conclusion here,
not an input. -/
theorem decompositionNatural
    (Msys : ModularSystem p K O k)
    (iota : PrimeRegularRootEmbedding p k K M)
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (productFormula : BrauerLinearTensorProductFormula iota)
    (hlift : OrdinaryLiftReductionCompatible G0 field hinvariant D iota) :
    DecompositionNatural
      (A := ActingGroup (k := k) G0 field hinvariant)
      (decompositionMapOfStableReduction Msys iota hcompat)
      (ordinaryKZeroAction G0 field hinvariant D)
      (modularKZeroAction (k := k) G0 field hinvariant) := by
  intro a x
  rw [ordinaryKZeroAction_apply, modularKZeroAction_apply]
  have hliftInv := hlift a.left⁻¹
  have hliftInv' : LinearCharacterReductionCompatible iota
      (OrdinaryReductionEquiv.lift (G0 := G0) (field := field)
        (hinvariant := hinvariant) D a.left)⁻¹ a.left.1⁻¹ := by
    simpa using hliftInv
  rw [decompositionMapOfStableReduction_linearCharacterTwist
    Msys iota hcompat productFormula _ _ hliftInv']
  rw [decompositionMapOfStableReduction_twist
    Msys iota hcompat (field a.right⁻¹) x]

/-- The actual tensor and automorphism action on an ordinary irreducible
character is realised by the corresponding exact `K₀` operation on its
chosen simple-module label. -/
theorem ordinaryLabel_linearTwist_twist
    (chi : Irr K M) (alpha : MulAut M) (lambda : M →* Kˣ) :
    simpleClassToFDRepKZeroGenerator
        (simpleModuleClassLabel
          (OrdinaryIrreducibleCharacter.linearTwist
            (OrdinaryIrreducibleCharacter.twist K M chi alpha) lambda)) =
      linearCharacterTwistKZero lambda
        (twistKZero (k := K) alpha
          (simpleClassToFDRepKZeroGenerator
            (simpleModuleClassLabel chi))) := by
  let V0 := simpleClassFDRep (simpleModuleClassLabel chi)
  let Vfield := (FDRep.twistEquivalence K M alpha).functor.obj V0
  let V1 := FDRep.of
    (Representation.linearCharacterTwist (FDRep.ρ Vfield) lambda)
  have hV0 : Representation.IsIrreducible (FDRep.ρ V0) :=
    simpleClassFDRep_irreducible (simpleModuleClassLabel chi)
  have hV1 : Representation.IsIrreducible (FDRep.ρ V1) := by
    change Representation.IsIrreducible
      (Representation.linearCharacterTwist
        (Representation.twist (FDRep.ρ V0) alpha) lambda)
    exact (hV0.twist alpha).linearCharacterTwist lambda
  let X1 := simpleClassOfIrreducibleFDRep V1 hV1
  have hclass :
      simpleModuleClassLabel
          (OrdinaryIrreducibleCharacter.linearTwist
            (OrdinaryIrreducibleCharacter.twist K M chi alpha) lambda) =
        X1 := by
    apply simpleModuleClass_character_injective
    calc
      (simpleClassFDRep
          (simpleModuleClassLabel
            (OrdinaryIrreducibleCharacter.linearTwist
              (OrdinaryIrreducibleCharacter.twist K M chi alpha)
              lambda))).character =
          (OrdinaryIrreducibleCharacter.linearTwist
            (OrdinaryIrreducibleCharacter.twist K M chi alpha)
            lambda).1 :=
        simpleModuleClassLabel_character _
      _ = V1.character := by
        funext g
        change (lambda g : K) * chi (alpha g) =
          (Representation.linearCharacterTwist
            (Representation.twist (FDRep.ρ V0) alpha) lambda).character g
        rw [Representation.character_linearCharacterTwist]
        change (lambda g : K) * chi (alpha g) =
          (lambda g : K) * V0.character (alpha g)
        rw [show V0.character = chi.1 by
          exact simpleModuleClassLabel_character chi]
      _ = (simpleClassFDRep X1).character :=
        (FDRep.char_iso
          (simpleClassOfIrreducibleFDRepIso V1 hV1)).symm
  change ExactGrothendieckGroup.classOf (FDRep K M)
      (simpleClassFDRep
        (simpleModuleClassLabel
          (OrdinaryIrreducibleCharacter.linearTwist
            (OrdinaryIrreducibleCharacter.twist K M chi alpha) lambda))) =
    linearCharacterTwistKZero lambda
      (twistKZero (k := K) alpha
        (ExactGrothendieckGroup.classOf (FDRep K M)
          (simpleClassFDRep (simpleModuleClassLabel chi))))
  rw [twistKZero_classOf, linearCharacterTwistKZero_classOf]
  calc
    simpleClassToFDRepKZeroGenerator
        (simpleModuleClassLabel
          (OrdinaryIrreducibleCharacter.linearTwist
            (OrdinaryIrreducibleCharacter.twist K M chi alpha) lambda)) =
        simpleClassToFDRepKZeroGenerator X1 :=
      congrArg (fun X : SimpleModuleClass K[M] ↦
        simpleClassToFDRepKZeroGenerator X) hclass
    _ = ExactGrothendieckGroup.classOf (FDRep K M) V1 :=
      ExactGrothendieckGroup.classOf_iso (FDRep K M)
        (simpleClassOfIrreducibleFDRepIso V1 hV1)
    _ = ExactGrothendieckGroup.classOf (FDRep K M)
        (FDRep.of
          (Representation.linearCharacterTwist
            (FDRep.ρ
              ((FDRep.twistEquivalence K M alpha).functor.obj
                (simpleClassFDRep (simpleModuleClassLabel chi))))
            lambda)) := rfl

/-- On the actual ordinary `Irr` carrier, the combined action and the
constructed exact `K₀` action agree on every simple generator. -/
theorem ordinaryLabel_action
    (a : ActingGroup (k := k) G0 field hinvariant) (chi : Irr K M) :
    let _ : MulAction (ActingGroup (k := k) G0 field hinvariant) (Irr K M) :=
      ordinaryCharacterAction G0 field hinvariant D
    simpleClassToFDRepKZeroGenerator
        (simpleModuleClassLabel (a • chi)) =
      ordinaryKZeroAction G0 field hinvariant D a
        (simpleClassToFDRepKZeroGenerator
          (simpleModuleClassLabel chi)) := by
  dsimp only
  rw [OrdinaryReductionEquiv.tensorFieldSemidirectAction_apply,
    ordinaryKZeroAction_apply]
  exact ordinaryLabel_linearTwist_twist
    (chi := chi) (alpha := field a.right⁻¹)
      (lambda := (OrdinaryReductionEquiv.lift
        (G0 := G0) (field := field) (hinvariant := hinvariant) D a.left)⁻¹)

/-- The corresponding statement for the actual function-valued Brauer
set of characters. -/
theorem brauerLabel_linearTwist_twist
    (iota : PrimeRegularRootEmbedding p k K M)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (productFormula : BrauerLinearTensorProductFormula iota)
    (phi : IBr iota) (alpha : MulAut M) (lambda : M →* kˣ) :
    simpleClassToFDRepKZeroGenerator
        ((simpleModuleClassEquivIBr iota hinj).symm
          (IrreducibleBrauerCharacter.linearTwist iota productFormula
            (IrreducibleBrauerCharacter.twist iota phi alpha) lambda)) =
      linearCharacterTwistKZero lambda
        (twistKZero (k := k) alpha
          (simpleClassToFDRepKZeroGenerator
            ((simpleModuleClassEquivIBr iota hinj).symm phi))) := by
  let X0 := (simpleModuleClassEquivIBr iota hinj).symm phi
  let V0 := simpleClassFDRep X0
  let Vfield := (FDRep.twistEquivalence k M alpha).functor.obj V0
  let V1 := FDRep.of
    (Representation.linearCharacterTwist (FDRep.ρ Vfield) lambda)
  have hV0 : Representation.IsIrreducible (FDRep.ρ V0) :=
    simpleClassFDRep_irreducible X0
  have hV1 : Representation.IsIrreducible (FDRep.ρ V1) := by
    change Representation.IsIrreducible
      (Representation.linearCharacterTwist
        (Representation.twist (FDRep.ρ V0) alpha) lambda)
    exact (hV0.twist alpha).linearCharacterTwist lambda
  let X1 := simpleClassOfIrreducibleFDRep V1 hV1
  let target := IrreducibleBrauerCharacter.linearTwist iota productFormula
    (IrreducibleBrauerCharacter.twist iota phi alpha) lambda
  have hX0 : simpleClassToIBr iota X0 = phi := by
    exact (simpleModuleClassEquivIBr iota hinj).apply_symm_apply phi
  have hX0val :
      Representation.brauerCharacterOfRootEmbedding (FDRep.ρ V0) iota =
        phi.1 :=
    congrArg (fun psi : IBr iota ↦ psi.1) hX0
  have hV1val :
      Representation.brauerCharacterOfRootEmbedding (FDRep.ρ V1) iota =
        target.1 := by
    change Representation.brauerCharacterOfRootEmbedding
        (Representation.linearCharacterTwist
          (FDRep.ρ Vfield) lambda) iota = target.1
    rw [productFormula Vfield lambda]
    rw [show Representation.brauerCharacterOfRootEmbedding
        (FDRep.ρ Vfield) iota =
          (Representation.brauerCharacterOfRootEmbedding
            (FDRep.ρ V0) iota).twist alpha by
      exact FDRep.twistEquivalence_obj_brauerCharacter
        (k := k) (G := M) iota alpha V0]
    rw [hX0val]
    rfl
  have hX1 : simpleClassToIBr iota X1 = target := by
    apply Subtype.ext
    calc
      Representation.brauerCharacterOfRootEmbedding
          (FDRep.ρ (simpleClassFDRep X1)) iota =
          Representation.brauerCharacterOfRootEmbedding
            (FDRep.ρ V1) iota :=
        Representation.brauerCharacterOfRootEmbedding_iso iota
          (simpleClassOfIrreducibleFDRepIso V1 hV1)
      _ = target.1 := hV1val
  have hclass : (simpleModuleClassEquivIBr iota hinj).symm target = X1 := by
    apply hinj
    calc
      simpleClassToIBr iota
          ((simpleModuleClassEquivIBr iota hinj).symm target) = target :=
        (simpleModuleClassEquivIBr iota hinj).apply_symm_apply target
      _ = simpleClassToIBr iota X1 := hX1.symm
  change ExactGrothendieckGroup.classOf (FDRep k M)
      (simpleClassFDRep
        ((simpleModuleClassEquivIBr iota hinj).symm target)) =
    linearCharacterTwistKZero lambda
      (twistKZero (k := k) alpha
        (ExactGrothendieckGroup.classOf (FDRep k M)
          (simpleClassFDRep X0)))
  rw [twistKZero_classOf, linearCharacterTwistKZero_classOf]
  calc
    simpleClassToFDRepKZeroGenerator
        ((simpleModuleClassEquivIBr iota hinj).symm target) =
        simpleClassToFDRepKZeroGenerator X1 :=
      congrArg (fun X : SimpleModuleClass k[M] ↦
        simpleClassToFDRepKZeroGenerator X) hclass
    _ = ExactGrothendieckGroup.classOf (FDRep k M) V1 :=
      ExactGrothendieckGroup.classOf_iso (FDRep k M)
        (simpleClassOfIrreducibleFDRepIso V1 hV1)
    _ = ExactGrothendieckGroup.classOf (FDRep k M)
        (FDRep.of
          (Representation.linearCharacterTwist
            (FDRep.ρ
              ((FDRep.twistEquivalence k M alpha).functor.obj
                (simpleClassFDRep X0))) lambda)) := rfl

/-- On the actual `IBr` carrier, the combined action and the constructed
modular exact `K₀` action agree on every simple generator. -/
theorem brauerLabel_action
    (iota : PrimeRegularRootEmbedding p k K M)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (productFormula : BrauerLinearTensorProductFormula iota)
    (a : ActingGroup (k := k) G0 field hinvariant) (phi : IBr iota) :
    let _ : MulAction (ActingGroup (k := k) G0 field hinvariant) (IBr iota) :=
      brauerCharacterAction G0 field hinvariant iota productFormula
    simpleClassToFDRepKZeroGenerator
        ((simpleModuleClassEquivIBr iota hinj).symm (a • phi)) =
      modularKZeroAction (k := k) G0 field hinvariant a
        (simpleClassToFDRepKZeroGenerator
          ((simpleModuleClassEquivIBr iota hinj).symm phi)) := by
  dsimp only
  rw [IrreducibleBrauerCharacter.trivialTensorFieldSemidirectAction_apply,
    modularKZeroAction_apply]
  exact brauerLabel_linearTwist_twist
    (iota := iota) (hinj := hinj) (productFormula := productFormula)
    (phi := phi) (alpha := field a.right⁻¹) (lambda := a.left.1⁻¹)

end ActualActions

section BlockFibres

variable (G0 : Subgroup M) [G0.Normal]
variable (field : E →* MulAut M)
variable (hinvariant : FieldInvariantSubgroup.IsInvariant G0 field)
variable (D : OrdinaryReductionEquiv (k := k) (K := K)
  G0 field hinvariant)
variable [MulAction (ActingGroup (k := k) G0 field hinvariant) Block]

/-- The actual ordinary `ell'`-series carrier. -/
def OrdinarySeriesCarrier (series : Irr K M → Prop) :=
  {chi : Irr K M // series chi}

/-- The actual simple-module label attached to a character in the selected
ordinary series union. -/
def ordinarySeriesLabel (series : Irr K M → Prop) :
    OrdinarySeriesCarrier series → SimpleModuleClass K[M] :=
  fun chi ↦ simpleModuleClassLabel chi.1

/-- Distinct ordinary characters in the selected series union have distinct
simple-module labels. -/
theorem ordinarySeriesLabel_injective (series : Irr K M → Prop) :
    Function.Injective (ordinarySeriesLabel (K := K) series) := by
  intro chi psi h
  apply Subtype.ext
  exact simpleModuleClassLabel_injective h

/-- Package a cited integral basic set on the actual ordinary series carrier
and the actual set of Brauer characters.  The linear equivalence and its
identification with the decomposition map remain explicit source inputs. -/
def ordinarySeriesBasicSet
    (Msys : ModularSystem p K O k)
    (iota : PrimeRegularRootEmbedding p k K M)
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (series : Irr K M → Prop)
    (linearEquiv :
      MonoidAlgebra ℤ (OrdinarySeriesCarrier series) ≃ₗ[ℤ]
        MonoidAlgebra ℤ (IBr iota))
    (hdecomposition : ∀ v : MonoidAlgebra ℤ (OrdinarySeriesCarrier series),
      labelledSimpleClassKZero (simpleModuleClassEquivIBr iota hinj).symm
          (linearEquiv v) =
        decompositionMapOfStableReduction Msys iota hcompat
          (labelledSimpleClassKZero
            (ordinarySeriesLabel (K := K) series) v)) :
    RestrictedIntegralBasicSetOnIBr iota hinj
      (OrdinarySeriesCarrier series)
      (decompositionMapOfStableReduction Msys iota hcompat) where
  ordinaryLabel := ordinarySeriesLabel (K := K) series
  ordinaryLabel_injective := ordinarySeriesLabel_injective (K := K) series
  linearEquiv := linearEquiv
  restricts_decomposition := hdecomposition

/-- The actual ordinary series carrier is stable under the constructed
action once tensor and field stability have been supplied. -/
@[instance_reducible]
def ordinarySeriesCarrierAction
    (series : Irr K M → Prop)
    (hseries : OrdinarySeriesStable G0 field hinvariant D series) :
    MulAction (ActingGroup (k := k) G0 field hinvariant)
      (OrdinarySeriesCarrier series) := by
  let _ : MulAction (ActingGroup (k := k) G0 field hinvariant) (Irr K M) :=
    ordinaryCharacterAction G0 field hinvariant D
  exact {
    smul := fun a chi ↦ ⟨a • chi.1, hseries a chi.1 chi.2⟩
    one_smul := by
      intro chi
      apply Subtype.ext
      exact one_smul _ chi.1
    mul_smul := by
      intro a b chi
      apply Subtype.ext
      exact mul_smul a b chi.1 }

/-- The block map on an ordinary series carrier. -/
def ordinarySeriesBlockMap
    (series : Irr K M → Prop) (ordinaryBlock : Irr K M → Block) :
    OrdinarySeriesCarrier series → Block :=
  fun chi ↦ ordinaryBlock chi.1

/-- Equivariance of the ambient ordinary block map restricts to the actual
series carrier. -/
theorem ordinarySeriesBlockMap_equivariant
    (series : Irr K M → Prop)
    (ordinaryBlock : Irr K M → Block)
    (hseries : OrdinarySeriesStable G0 field hinvariant D series)
    (hblock : OrdinaryBlockEquivariant G0 field hinvariant D ordinaryBlock)
    (a : ActingGroup (k := k) G0 field hinvariant)
    (chi : OrdinarySeriesCarrier series) :
    let _ : MulAction (ActingGroup (k := k) G0 field hinvariant)
        (OrdinarySeriesCarrier series) :=
      ordinarySeriesCarrierAction G0 field hinvariant D series hseries
    ordinarySeriesBlockMap series ordinaryBlock (a • chi) =
      a • ordinarySeriesBlockMap series ordinaryBlock chi := by
  dsimp only
  exact hblock a chi.1

/-- The literal stabiliser of a block acts on the ordinary labels in that
block and in the selected series union. -/
@[instance_reducible]
def ordinaryBlockFibreAction
    (series : Irr K M → Prop)
    (ordinaryBlock : Irr K M → Block) (block : Block)
    (hseries : OrdinarySeriesStable G0 field hinvariant D series)
    (hblock : OrdinaryBlockEquivariant G0 field hinvariant D ordinaryBlock) :
    MulAction
      (MulAction.stabilizer
        (ActingGroup (k := k) G0 field hinvariant) block)
      {chi : OrdinarySeriesCarrier series //
        ordinarySeriesBlockMap series ordinaryBlock chi = block} := by
  let _ : MulAction (ActingGroup (k := k) G0 field hinvariant)
      (OrdinarySeriesCarrier series) :=
    ordinarySeriesCarrierAction G0 field hinvariant D series hseries
  exact {
    smul := fun a chi ↦
      ⟨a.1 • chi.1, by
        rw [ordinarySeriesBlockMap_equivariant G0 field hinvariant D
          series ordinaryBlock hseries hblock, chi.2]
        exact a.2⟩
    one_smul := by
      intro chi
      apply Subtype.ext
      exact one_smul _ chi.1
    mul_smul := by
      intro a b chi
      apply Subtype.ext
      exact mul_smul a.1 b.1 chi.1 }

/-- The same literal block stabiliser acts on the actual Brauer block
fibre. -/
@[instance_reducible]
def brauerBlockFibreAction
    (iota : PrimeRegularRootEmbedding p k K M)
    (productFormula : BrauerLinearTensorProductFormula iota)
    (brauerBlock : IBr iota → Block) (block : Block)
    (hblock : BrauerBlockEquivariant G0 field hinvariant iota
      productFormula brauerBlock) :
    MulAction
      (MulAction.stabilizer
        (ActingGroup (k := k) G0 field hinvariant) block)
      {phi : IBr iota // brauerBlock phi = block} :=
  TypeCConformalActionAdapter.brauerBlockStabilizerAction
    G0 field hinvariant iota productFormula brauerBlock block hblock

/-- The actual ordinary and Brauer carrier actions realise the tensor and
field operations on the two exact Grothendieck groups.  The cited basic-set
equivalence is used only to select the labels; equivariance is not an input. -/
def labelledKZeroActionData
    (Msys : ModularSystem p K O k)
    (iota : PrimeRegularRootEmbedding p k K M)
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (productFormula : BrauerLinearTensorProductFormula iota)
    (series : Irr K M → Prop)
    (hseries : OrdinarySeriesStable G0 field hinvariant D series)
    (linearEquiv :
      MonoidAlgebra ℤ (OrdinarySeriesCarrier series) ≃ₗ[ℤ]
        MonoidAlgebra ℤ (IBr iota))
    (hdecomposition : ∀ v : MonoidAlgebra ℤ (OrdinarySeriesCarrier series),
      labelledSimpleClassKZero (simpleModuleClassEquivIBr iota hinj).symm
          (linearEquiv v) =
        decompositionMapOfStableReduction Msys iota hcompat
          (labelledSimpleClassKZero
            (ordinarySeriesLabel (K := K) series) v)) :
    let _ : MulAction (ActingGroup (k := k) G0 field hinvariant)
        (OrdinarySeriesCarrier series) :=
      ordinarySeriesCarrierAction G0 field hinvariant D series hseries
    let _ : MulAction (ActingGroup (k := k) G0 field hinvariant) (IBr iota) :=
      brauerCharacterAction G0 field hinvariant iota productFormula
    LabelledKZeroActionData
      (A := ActingGroup (k := k) G0 field hinvariant)
      ((ordinarySeriesBasicSet Msys iota hcompat hinj series
        linearEquiv hdecomposition).toRestrictedIntegralBasicSet) := by
  dsimp only
  letI : MulAction (ActingGroup (k := k) G0 field hinvariant)
      (OrdinarySeriesCarrier series) :=
    ordinarySeriesCarrierAction G0 field hinvariant D series hseries
  letI : MulAction (ActingGroup (k := k) G0 field hinvariant) (IBr iota) :=
    brauerCharacterAction G0 field hinvariant iota productFormula
  exact {
    ordinaryAction := ordinaryKZeroAction G0 field hinvariant D
    modularAction := modularKZeroAction (k := k) G0 field hinvariant
    ordinary_single := by
      intro a chi
      rw [labelledSimpleClassKZero_single, labelledSimpleClassKZero_single]
      exact ordinaryLabel_action G0 field hinvariant D a chi.1
    modular_single := by
      intro a phi
      rw [labelledSimpleClassKZero_single, labelledSimpleClassKZero_single]
      exact brauerLabel_action
        (G0 := G0) (field := field) (hinvariant := hinvariant)
        (iota := iota) (hinj := hinj) (productFormula := productFormula)
        a phi }

end BlockFibres

end ModularRep.PaperProofs.TypeBSpecialCliffordActionAdapter


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
