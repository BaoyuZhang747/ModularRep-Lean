import ModularRep.PaperProofs.TypeBIntegralSeriesSplitting
import ModularRep.PaperProofs.TypeBOrdinaryTraceSeparationSplitting
import ModularRep.PaperProofs.TypeBSpecialCliffordActionAdapter
import ModularRep.KZeroLinearCharacterSemidirect

/-!
# Actual special-Clifford tensor/field labels over the prescribed ordinary field

The existing semidirect groups, actual character actions and exact K0 actions
are reused. The ordinary simple labels and their reverse trace separation
come from the checked characteristic-zero supplements. The same per-series
integral data produces the basic set used by the labelled action record.
No ordinary algebraic closure or new action/basic-set conclusion is supplied.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBSpecialCliffordActionSplitting

open ModularRep DecompositionBasicSetBridge ExactGrothendieckGroup
open FDRepSimpleClassKZero OrdinaryIrreducibleCharacter
open TypeBOrdinaryLabelSplitting TypeCConformalActionAdapter
open TypeBSpecialCliffordActionAdapter
  (ordinarySemidirectMap modularSemidirectMap ordinaryCharacterAction brauerCharacterAction
    ordinaryKZeroAction modularKZeroAction OrdinaryLiftReductionCompatible
    ordinarySeriesCarrierAction ordinarySeriesBlockMap)
open scoped MonoidAlgebra

universe u

variable {p : ℕ} {K O k M E Block : Type u}
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharZero K] [CharP k p] [IsAlgClosed k]
  [Group M] [Finite M] [Group E]
  (G0 : Subgroup M) [G0.Normal]
  (field : E →* MulAut M)
  (hinvariant : FieldInvariantSubgroup.IsInvariant G0 field)
  (D : OrdinaryReductionEquiv (k := k) (K := K) G0 field hinvariant)

/-- The existing exact ordinary action has the literal inverse convention. -/
theorem ordinaryKZeroAction_apply
    (a : ActingGroup (k := k) G0 field hinvariant) (x : FDRepKZero K M) :
    ordinaryKZeroAction G0 field hinvariant D a x =
      linearCharacterTwistKZero
        (OrdinaryReductionEquiv.lift (G0 := G0) (field := field)
          (hinvariant := hinvariant) D a.left)⁻¹
        (twistKZero (k := K) (field a.right⁻¹) x) :=
  rfl

/-- The existing modular action uses the same field factor and actual lift. -/
theorem modularKZeroAction_apply
    (a : ActingGroup (k := k) G0 field hinvariant) (x : FDRepKZero k M) :
    modularKZeroAction (k := k) G0 field hinvariant a x =
      linearCharacterTwistKZero a.left.val⁻¹
        (twistKZero (k := k) (field a.right⁻¹) x) :=
  rfl

/-- The shared combined tensor/field reduction theorem supplies naturality
on the SAME ordinary/modular lift, root and exact K0 actions. -/
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
  let phi := LinearCharactersTrivialOn.fieldAction (k := k) field
    (FieldInvariantSubgroup.isFieldStable G0 field hinvariant)
  let liftK := OrdinaryReductionEquiv.lift (G0 := G0) (field := field)
    (hinvariant := hinvariant) D
  let liftk := (linearCharactersTrivialOn (k := k) G0).subtype
  have fieldK : ∀ e : E,
      liftK.comp (phi e).toMonoidHom =
        (OrdinaryIrreducibleCharacter.linearCharacterFieldAction (k := K) field e).toMonoidHom.comp
          liftK := by
    intro e
    apply MonoidHom.ext
    intro lambda
    exact OrdinaryReductionEquiv.lift_field_equivariant
      (G0 := G0) (field := field) (hinvariant := hinvariant) D e lambda
  have fieldk : ∀ e : E,
      liftk.comp (phi e).toMonoidHom =
        (OrdinaryIrreducibleCharacter.linearCharacterFieldAction (k := k) field e).toMonoidHom.comp
          liftk := by
    intro e
    ext lambda g
    rfl
  intro a x
  rw [ordinaryKZeroAction_apply, modularKZeroAction_apply]
  have natural := decompositionMapOfStableReduction_tensorFieldKZeroRepresentationOf
    Msys iota hcompat productFormula phi field liftK liftk fieldK fieldk hlift a x
  simpa only [tensorFieldKZeroRepresentationOf_apply, liftK, liftk,
    Subgroup.subtype_apply] using natural

/-- Actual ordinary tensor and automorphism transport of the checked chosen
simple label is realized by the SAME exact K0 operations. -/
theorem ordinaryLabel_linearTwist_twist
    (chi : Irr K M) (alpha : MulAut M) (lambda : M →* Kˣ) :
    simpleClassToFDRepKZeroGenerator
        (ordinaryLabel
          (OrdinaryIrreducibleCharacter.linearTwist
            (OrdinaryIrreducibleCharacter.twist K M chi alpha) lambda)) =
      linearCharacterTwistKZero lambda
        (twistKZero (k := K) alpha
          (simpleClassToFDRepKZeroGenerator
            (ordinaryLabel chi))) := by
  let V0 := simpleClassFDRep (ordinaryLabel chi)
  let Vfield := (FDRep.twistEquivalence K M alpha).functor.obj V0
  let V1 := FDRep.of
    (Representation.linearCharacterTwist (FDRep.ρ Vfield) lambda)
  have hV0 : Representation.IsIrreducible (FDRep.ρ V0) :=
    simpleClassFDRep_irreducible (ordinaryLabel chi)
  have hV1 : Representation.IsIrreducible (FDRep.ρ V1) := by
    change Representation.IsIrreducible
      (Representation.linearCharacterTwist
        (Representation.twist (FDRep.ρ V0) alpha) lambda)
    exact (hV0.twist alpha).linearCharacterTwist lambda
  let X1 := simpleClassOfIrreducibleFDRep V1 hV1
  have hclass :
      ordinaryLabel
          (OrdinaryIrreducibleCharacter.linearTwist
            (OrdinaryIrreducibleCharacter.twist K M chi alpha) lambda) =
        X1 := by
    apply TypeBOrdinaryTraceSeparationSplitting.simpleModuleClass_character_injective
    calc
      (simpleClassFDRep
          (ordinaryLabel
            (OrdinaryIrreducibleCharacter.linearTwist
              (OrdinaryIrreducibleCharacter.twist K M chi alpha)
              lambda))).character =
          (OrdinaryIrreducibleCharacter.linearTwist
            (OrdinaryIrreducibleCharacter.twist K M chi alpha)
            lambda).1 :=
        ordinaryLabel_character _
      _ = V1.character := by
        funext g
        change (lambda g : K) * chi (alpha g) =
          (Representation.linearCharacterTwist
            (Representation.twist (FDRep.ρ V0) alpha) lambda).character g
        rw [Representation.character_linearCharacterTwist]
        change (lambda g : K) * chi (alpha g) =
          (lambda g : K) * V0.character (alpha g)
        rw [show V0.character = chi.1 by
          exact ordinaryLabel_character chi]
      _ = (simpleClassFDRep X1).character :=
        (FDRep.char_iso
          (simpleClassOfIrreducibleFDRepIso V1 hV1)).symm
  change ExactGrothendieckGroup.classOf (FDRep K M)
      (simpleClassFDRep
        (ordinaryLabel
          (OrdinaryIrreducibleCharacter.linearTwist
            (OrdinaryIrreducibleCharacter.twist K M chi alpha) lambda))) =
    linearCharacterTwistKZero lambda
      (twistKZero (k := K) alpha
        (ExactGrothendieckGroup.classOf (FDRep K M)
          (simpleClassFDRep (ordinaryLabel chi))))
  rw [twistKZero_classOf, linearCharacterTwistKZero_classOf]
  calc
    simpleClassToFDRepKZeroGenerator
        (ordinaryLabel
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
                (simpleClassFDRep (ordinaryLabel chi))))
            lambda)) := rfl

/-- On the actual ordinary `Irr` carrier, the combined action and the
constructed exact `K₀` action agree on every simple generator. -/
theorem ordinaryLabel_action
    (a : ActingGroup (k := k) G0 field hinvariant) (chi : Irr K M) :
    let _ : MulAction (ActingGroup (k := k) G0 field hinvariant) (Irr K M) :=
      ordinaryCharacterAction G0 field hinvariant D
    simpleClassToFDRepKZeroGenerator
        (ordinaryLabel (a • chi)) =
      ordinaryKZeroAction G0 field hinvariant D a
        (simpleClassToFDRepKZeroGenerator
          (ordinaryLabel chi)) := by
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

section BlockFibres

variable [MulAction (ActingGroup (k := k) G0 field hinvariant) Block]

/-- The existing selected subtype action preserves the SAME specified block
map whenever the given ambient ordinary block action does. -/
theorem ordinarySeriesBlockMap_equivariant
    (series : Irr K M → Prop) (ordinaryBlock : Irr K M → Block)
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
  exact hblock a chi.val

/-- The literal block stabilizer acts on the existing nested ordinary
series/set of blocks, without a new carrier or ordinary closure assumption. -/
@[instance_reducible]
def ordinaryBlockFibreAction
    (series : Irr K M → Prop) (ordinaryBlock : Irr K M → Block) (b : Block)
    (hseries : OrdinarySeriesStable G0 field hinvariant D series)
    (hblock : OrdinaryBlockEquivariant G0 field hinvariant D ordinaryBlock) :
    MulAction (MulAction.stabilizer (ActingGroup (k := k) G0 field hinvariant) b)
      {chi : OrdinarySeriesCarrier series // ordinarySeriesBlockMap series ordinaryBlock chi = b} := by
  let _ : MulAction (ActingGroup (k := k) G0 field hinvariant)
      (OrdinarySeriesCarrier series) :=
    ordinarySeriesCarrierAction G0 field hinvariant D series hseries
  exact {
    smul := fun a chi =>
      ⟨a.val • chi.val, by
        rw [ordinarySeriesBlockMap_equivariant G0 field hinvariant D
          series ordinaryBlock hseries hblock, chi.property]
        exact a.property⟩
    one_smul := by
      intro chi
      apply Subtype.ext
      exact one_smul _ chi.val
    mul_smul := by
      intro a b chi
      apply Subtype.ext
      exact mul_smul a.val b.val chi.val }

end BlockFibres

section DerivedBasicSet

variable {I : Type u} [Fintype I]
  (Msys : ModularSystem p K O k)
  (iota : PrimeRegularRootEmbedding p k K M)
  (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
  (hinj : IrreducibleBrauerCharacterInjectivity iota)
  (productFormula : BrauerLinearTensorProductFormula iota)
  (S : TypeBRationalSeriesSource.RationalSeriesSource K M I)
  [Fintype (LiteralPrimitiveBlock k M)]
  (blocks : BlockIdempotentDecomposition
    (fun b : LiteralPrimitiveBlock k M => b.val))
  (blockSeries : LiteralPrimitiveBlock k M → I)
  (data : TypeBIntegralSeriesSplitting.IntegralSeriesData
    Msys iota hcompat hinj S blocks blockSeries)
  (hseries : OrdinarySeriesStable G0 field hinvariant D S.selectedSeries)

/-- The SAME per-series packet's derived global basic set realizes the
actual tensor/field operations on both exact Grothendieck groups.
Its integral map, simple labels and generator equations are not resourced. -/
def labelledKZeroActionData :
    let _ : MulAction (ActingGroup (k := k) G0 field hinvariant) S.Basic :=
      ordinarySeriesCarrierAction G0 field hinvariant D S.selectedSeries hseries
    let _ : MulAction (ActingGroup (k := k) G0 field hinvariant) (IBr iota) :=
      brauerCharacterAction G0 field hinvariant iota productFormula
    LabelledKZeroActionData
      (A := ActingGroup (k := k) G0 field hinvariant)
      ((data.globalBasicSet Msys iota hcompat hinj S blocks blockSeries).toRestrictedIntegralBasicSet) := by
  dsimp only
  letI : MulAction (ActingGroup (k := k) G0 field hinvariant) S.Basic :=
    ordinarySeriesCarrierAction G0 field hinvariant D S.selectedSeries hseries
  letI : MulAction (ActingGroup (k := k) G0 field hinvariant) (IBr iota) :=
    brauerCharacterAction G0 field hinvariant iota productFormula
  exact {
    ordinaryAction := ordinaryKZeroAction G0 field hinvariant D
    modularAction := modularKZeroAction (k := k) G0 field hinvariant
    ordinary_single := by
      intro a chi
      rw [labelledSimpleClassKZero_single, labelledSimpleClassKZero_single]
      exact ordinaryLabel_action G0 field hinvariant D a chi.val
    modular_single := by
      intro a phi
      rw [labelledSimpleClassKZero_single, labelledSimpleClassKZero_single]
      exact brauerLabel_action (G0 := G0) (field := field) (hinvariant := hinvariant)
        (iota := iota) (hinj := hinj) (productFormula := productFormula) a phi }

end DerivedBasicSet

end ModularRep.PaperProofs.TypeBSpecialCliffordActionSplitting


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
