import ModularRep.PaperProofs.TypeBSpinEffectiveClassActions
import ModularRep.PaperProofs.TypeBAutomorphismPhysicalLabels
import ModularRep.PaperProofs.TypeBSpinConlonPhysicalSourceInstantiation

/-!
# The Spin effective source from actual class actions and labels

Only the literal diagonal homomorphism/kernel and the selected rational
family's stability under actual diagonal and field twists remain inputs.
The effective actions, simple-generator equations and specified block
equivariance are deductions on the same modular system and integral packet.
The complete former effective-action source is constructed, not assumed.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBSpinEffectiveSourceBinding

open ModularRep ExactGrothendieckGroup FDRepSimpleClassKZero DecompositionBasicSetBridge
open OrdinaryIrreducibleCharacter TypeBCliffordCarriers TypeBSpinStabilizer
open TypeBSpinDiagonalFieldQuotient TypeBSpinEffectiveClassActions
open TypeBSpinQuotientClassActions TypeBSpinFieldClassActions
open TypeBAutomorphismPhysicalLabels TypeBSpinConlonBlockSourceInstantiation
open TypeBIntegralSeriesSplitting

variable {n p f : ℕ} {F K : Type} [Field F] [Finite F] [CharP F p]
  [Field K] [CharZero K]
  (N : NormSource n F) (D : DiagonalSource N)
  {parameters : OddFieldParameters F p f}
  (fs : FieldActionSource n F p f parameters N)

/-- The representative used by all four diagonal class actions is the same coset. -/
theorem diagonal_preimage (g : SpecialClifford n F) :
    (D.quotientEquiv N).symm (D.diagonal g) = projection N g := by
  rw [← D.quotientEquiv_mk N g, MulEquiv.symm_apply_apply]

section Series

variable (series : Irr K (Spin n F N) → Prop)
  (diagonalStable : ∀ (g : SpecialClifford n F) (chi : Irr K (Spin n F N)),
    series chi → series (OrdinaryIrreducibleCharacter.twist K (Spin n F N) chi
      (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹)))
  (fieldStable : ∀ (e : FieldGroup f) (chi : Irr K (Spin n F N)),
    series chi → series (OrdinaryIrreducibleCharacter.twist K (Spin n F N) chi
      (spinFieldAction n F fs e⁻¹)))

include diagonalStable fieldStable in
/-- The actual product preserves the selected family by its two literal factors. -/
theorem effectiveOrdinary_stable (a : OuterGroup f) (chi : Irr K (Spin n F N))
    (hchi : series chi) : series (effectiveOrdinaryHom (k := K) N D fs a chi) := by
  rcases a with ⟨d, e⟩
  obtain ⟨g, rfl⟩ := D.surjective d
  rw [effectiveOrdinaryHom_apply, diagonal_preimage,
    quotientOrdinaryHom_mk_apply, spinFieldOrdinaryHom_apply]
  exact diagonalStable g _ (fieldStable e chi hchi)

/-- The selected subtype inherits the constructed ordinary action. -/
@[instance_reducible]
def selectedSeriesAction : MulAction (OuterGroup f)
    (TypeBSpecialCliffordActionAdapter.OrdinarySeriesCarrier series) where
  smul a chi := ⟨effectiveOrdinaryHom (k := K) N D fs a chi.val,
    effectiveOrdinary_stable N D fs series diagonalStable fieldStable a chi.val chi.property⟩
  one_smul chi := by
    apply Subtype.ext
    change effectiveOrdinaryHom (k := K) N D fs 1 chi.val = chi.val
    rw [map_one]
    rfl
  mul_smul a b chi := by
    apply Subtype.ext
    change effectiveOrdinaryHom (k := K) N D fs (a * b) chi.val =
      effectiveOrdinaryHom (k := K) N D fs a
        (effectiveOrdinaryHom (k := K) N D fs b chi.val)
    rw [map_mul]
    rfl

theorem selectedSeriesAction_val (a : OuterGroup f)
    (chi : TypeBSpecialCliffordActionAdapter.OrdinarySeriesCarrier series) :
    let _ := selectedSeriesAction N D fs series diagonalStable fieldStable
    (a • chi).val = effectiveOrdinaryHom (k := K) N D fs a chi.val := rfl

end Series

variable {ell : ℕ} {O k : Type} [CommRing O] [IsDomain O]
  [Field k] [Algebra O K] [CharP k ell] [IsAlgClosed k]
  [Finite (Spin n F N)]
  (Msys : ModularSystem ell K O k)
  (iota : PrimeRegularRootEmbedding ell k K (Spin n F N))
  (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
  (hinj : IrreducibleBrauerCharacterInjectivity iota)

/-- The effective Brauer action is the actual constructed permutation homomorphism. -/
@[instance_reducible]
def brauerAction : MulAction (OuterGroup f) (IBr iota) :=
  MulAction.compHom (IBr iota) (effectiveBrauerHom N D fs iota)

/-- The effective block action acts on literal primitive central idempotents. -/
@[instance_reducible]
def blockAction : MulAction (OuterGroup f) (LiteralPrimitiveBlock k (Spin n F N)) :=
  MulAction.compHom (LiteralPrimitiveBlock k (Spin n F N))
    (effectiveBlockHom (k := k) N D fs)

/-- Same ordinary simple generators realize the constructed product action. -/
theorem ordinary_generator_action (a : OuterGroup f) (chi : Irr K (Spin n F N)) :
    simpleClassToFDRepKZeroGenerator
        (TypeBOrdinaryLabelSplitting.ordinaryLabel
          (effectiveOrdinaryHom (k := K) N D fs a chi)) =
      effectiveKZeroAction (k := K) N D fs a
        (simpleClassToFDRepKZeroGenerator (TypeBOrdinaryLabelSplitting.ordinaryLabel chi)) := by
  rcases a with ⟨d, e⟩
  obtain ⟨g, rfl⟩ := D.surjective d
  have ho : effectiveOrdinaryHom (k := K) N D fs (D.diagonal g, e) chi =
      OrdinaryIrreducibleCharacter.twist K (Spin n F N)
        (OrdinaryIrreducibleCharacter.twist K (Spin n F N) chi
          (spinFieldAction n F fs e⁻¹))
        (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹) := by
    rw [effectiveOrdinaryHom_apply, diagonal_preimage,
      quotientOrdinaryHom_mk_apply, spinFieldOrdinaryHom_apply]
  have hk (x : FDRepKZero K (Spin n F N)) :
      effectiveKZeroAction (k := K) N D fs (D.diagonal g, e) x =
        twistKZero (k := K) (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹)
          (twistKZero (k := K) (spinFieldAction n F fs e⁻¹) x) := by
    exact (effectiveKZeroAction_apply (k := K) N D fs (D.diagonal g) e x).trans
      ((congrArg (fun q => quotientKZeroAction (k := K) N q
        (spinFieldKZeroAction (k := K) fs e x)) (diagonal_preimage N D g)).trans
        ((quotientKZeroAction_mk_apply (k := K) N g _).trans
          (congrArg (twistKZero (k := K)
            (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹))
            (spinFieldKZeroAction_apply (k := K) fs e x))))
  exact (congrArg (fun x : Irr K (Spin n F N) =>
      simpleClassToFDRepKZeroGenerator (TypeBOrdinaryLabelSplitting.ordinaryLabel x)) ho).trans
    ((ordinaryLabel_twist _ _).trans
      ((congrArg (twistKZero (k := K)
        (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹))
        (ordinaryLabel_twist chi _)).trans (hk _).symm))

/-- Same prescribed-root Brauer generators realize that product action. -/
theorem brauer_generator_action (a : OuterGroup f) (phi : IBr iota) :
    simpleClassToFDRepKZeroGenerator
        ((simpleModuleClassEquivIBr iota hinj).symm (effectiveBrauerHom N D fs iota a phi)) =
      effectiveKZeroAction (k := k) N D fs a
        (simpleClassToFDRepKZeroGenerator ((simpleModuleClassEquivIBr iota hinj).symm phi)) := by
  rcases a with ⟨d, e⟩
  obtain ⟨g, rfl⟩ := D.surjective d
  have hb : effectiveBrauerHom N D fs iota (D.diagonal g, e) phi =
      IrreducibleBrauerCharacter.twist iota
        (IrreducibleBrauerCharacter.twist iota phi (spinFieldAction n F fs e⁻¹))
        (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹) := by
    rw [effectiveBrauerHom_apply, diagonal_preimage,
      quotientBrauerHom_mk_apply, spinFieldBrauerHom_apply]
  have hk (x : FDRepKZero k (Spin n F N)) :
      effectiveKZeroAction (k := k) N D fs (D.diagonal g, e) x =
        twistKZero (k := k) (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹)
          (twistKZero (k := k) (spinFieldAction n F fs e⁻¹) x) := by
    exact (effectiveKZeroAction_apply (k := k) N D fs (D.diagonal g) e x).trans
      ((congrArg (fun q => quotientKZeroAction (k := k) N q
        (spinFieldKZeroAction (k := k) fs e x)) (diagonal_preimage N D g)).trans
        ((quotientKZeroAction_mk_apply (k := k) N g _).trans
          (congrArg (twistKZero (k := k)
            (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹))
            (spinFieldKZeroAction_apply (k := k) fs e x))))
  exact (congrArg (fun x : IBr iota => simpleClassToFDRepKZeroGenerator
      ((simpleModuleClassEquivIBr iota hinj).symm x)) hb).trans
    ((brauerLabel_twist iota hinj _ _).trans
      ((congrArg (twistKZero (k := k)
        (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹))
        (brauerLabel_twist iota hinj phi _)).trans (hk _).symm))

variable [Fintype (LiteralPrimitiveBlock k (Spin n F N))]
  (blocks : BlockIdempotentDecomposition
    (fun b : LiteralPrimitiveBlock k (Spin n F N) => b.val))

/-- Both exact primitive-block catalogues transform by the same product action. -/
theorem brauerBlock_action (a : OuterGroup f) (phi : IBr iota) :
    irreducibleBrauerCharacterBlock iota hinj blocks (effectiveBrauerHom N D fs iota a phi) =
      effectiveBlockHom (k := k) N D fs a (irreducibleBrauerCharacterBlock iota hinj blocks phi) := by
  rcases a with ⟨d, e⟩
  obtain ⟨g, rfl⟩ := D.surjective d
  rw [effectiveBrauerHom_apply, effectiveBlockHom_apply, diagonal_preimage,
    quotientBrauerHom_mk_apply, spinFieldBrauerHom_apply,
    quotientBlockHom_mk_apply, spinFieldBlockHom_apply,
    brauerBlock_twist, brauerBlock_twist]

variable [ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card (Spin n F N))]
  (ordinary : TypeBOrdinaryBlockSplitting.OrdinaryBlockSource Msys iota hinj blocks)

include hcompat in
/-- The specified ordinary selector is equivariant, by its actual decomposition support. -/
theorem ordinaryBlock_action (a : OuterGroup f) (chi : Irr K (Spin n F N)) :
    ordinary.physical.ordinaryBlock (effectiveOrdinaryHom (k := K) N D fs a chi) =
      effectiveBlockHom (k := k) N D fs a (ordinary.physical.ordinaryBlock chi) := by
  rcases a with ⟨d, e⟩
  obtain ⟨g, rfl⟩ := D.surjective d
  rw [effectiveOrdinaryHom_apply, effectiveBlockHom_apply, diagonal_preimage,
    quotientOrdinaryHom_mk_apply, spinFieldOrdinaryHom_apply,
    quotientBlockHom_mk_apply, spinFieldBlockHom_apply,
    ordinaryBlock_twist iota hinj Msys hcompat blocks ordinary,
    ordinaryBlock_twist iota hinj Msys hcompat blocks ordinary]

variable [NeZero f]
  (source : SpinRationalSeriesSource (p := p) (ell := ell) (K := K) (k := k) (N := N))
  (certificate : Theorem23Certificate Msys iota hcompat hinj source.family
    blocks source.blockSeries p 2)
  (hEll : Nat.Prime ell) (hOdd : Odd ell) (hNondef : ell ≠ p)
  (diagonalStable : ∀ (g : SpecialClifford n F) (chi : Irr K (Spin n F N)),
    source.family.selectedSeries chi → source.family.selectedSeries
      (OrdinaryIrreducibleCharacter.twist K (Spin n F N) chi
        (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹)))
  (fieldStable : ∀ (e : FieldGroup f) (chi : Irr K (Spin n F N)),
    source.family.selectedSeries chi → source.family.selectedSeries
      (OrdinaryIrreducibleCharacter.twist K (Spin n F N) chi
        (spinFieldAction n F fs e⁻¹)))

/-- All six action formulas and the literal generator joins are constructed.
The integral packet is exactly the one chosen by the frozen Spin consumer. -/
def effectiveActionSource :
    let _ := selectedSeriesAction N D fs source.family.selectedSeries diagonalStable fieldStable
    let _ := brauerAction N D fs iota
    let _ := blockAction (k := k) N D fs
    EffectiveActionSource fs iota hinj source.family.selectedSeries
      (TypeBSpinConlonSplittingSourceInstantiation.spinBasicSetFromTheorem23
        Msys iota hcompat hinj source blocks certificate hEll hOdd hNondef) := by
  letI := selectedSeriesAction N D fs source.family.selectedSeries diagonalStable fieldStable
  letI := brauerAction N D fs iota
  letI := blockAction (k := k) N D fs
  refine {
    labelled := {
      ordinaryAction := effectiveKZeroAction (k := K) N D fs
      modularAction := effectiveKZeroAction (k := k) N D fs
      ordinary_single := ?_
      modular_single := ?_ }
    diagonal := D.diagonal
    diagonal_surjective := D.surjective
    diagonal_kernel := D.kernel
    ordinary_diagonal := effectiveKZeroAction_diagonal_apply (k := K) N D fs
    modular_diagonal := effectiveKZeroAction_diagonal_apply (k := k) N D fs
    ordinary_field := effectiveKZeroAction_field_apply (k := K) N D fs
    modular_field := effectiveKZeroAction_field_apply (k := k) N D fs
    block_diagonal := effectiveBlockHom_diagonal_apply (k := k) N D fs
    block_field := effectiveBlockHom_field_apply (k := k) N D fs }
  · intro a chi
    rw [labelledSimpleClassKZero_single, labelledSimpleClassKZero_single]
    change simpleClassToFDRepKZeroGenerator
        (TypeBOrdinaryLabelSplitting.ordinaryLabel
          (effectiveOrdinaryHom (k := K) N D fs a chi.val)) =
      effectiveKZeroAction (k := K) N D fs a
        (simpleClassToFDRepKZeroGenerator (TypeBOrdinaryLabelSplitting.ordinaryLabel chi.val))
    exact ordinary_generator_action N D fs a chi.val
  · intro a phi
    rw [labelledSimpleClassKZero_single, labelledSimpleClassKZero_single]
    exact brauer_generator_action N D fs iota hinj a phi

end ModularRep.PaperProofs.TypeBSpinEffectiveSourceBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
