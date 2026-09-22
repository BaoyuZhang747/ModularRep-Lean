import ModularRep.PaperProofs.TypeBSpecialCliffordActionSplitting

/-!
# Exact basic-set action data without ordinary algebraic closure

The integral basic set retains its existing linear map and stable reduction
identity. The labels are the checked characteristic-zero simple realizations.
Their tensor and field covariance is a theorem of the finite-splitting action
module. No equivariant set matching or Conlon conclusion is a source here.
-/

noncomputable section
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.TypeCCurrentOrdinaryActions
open ModularRep DecompositionBasicSetBridge ExactGrothendieckGroup
open FDRepSimpleClassKZero OrdinaryIrreducibleCharacter
open TypeBOrdinaryLabelSplitting TypeCConformalActionAdapter
open OddConformalProposition311Relative
open TypeBSpecialCliffordActionAdapter
  (ordinarySeriesCarrierAction brauerCharacterAction ordinaryKZeroAction modularKZeroAction)
universe u
variable {p : ℕ} {K O k M E : Type u}
variable [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
variable [CharZero K] [CharP k p] [IsAlgClosed k]
variable [Group M] [Finite M] [Group E]
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


variable (G0 : Subgroup M) [G0.Normal] (field : E →* MulAut M)
variable (hinvariant : FieldInvariantSubgroup.IsInvariant G0 field)
variable (D : OrdinaryReductionEquiv (k := k) (K := K) G0 field hinvariant)

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
      exact TypeBSpecialCliffordActionSplitting.ordinaryLabel_action G0 field hinvariant D a chi.1
    modular_single := by
      intro a phi
      rw [labelledSimpleClassKZero_single, labelledSimpleClassKZero_single]
      exact TypeBSpecialCliffordActionSplitting.brauerLabel_action
        (G0 := G0) (field := field) (hinvariant := hinvariant)
        (iota := iota) (hinj := hinj) (productFormula := productFormula)
        a phi }

end ModularRep.PaperProofs.TypeCCurrentOrdinaryActions


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
