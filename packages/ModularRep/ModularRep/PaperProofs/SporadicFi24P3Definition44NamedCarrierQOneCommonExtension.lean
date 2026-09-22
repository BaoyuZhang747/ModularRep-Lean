import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFactorOneExtension
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSamePairQOneGroups
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction

/-! One global extension gives the common Q=1 pair on the actual ambient
and local subgroups. The ordinary local model is retained separately. -/

noncomputable section
set_option maxHeartbeats 2000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQOneCommonExtension

open ModularRep ModularRep.CharacterWeight
open Representation.Extension
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierAssociatedProjectiveModel
open SporadicFi24P3Definition44NamedCarrierFactorOneExtension
open SporadicFi24P3Definition44NamedCarrierSamePairQOneGroups

universe u
variable {p : ℕ} {k K G A : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Group A] [Finite A]
variable (iota : PrimeRegularRootEmbedding p k K G) (phi : IBr iota)
variable (V : CharacterWeight p K G) (source : CanonicalRawReduction iota V)
variable (B : Subgroup A) (eG : G ≃* B)
variable (D : Subgroup A) (hD : D = ⊤) (L : Subgroup D)
variable (eN : Subgroup.normalizer (V.subgroup : Set G) ≃* L)
variable (square : D.subtype.comp (L.subtype.comp eN.toMonoidHom) =
  B.subtype.comp (eG.toMonoidHom.comp (Subgroup.normalizer (V.subgroup : Set G)).subtype))
variable (hlocal : PrimeRegularClassFunction.pullback
  (Subgroup.normalizer (V.subgroup : Set G)).subtype phi.val = source.localBrauer.val)
local notation "rB" => iota.alongMulEquiv eG
local notation "phiB" => IrreducibleBrauerCharacter.alongMulEquiv iota eG phi
local notation "rL" => source.normalizerRoot.alongMulEquiv eN
local notation "phiL" => IrreducibleBrauerCharacter.alongMulEquiv source.normalizerRoot eN source.localBrauer

def localExtensionOfGlobal
    (rA : PrimeRegularRootEmbedding p k K A)
    (globalW : BrauerCharacterExtensionWitness rA rB phiB) :
    BrauerCharacterExtensionWitness
      (rA.alongMulEquiv (ambientEquivOfEqTop D hD).symm) rL phiL := by
  refine ⟨IrreducibleBrauerCharacter.alongMulEquiv rA
    (ambientEquivOfEqTop D hD).symm globalW.val, ?_⟩
  apply PrimeRegularClassFunction.ext
  intro x
  let n := PrimeRegularElement.map eN.symm.toMonoidHom x
  let b := PrimeRegularElement.map eG.toMonoidHom
    (PrimeRegularElement.map (Subgroup.normalizer (V.subgroup : Set G)).subtype n)
  have hx : PrimeRegularElement.map D.subtype (PrimeRegularElement.map L.subtype x) =
      PrimeRegularElement.map B.subtype b := by
    apply Subtype.ext
    change (x.val.val : A) = (eG ((eN.symm x.val).val) : A)
    have h := DFunLike.congr_fun square n.val
    change ((eN (eN.symm x.val)).val : A) =
      (eG ((eN.symm x.val).val) : A) at h
    simpa only [MulEquiv.apply_symm_apply] using h
  have hb : PrimeRegularElement.map eG.symm.toMonoidHom b =
      PrimeRegularElement.map (Subgroup.normalizer (V.subgroup : Set G)).subtype n := by
    apply Subtype.ext
    exact eG.symm_apply_apply _
  have hg := congrArg (fun chi : PrimeRegularClassFunction K B p => chi b) globalW.property
  have hl := congrArg (fun chi : PrimeRegularClassFunction K
    (Subgroup.normalizer (V.subgroup : Set G)) p => chi n) hlocal
  change globalW.val.val (PrimeRegularElement.map D.subtype (PrimeRegularElement.map L.subtype x)) =
    source.localBrauer.val n
  exact (congrArg globalW.val.val hx).trans
    (hg.trans ((congrArg phi.val hb).trans hl))

theorem localExtensionOfGlobal_equality
    (rA : PrimeRegularRootEmbedding p k K A)
    (globalW : BrauerCharacterExtensionWitness rA rB phiB) :
    PrimeRegularClassFunction.pullback D.subtype globalW.val.val =
      (localExtensionOfGlobal iota phi V source B eG D hD L eN (square := square) (hlocal := hlocal) rA globalW).val.val := by
  apply PrimeRegularClassFunction.ext
  intro x
  rfl

variable {W : Type u} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
variable [B.Normal] (rho : Representation k B W)

/-- The actual pair is explicitly linked to the retained global model. -/
def CommonExtensionFromModel (M : AssociatedProjectiveModel B rho)
    (hM : M.factorSet = ScalarFactorSet.trivial)
    (rA : PrimeRegularRootEmbedding p k K A) : Prop :=
  ∃ globalW : BrauerCharacterExtensionWitness rA rB phiB,
    globalW.val.val = (representationOfFactorOne M hM).brauerCharacterOfRootEmbedding rA ∧
    ∃ localW : BrauerCharacterExtensionWitness
      (rA.alongMulEquiv (ambientEquivOfEqTop D hD).symm) rL phiL,
      PrimeRegularClassFunction.pullback D.subtype globalW.val.val = localW.val.val

include square hlocal in
theorem common_extension_from_model
    (M : AssociatedProjectiveModel B rho) (hM : M.factorSet = ScalarFactorSet.trivial)
    (hirr : Representation.IsIrreducible rho)
    (haffords : rho.brauerCharacterOfRootEmbedding rB = (phiB).val)
    (rA : PrimeRegularRootEmbedding p k K A)
    (hroots : ∀ zeta : rootsOfUnity (primeRegularExponent p B) k,
      (rB).lift (((zeta : kˣ) : k)) = rA.lift (((zeta : kˣ) : k))) :
    CommonExtensionFromModel iota phi V source B eG D hD L eN rho M hM rA := by
  let globalW := brauerExtensionOfFactorOne M hM hirr rA rB phiB haffords hroots
  exact ⟨globalW, rfl,
    localExtensionOfGlobal iota phi V source B eG D hD L eN (square := square) (hlocal := hlocal) rA globalW,
    localExtensionOfGlobal_equality iota phi V source B eG D hD L eN (square := square) (hlocal := hlocal) rA globalW⟩

include square hlocal in
theorem exists_common_extension_from_model
    (M : AssociatedProjectiveModel B rho) (hM : M.factorSet = ScalarFactorSet.trivial)
    (hirr : Representation.IsIrreducible rho)
    (haffords : rho.brauerCharacterOfRootEmbedding rB = (phiB).val)
    (seed : Nonempty (PrimeRegularRootEmbedding p k K A)) :
    ∃ rA : PrimeRegularRootEmbedding p k K A,
      (∀ zeta : rootsOfUnity (primeRegularExponent p B) k,
        (rB).lift (((zeta : kˣ) : k)) = rA.lift (((zeta : kˣ) : k))) ∧
      CommonExtensionFromModel iota phi V source B eG D hD L eN rho M hM rA := by
  obtain ⟨rA, hroots⟩ := PrimeRegularRootEmbedding.exists_ambient_agreeing_on_subgroup B rB seed
  exact ⟨rA, hroots, common_extension_from_model iota phi V source B eG D hD L eN
    square hlocal rho M hM hirr haffords rA hroots⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQOneCommonExtension


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
