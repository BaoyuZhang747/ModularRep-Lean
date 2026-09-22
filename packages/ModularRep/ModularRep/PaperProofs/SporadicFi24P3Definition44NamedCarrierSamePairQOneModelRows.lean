import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQOneCommonExtension

/-! Universal realization covers each actual retained model in the AD3
existential, while leaving its independent local model unchanged. -/

noncomputable section
set_option maxHeartbeats 2000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSamePairQOneModelRows

open ModularRep ModularRep.CharacterWeight
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierAssociatedProjectiveModel
open SporadicFi24P3Definition44NamedCarrierQOneCommonExtension

universe u
variable {p : ℕ} {k K G A : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Group A] [Finite A]
variable (iota : PrimeRegularRootEmbedding p k K G) (phi : IBr iota)
variable (V : CharacterWeight p K G) (source : CanonicalRawReduction iota V)
variable (B : Subgroup A) [B.Normal] (eG : G ≃* B)
variable (D : Subgroup A) (hD : D = ⊤) (L : Subgroup D)
variable (eN : Subgroup.normalizer (V.subgroup : Set G) ≃* L)
local notation "rB" => iota.alongMulEquiv eG
local notation "phiB" => IrreducibleBrauerCharacter.alongMulEquiv iota eG phi

def EveryModelCommonAtRoot (rA : PrimeRegularRootEmbedding p k K A) : Prop :=
  ∀ (WG : FDRep k B) (MG : AssociatedProjectiveModel B WG.ρ)
    (hMG : MG.factorSet = ScalarFactorSet.trivial),
    Representation.IsIrreducible WG.ρ →
    (phiB).val = Representation.brauerCharacterOfRootEmbedding WG.ρ rB →
    CommonExtensionFromModel iota phi V source B eG D hD L eN WG.ρ MG hMG rA

def EveryModelCommon : Prop :=
  ∀ (WG : FDRep k B) (MG : AssociatedProjectiveModel B WG.ρ)
    (hMG : MG.factorSet = ScalarFactorSet.trivial),
    Representation.IsIrreducible WG.ρ →
    (phiB).val = Representation.brauerCharacterOfRootEmbedding WG.ρ rB →
    ∃ rA : PrimeRegularRootEmbedding p k K A,
      (∀ zeta : rootsOfUnity (primeRegularExponent p B) k,
        (rB).lift (((zeta : kˣ) : k)) = rA.lift (((zeta : kˣ) : k))) ∧
      CommonExtensionFromModel iota phi V source B eG D hD L eN WG.ρ MG hMG rA

variable (square : D.subtype.comp (L.subtype.comp eN.toMonoidHom) =
  B.subtype.comp (eG.toMonoidHom.comp (Subgroup.normalizer (V.subgroup : Set G)).subtype))
variable (hlocal : PrimeRegularClassFunction.pullback
  (Subgroup.normalizer (V.subgroup : Set G)).subtype phi.val = source.localBrauer.val)

include square hlocal in
theorem every_model_common_at_root (rA : PrimeRegularRootEmbedding p k K A)
    (hroots : ∀ zeta : rootsOfUnity (primeRegularExponent p B) k,
      (rB).lift (((zeta : kˣ) : k)) = rA.lift (((zeta : kˣ) : k))) :
    EveryModelCommonAtRoot iota phi V source B eG D hD L eN rA := by
  intro WG MG hMG hirr haffords
  exact common_extension_from_model iota phi V source B eG D hD L eN square hlocal
    WG.ρ MG hMG hirr haffords.symm rA hroots

include square hlocal in
theorem every_model_common (seed : Nonempty (PrimeRegularRootEmbedding p k K A)) :
    EveryModelCommon iota phi V source B eG D hD L eN := by
  intro WG MG hMG hirr haffords
  exact exists_common_extension_from_model iota phi V source B eG D hD L eN square hlocal
    WG.ρ MG hMG hirr haffords.symm seed

/-- Apply the universal conclusion to the same representation underlying an AD3 model. -/
theorem every_model_common_apply
    (h : EveryModelCommon iota phi V source B eG D hD L eN)
    {W : Type u} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (rho : Representation k B W) (M : AssociatedProjectiveModel B rho)
    (hM : M.factorSet = ScalarFactorSet.trivial)
    (hirr : Representation.IsIrreducible rho)
    (haffords : (phiB).val = rho.brauerCharacterOfRootEmbedding rB) :
    ∃ rA : PrimeRegularRootEmbedding p k K A,
      (∀ zeta : rootsOfUnity (primeRegularExponent p B) k,
        (rB).lift (((zeta : kˣ) : k)) = rA.lift (((zeta : kˣ) : k))) ∧
      CommonExtensionFromModel iota phi V source B eG D hD L eN rho M hM rA :=
  h (FDRep.of rho) M hM hirr haffords

/-- The original-group branches apply the same model at the fixed original root. -/
theorem every_model_common_at_root_apply
    (rA : PrimeRegularRootEmbedding p k K A)
    (h : EveryModelCommonAtRoot iota phi V source B eG D hD L eN rA)
    {W : Type u} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (rho : Representation k B W) (M : AssociatedProjectiveModel B rho)
    (hM : M.factorSet = ScalarFactorSet.trivial)
    (hirr : Representation.IsIrreducible rho)
    (haffords : (phiB).val = rho.brauerCharacterOfRootEmbedding rB) :
    CommonExtensionFromModel iota phi V source B eG D hD L eN rho M hM rA :=
  h (FDRep.of rho) M hM hirr haffords

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSamePairQOneModelRows


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
