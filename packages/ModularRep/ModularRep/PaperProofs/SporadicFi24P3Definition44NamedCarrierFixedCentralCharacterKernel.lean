import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFixedCentralBlockKernel
import ModularRep.PaperProofs.CentralEllPrimeWeightLocalQuotient

/-!
# Ordinary local character constancy from fixed central support

The same canonical reduction turns the modular kernel statement into
ordinary character constancy on every element of the literal qW kernel.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFixedCentralCharacterKernel

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open SporadicFi24P3Definition44NamedCarrierBrauerBlockAction
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierFixedCentralBlockKernel
open CentralEllPrimeWeightLocalQuotient

universe u

variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G]

local instance subgroupFintype (H : Subgroup G) : Fintype H := Fintype.ofFinite H

theorem character_constant_on_qW_kernel_of_local_kernel
    (iota : PrimeRegularRootEmbedding p k K G)
    (W : CharacterWeight p K G) (source : CanonicalRawReduction iota W)
    (Z : Subgroup G) [Z.Normal]
    (hZ : Z ≤ Subgroup.center G) (hprimeTo : ¬ p ∣ Nat.card Z)
    (hkernel : Z.subgroupOf (Subgroup.normalizer (W.subgroup : Set G)) ≤
      (chosenIBrRepresentation source.normalizerRoot source.localBrauer).ρ.ker) :
    ∀ x : (qW Z W.subgroup).ker,
      W.localCharacter (x : NormalizerQuotient W.subgroup) = W.localCharacter 1 := by
  let N := Subgroup.normalizer (W.subgroup : Set G)
  let ZN := Z.subgroupOf N
  have hZN : Z ≤ N := hZ.trans (Subgroup.center_le_normalizer (W.subgroup : Set G))
  have hcard : Nat.card ZN = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZN).toEquiv
  have hcoprime : (Nat.card ZN).Coprime p := by
    rw [hcard]
    exact (iota.prime.coprime_iff_not_dvd.mpr hprimeTo).symm
  intro x
  have hx : (x : NormalizerQuotient W.subgroup) ∈
      ZN.map (QuotientGroup.mk' (W.subgroup.subgroupOf N)) := by
    rw [← qW_ker_eq_localCentralKernel_map Z W.subgroup hZ]
    exact x.2
  obtain ⟨y, hy, hxy⟩ := hx
  have hyregular : IsPrimeRegular p y :=
    Nat.Coprime.of_dvd_left (Subgroup.orderOf_dvd_natCard ZN hy) hcoprime
  let yp : PrimeRegularElement (G := N) p := ⟨y, hyregular⟩
  let onep : PrimeRegularElement (G := N) p := ⟨1, isPrimeRegular_one⟩
  have hvalues : source.localBrauer.1 yp = source.localBrauer.1 onep := by
    rw [chosenIBrRepresentation_character source.normalizerRoot source.localBrauer]
    exact brauer_apply_eq_one_of_mem_ker _ _ yp (hkernel hy)
  calc
    W.localCharacter (x : NormalizerQuotient W.subgroup) =
        W.localCharacter (QuotientGroup.mk' (W.subgroup.subgroupOf N) y) :=
      congrArg W.localCharacter hxy.symm
    _ = source.localBrauer.1 yp := source.localBrauer_reduction yp
    _ = source.localBrauer.1 onep := hvalues
    _ = W.localCharacter 1 := by
      simpa only [onep, map_one] using (source.localBrauer_reduction onep).symm

variable {Block : Type u} [MulAction (MulAut G)ᵐᵒᵖ Block]

theorem fixedZ_character_constant_on_qW_kernel
    (iota : PrimeRegularRootEmbedding p k K G)
    (O : LocalBlockInductionOperations
      (p := p) (k := k) (K := K) (G := G) (Block := Block))
    (W : CharacterWeight p K G) (source : CanonicalRawReduction iota W)
    (compatibility : CanonicalLocalBlockCompatibility iota O)
    (Z : Subgroup G) [Z.Normal] [Invertible (Fintype.card Z : k)]
    (hZ : Z ≤ Subgroup.center G) (hprimeTo : ¬ p ∣ Nat.card Z)
    (hsupport : O.ambientBlockData.blockIdempotent (O.rawWeightBlock W) *
        centralCharacterIdempotent Z (1 : Z →* kˣ) =
      O.ambientBlockData.blockIdempotent (O.rawWeightBlock W)) :
    ∀ x : (qW Z W.subgroup).ker,
      W.localCharacter (x : NormalizerQuotient W.subgroup) = W.localCharacter 1 := by
  exact character_constant_on_qW_kernel_of_local_kernel iota W source Z hZ hprimeTo
    (fixedZ_local_kernel iota O W source compatibility Z hZ hsupport)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFixedCentralCharacterKernel


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
