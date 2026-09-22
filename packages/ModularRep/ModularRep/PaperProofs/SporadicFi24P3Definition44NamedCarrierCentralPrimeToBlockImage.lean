import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientBlockAlgebra
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBrauerBlockAction

/-! The actual Brauer block image under a central prime-to-p quotient.
The sole literature input is unselected guarded primitivity of block
images (Navarro, pp.198--199 and Theorem 9.9(c)). Nonzeroness and the
selected specified block equality are derived from actual inflation. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage

open ModularRep ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientBlockAlgebra
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBrauerBlockAction

universe u

structure CentralPrimeToPrimitiveImageSource
    {p : ℕ} {k G H : Type u}
    [Field k] [CharP k p] [IsAlgClosed k]
    [Group G] [Finite G] [Group H] [Finite H]
    (f : G →* H) (hf : Function.Surjective f) (hp : p.Prime)
    (hcentral : f.ker ≤ Subgroup.center G)
    (hprimeTo : ¬ p ∣ Nat.card f.ker) : Prop where
  primitive_image_of_ne_zero :
    ∀ e : k[G], IsPrimitiveCentralIdempotent e →
      algebraMapOf f e ≠ 0 → IsPrimitiveCentralIdempotent (algebraMapOf f e)

theorem algebra_action_map
    {k G H : Type u} [Field k] [Group G] [Group H]
    (f : G →* H) {V : Type u} [AddCommGroup V] [Module k V]
    (rho : Representation k H V) (b : k[G]) :
    (rho.pullback f).asAlgebraHom b = rho.asAlgebraHom (algebraMapOf f b) := by
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp
  | add b c hb hc => simp only [map_add, hb, hc]
  | single g a => simp [algebraMapOf, Representation.asAlgebraHom_single]

theorem actualBrauerBlock_image
    {p : ℕ} {k K G H I J : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group G] [Finite G] [Group H] [Finite H] [Fintype I] [Fintype J]
    {eG : I → k[G]} {eH : J → k[H]}
    (f : G →* H) (hf : Function.Surjective f) (hp : p.Prime)
    (hcentral : f.ker ≤ Subgroup.center G)
    (hprimeTo : ¬ p ∣ Nat.card f.ker)
    (S : CentralPrimeToPrimitiveImageSource (k := k) f hf hp hcentral hprimeTo)
    (iotaG : PrimeRegularRootEmbedding p k K G)
    (iotaH : PrimeRegularRootEmbedding p k K H)
    (hcompat : ∀ W : FDRep k H,
      Representation.BrauerRootLiftCompatibleAlong W.ρ iotaH iotaG f)
    (injG : IrreducibleBrauerCharacterInjectivity iotaG)
    (injH : IrreducibleBrauerCharacterInjectivity iotaH)
    (DG : BlockIdempotentDecomposition eG) (DH : BlockIdempotentDecomposition eH)
    (phiG : IBr iotaG) (phiH : IBr iotaH)
    (values : phiG.1 = PrimeRegularClassFunction.pullback f phiH.1) :
    algebraMapOf f (eG (irreducibleBrauerCharacterBlock iotaG injG DG phiG)) =
      eH (irreducibleBrauerCharacterBlock iotaH injH DH phiH) := by
  obtain ⟨V, hV, hchar⟩ := phiH.2
  let rho : Representation k G V := Representation.pullback V.ρ f
  have hrho : Representation.IsIrreducible rho := hV.pullback f hf
  have hcharG : phiG.1 = Representation.brauerCharacterOfRootEmbedding rho iotaG := by
    rw [values, hchar]
    exact (Representation.brauerCharacterOfRootEmbedding_pullback_of_compatible
      V.ρ iotaH iotaG f (hcompat V)).symm
  let : IsSimpleModule k[H] (Representation.asModule V.ρ) :=
    (Representation.irreducible_iff_isSimpleModule_asModule V.ρ).mp hV
  let iG := irreducibleBrauerCharacterBlock iotaG injG DG phiG
  let iH := irreducibleBrauerCharacterBlock iotaH injH DH phiH
  have hsupp : rho.asAlgebraHom (eG iG) = 1 := by
    apply LinearMap.ext
    intro v
    change rho.asAlgebraHom (eG iG) v = v
    have hs := block_smul_of_affording iotaG injG DG phiG
      (FDRep.of rho) hrho hcharG (rho.asModuleEquiv.symm v)
    change eG iG • rho.asModuleEquiv.symm v = rho.asModuleEquiv.symm v at hs
    have heq := congrArg rho.asModuleEquiv hs
    simpa only [Representation.asModuleEquiv_map_smul,
      LinearEquiv.apply_symm_apply] using heq
  have hdownSupport : Representation.asAlgebraHom V.ρ (algebraMapOf f (eG iG)) = 1 := by
    rw [← algebra_action_map]
    exact hsupp
  let : Nontrivial (Representation.asModule V.ρ) :=
    IsSimpleModule.nontrivial k[H] (Representation.asModule V.ρ)
  let : Nontrivial V := (Representation.asModuleEquiv V.ρ).symm.toEquiv.nontrivial
  have hnonzero : algebraMapOf f (eG iG) ≠ 0 := by
    intro hz
    have bad : (0 : Module.End k V) = 1 := by
      simpa only [hz, map_zero] using hdownSupport
    exact zero_ne_one bad
  obtain ⟨j, hj⟩ := DH.primitiveBlockOfIndex_surjective
    ⟨algebraMapOf f (eG iG), S.primitive_image_of_ne_zero _ (DG.primitive iG) hnonzero⟩
  have hjval : eH j = algebraMapOf f (eG iG) := congrArg Subtype.val hj
  have hjmodule : j = DH.moduleBlock (V := Representation.asModule V.ρ) := by
    apply DH.moduleBlock_eq_of_smul_eq_self
    intro v
    apply (Representation.asModuleEquiv V.ρ).injective
    rw [Representation.asModuleEquiv_map_smul, hjval, hdownSupport]
    rfl
  have himodule : iH = DH.moduleBlock (V := Representation.asModule V.ρ) :=
    DH.moduleBlock_eq_of_smul_eq_self
      (block_smul_of_affording iotaH injH DH phiH V hV hchar)
  exact hjval.symm.trans (congrArg eH (hjmodule.trans himodule.symm))

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
