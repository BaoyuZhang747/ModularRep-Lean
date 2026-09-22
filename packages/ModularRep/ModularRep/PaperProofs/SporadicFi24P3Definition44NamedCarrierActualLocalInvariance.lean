import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualNormalizerBase
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnNormalizerInvariance
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorActualAmbient

/-! The actual local ambient fixes the transported normalizer character.
Both subgroup stability and character fixedness are derived from the
literal ambient action and the original equivariant weight match. -/

noncomputable section

set_option maxHeartbeats 2000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualLocalInvariance

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualNormalizerBase
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnNormalizerInvariance
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnNormalizerBrauer
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnCentralQuotient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientRoot
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorAutomorphismTransport
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorActualAmbient

universe u

section ActualAction

variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [Group G] [Finite G]
variable [CharP k p] [IsAlgClosed k] [CharZero K]
variable (iota : PrimeRegularRootEmbedding p k K G) (phi : IBr iota)

instance actualEmbeddedLocalBaseNormal (Q : Subgroup G) :
    (embeddedLocalBase (innerEmbedding iota phi) Q).Normal := by
  change ((actualBase iota phi).comap
    (embeddedNormalizer (innerEmbedding iota phi) Q).subtype).Normal
  infer_instance

theorem embedded_radical_stable
    (hcenter : Subgroup.center G = ⊥) (Q : Subgroup G)
    (d : embeddedNormalizer (innerEmbedding iota phi) Q) :
    Q.comap (actualConjugation iota phi d.1).toMonoidHom = Q := by
  have hsquare : (innerEmbedding iota phi).comp
      (actualConjugation iota phi d.1).toMonoidHom =
        (MulAut.conj d.1).toMonoidHom.comp (innerEmbedding iota phi) := by
    apply MonoidHom.ext
    intro x
    exact innerEmbedding_conjugation iota phi d.1 x
  have hmap : Q.map (actualConjugation iota phi d.1).toMonoidHom = Q := by
    apply Subgroup.map_injective (innerEmbedding_injective iota phi hcenter)
    rw [Subgroup.map_map, hsquare, ← Subgroup.map_map]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp d.2
  have h := congrArg (fun R : Subgroup G =>
    R.comap (actualConjugation iota phi d.1).toMonoidHom) hmap
  rw [Subgroup.comap_map_eq_self_of_injective
    (actualConjugation iota phi d.1).injective Q] at h
  exact h.symm

theorem actualConjugation_brauer_fixed (a : ActualAutAmbient iota phi) :
    MulOpposite.op (actualConjugation iota phi a) • phi = phi := by
  change MulOpposite.op (a.1.unop⁻¹) • phi = phi
  exact (a⁻¹).2

theorem normalizerBaseEquiv_conjugation
    (hcenter : Subgroup.center G = ⊥) (Q : Subgroup G)
    (d : embeddedNormalizer (innerEmbedding iota phi) Q)
    (n : Subgroup.normalizer (Q : Set G)) :
    normalizerBaseEquiv (innerEmbedding iota phi)
        (innerEmbedding_injective iota phi hcenter) Q
        (stableNormalizerAut Q (actualConjugation iota phi d.1)
          (embedded_radical_stable iota phi hcenter Q d) n) =
      MulAut.conjNormal d (normalizerBaseEquiv (innerEmbedding iota phi)
        (innerEmbedding_injective iota phi hcenter) Q n) := by
  apply Subtype.ext
  apply Subtype.ext
  change innerEmbedding iota phi
      (stableNormalizerAut Q (actualConjugation iota phi d.1)
        (embedded_radical_stable iota phi hcenter Q d) n : G) =
    d.1 * innerEmbedding iota phi n.1 * d.1⁻¹
  rw [stableNormalizerAut_coe]
  exact innerEmbedding_conjugation iota phi d.1 n.1

theorem normalizerBaseEquiv_congr_conjugation
    (hcenter : Subgroup.center G = ⊥) (Q : Subgroup G)
    (d : embeddedNormalizer (innerEmbedding iota phi) Q) :
    MulAut.congr (normalizerBaseEquiv (innerEmbedding iota phi)
        (innerEmbedding_injective iota phi hcenter) Q)
        (stableNormalizerAut Q (actualConjugation iota phi d.1)
          (embedded_radical_stable iota phi hcenter Q d)) = MulAut.conjNormal d := by
  let e := normalizerBaseEquiv (innerEmbedding iota phi)
    (innerEmbedding_injective iota phi hcenter) Q
  let betaN := stableNormalizerAut Q (actualConjugation iota phi d.1)
    (embedded_radical_stable iota phi hcenter Q d)
  change MulAut.congr e betaN = MulAut.conjNormal d
  apply MulEquiv.ext
  intro x
  obtain ⟨n, rfl⟩ := e.surjective x
  change e (betaN (e.symm (e n))) = MulAut.conjNormal d (e n)
  rw [e.symm_apply_apply]
  exact normalizerBaseEquiv_conjugation iota phi hcenter Q d n

end ActualAction

section Own

variable (P : Definition35Problem.{u}) (psi : Definition35Brauer P)
variable (V : CharacterWeight P.p P.K P.H)
variable (hprimeTo : ¬ P.p ∣ Nat.card (centralCharacterKernel P psi))

local instance problemPrime : Fact P.p.Prime := ⟨P.iota.prime⟩

variable (normalizers : NavarroTiep23cFixedCentralQuotientSource
  (centralCharacterKernel P psi)
  (show centralCharacterKernel P psi ≤ Subgroup.center P.H from inf_le_left)
  hprimeTo V.subgroup V.radical)
variable (source : CanonicalRawReduction P.iota V)
variable (compatibility : CanonicalLocalBlockCompatibility P.iota P.blockSource.operations)
variable (hrawBlock :
  letI := P.blockSource.operations.ambientBlockData.fintypeBlock
  P.blockSource.operations.rawWeightBlock V =
    irreducibleBrauerCharacterBlock P.iota P.irreducibleBrauerInjective
      P.blockSource.operations.ambientBlockData.blocks psi.1)
variable [Group.IsPerfect P.H]
variable (hZ0 : centralCharacterKernel P psi = Subgroup.center P.H)
variable (hcenter : ¬ P.p ∣ Nat.card (Subgroup.center P.H))
variable (E : MulAut P.H ≃* MulAut (CentralCharacterQuotient P psi))
variable (E_square : ∀ (alpha : MulAut P.H) (x : P.H),
  E alpha (centralCharacterQuotientMap P psi x) = centralCharacterQuotientMap P psi (alpha x))
variable (Omega : IBr P.iota ≃ ConjugacyClass (p := P.p) (K := P.K) (G := P.H))
variable (hOmega : ∀ (a : (MulAut P.H)ᵐᵒᵖ) (chi : IBr P.iota),
  Omega (a • chi) = a • Omega chi)
variable (hclass : (Quotient.mk'' (Quotient.mk'' V) :
  ConjugacyClass (p := P.p) (K := P.K) (G := P.H)) = Omega psi.1)

local notation "rG" => quotientRoot P.iota (centralCharacterKernel P psi)
local notation "phiG" => ownQuotientBrauer P psi
local notation "Qbar" => V.subgroup.map (centralCharacterQuotientMap P psi)
local notation "iG" => innerEmbedding rG phiG
local notation "hbarCenter" => ownQuotient_center_eq_bot P psi hZ0
local notation "eN" => normalizerBaseEquiv iG (innerEmbedding_injective rG phiG hbarCenter) Qbar
local notation "rN" => ownNormalizerRoot P psi V source hprimeTo normalizers
local notation "phiN" => ownNormalizerBrauer P psi V source compatibility hrawBlock hprimeTo normalizers

include hcenter E E_square Omega hOmega hclass in
theorem own_actualLocalBrauer_fixed (d : embeddedNormalizer iG Qbar) :
    IrreducibleBrauerCharacter.twist ((rN).alongMulEquiv eN)
        (IrreducibleBrauerCharacter.alongMulEquiv rN eN phiN) (MulAut.conjNormal d) =
      IrreducibleBrauerCharacter.alongMulEquiv rN eN phiN := by
  let beta := actualConjugation rG phiG d.1
  let alpha := E.symm beta
  have hQbar : (Qbar).comap beta.toMonoidHom = Qbar :=
    embedded_radical_stable rG phiG hbarCenter Qbar d
  have hbeta : MulOpposite.op beta • phiG = phiG := actualConjugation_brauer_fixed rG phiG d.1
  have hfixed : MulOpposite.op alpha • psi.1 = psi.1 := by
    apply (ownBrauer_fixed_iff P psi E E_square hcenter alpha).mpr
    simpa only [alpha, E.apply_symm_apply] using hbeta
  have hsquare : ∀ x, centralCharacterQuotientMap P psi (alpha x) =
      beta (centralCharacterQuotientMap P psi x) := by
    intro x
    simpa only [alpha, E.apply_symm_apply] using (E_square alpha x).symm
  let betaN := stableNormalizerAut Qbar beta hQbar
  have hdesc : (phiN).1.twist betaN = (phiN).1 :=
    ownNormalizerBrauer_fixed_of_quotient_match
      P psi V hprimeTo normalizers source compatibility hrawBlock
      Omega hOmega hclass alpha beta hsquare hfixed hQbar
  have hdescIBr : IrreducibleBrauerCharacter.twist rN phiN betaN = phiN := Subtype.ext hdesc
  have hconj : MulAut.congr eN betaN = MulAut.conjNormal d :=
    normalizerBaseEquiv_congr_conjugation rG phiG hbarCenter Qbar d
  have ht := IrreducibleBrauerCharacter.equivAlongMulEquiv_twist rN eN phiN betaN
  rw [hdescIBr, hconj] at ht
  exact ht.symm

end Own

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualLocalInvariance


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
