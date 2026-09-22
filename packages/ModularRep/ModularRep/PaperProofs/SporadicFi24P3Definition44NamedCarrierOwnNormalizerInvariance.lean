import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnQuotientGroupFacts
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorAutomorphismTransport
import ModularRep.PaperProofs.CyclicOuterRawPairNormalizer
import ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalAction

/-! Local invariance is derived from the original equivariant match.
Normalizer saturation and radicality recover the original support, raw
weight uniqueness gives ordinary invariance, and canonical pullback gives
invariance of the actual descended normalizer Brauer character. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnNormalizerInvariance

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.IrreducibleBrauerCharacterSurjectiveDescent
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalAction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnNormalizerBrauer
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnQuotientGroupFacts
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorAutomorphismTransport

universe u

theorem radical_stable_of_normalizer_stable
    {p : ℕ} {G : Type*} [Group G]
    (Q : Subgroup G) (hQ : IsRadicalSubgroup p Q) (alpha : MulAut G)
    (hN : (Subgroup.normalizer (Q : Set G)).comap alpha.toMonoidHom =
      Subgroup.normalizer (Q : Set G)) : Q.comap alpha.toMonoidHom = Q := by
  have hn : Subgroup.normalizer (Q.comap alpha.toMonoidHom : Set G) =
      Subgroup.normalizer (Q : Set G) :=
    (Subgroup.comap_normalizer_eq_of_surjective Q alpha.surjective).symm.trans hN
  calc
    Q.comap alpha.toMonoidHom = normalizerPCore p (Q.comap alpha.toMonoidHom) :=
      hQ.comap_mulAut alpha
    _ = normalizerPCore p Q := by unfold normalizerPCore; rw [hn]
    _ = Q := hQ.symm

private theorem normalizerCast_coe {G : Type u} [Group G]
    {Q R : Subgroup G} (h : Q = R)
    (n : Subgroup.normalizer (Q : Set G)) :
    (CyclicOuterLemma37LiteralLocalAction.castNormalizer h n : G) = n := by
  subst R
  rfl

def stableNormalizerAut {G : Type u} [Group G]
    (Q : Subgroup G) (alpha : MulAut G) (hQ : Q.comap alpha.toMonoidHom = Q) :
    MulAut (Subgroup.normalizer (Q : Set G)) :=
  (CyclicOuterLemma37LiteralLocalAction.castNormalizer hQ.symm).trans
    (rightNormalizerEquiv alpha Q)

theorem stableNormalizerAut_coe {G : Type u} [Group G]
    (Q : Subgroup G) (alpha : MulAut G) (hQ : Q.comap alpha.toMonoidHom = Q)
    (n : Subgroup.normalizer (Q : Set G)) :
    (stableNormalizerAut Q alpha hQ n : G) = alpha n.1 := by
  exact congrArg alpha
    (normalizerCast_coe hQ.symm n)

theorem inflated_ordinary_fixed_of_isomorphic
    {p : ℕ} {K G : Type u} [Field K] [CharZero K] [Group G] [Fintype G]
    (V : CharacterWeight p K G) (alpha : MulAut G)
    (hIso : CharacterWeight.Isomorphic (V.rightTwist alpha) V)
    (x y : Subgroup.normalizer (V.subgroup : Set G)) (hxy : (y : G) = alpha (x : G)) :
    V.localCharacter (QuotientGroup.mk y) = V.localCharacter (QuotientGroup.mk x) := by
  have hv := localCharacter_fixed_of_rightTwist_isomorphic V alpha hIso (QuotientGroup.mk x)
  dsimp only at hv
  have heq : rightNormalizerEquiv alpha V.subgroup
      (CyclicOuterLemma37LiteralLocalAction.castNormalizer hIso.choose.symm x) = y := by
    apply Subtype.ext
    exact (congrArg alpha
      (normalizerCast_coe hIso.choose.symm x)).trans hxy.symm
  have harg : rightNormalizerQuotientEquiv alpha V.subgroup
      ((MulEquiv.cast (M := fun R : Subgroup G => NormalizerQuotient R)
        hIso.choose).symm (QuotientGroup.mk x)) = QuotientGroup.mk y := by
    calc
      _ = rightNormalizerQuotientEquiv alpha V.subgroup
          (QuotientGroup.mk (CyclicOuterLemma37LiteralLocalAction.castNormalizer
            hIso.choose.symm x)) :=
        congrArg (rightNormalizerQuotientEquiv alpha V.subgroup)
          (quotientCast_symm_mk hIso.choose x)
      _ = QuotientGroup.mk (rightNormalizerEquiv alpha V.subgroup
          (CyclicOuterLemma37LiteralLocalAction.castNormalizer hIso.choose.symm x)) :=
        rightNormalizerQuotientEquiv_mk _ _ _
      _ = QuotientGroup.mk y := congrArg QuotientGroup.mk heq
  exact (congrArg V.localCharacter harg).symm.trans hv

theorem raw_isomorphic_of_equivariant_match
    (P : Definition35Problem.{u}) (psi : Definition35Brauer P)
    (V : CharacterWeight P.p P.K P.H)
    (Omega : IBr P.iota ≃ ConjugacyClass (p := P.p) (K := P.K) (G := P.H))
    (hOmega : ∀ (a : (MulAut P.H)ᵐᵒᵖ) (chi : IBr P.iota),
      Omega (a • chi) = a • Omega chi)
    (hclass : (Quotient.mk'' (Quotient.mk'' V) :
      ConjugacyClass (p := P.p) (K := P.K) (G := P.H)) = Omega psi.1)
    (alpha : MulAut P.H) (hfixed : MulOpposite.op alpha • psi.1 = psi.1)
    (hQ : V.subgroup.comap alpha.toMonoidHom = V.subgroup) :
    CharacterWeight.Isomorphic (V.rightTwist alpha) V := by
  apply Quotient.exact (s := CharacterWeight.isomorphicSetoid)
  apply CyclicOuterRawPairNormalizer.isoClass_eq_of_conjugacyClass_eq_of_rawSubgroup_eq
  · change MulOpposite.op alpha • (Quotient.mk'' (Quotient.mk'' V) :
      ConjugacyClass (p := P.p) (K := P.K) (G := P.H)) = Quotient.mk'' (Quotient.mk'' V)
    rw [hclass, ← hOmega, hfixed]
  · exact hQ

variable (P : Definition35Problem.{u}) (psi : Definition35Brauer P)
variable (V : CharacterWeight P.p P.K P.H)
variable (hprimeTo : ¬ P.p ∣ Nat.card (centralCharacterKernel P psi))

local instance problemPrime : Fact P.p.Prime := ⟨P.iota.prime⟩

variable (normalizers : NavarroTiep23cFixedCentralQuotientSource
  (centralCharacterKernel P psi) (show centralCharacterKernel P psi ≤ Subgroup.center P.H from inf_le_left)
  hprimeTo V.subgroup V.radical)

include hprimeTo normalizers in
theorem own_radical_stable_of_quotient_stable
    (alpha : MulAut P.H) (beta : MulAut (CentralCharacterQuotient P psi))
    (hsquare : ∀ x, centralCharacterQuotientMap P psi (alpha x) =
      beta (centralCharacterQuotientMap P psi x))
    (hQbar : (V.subgroup.map (centralCharacterQuotientMap P psi)).comap beta.toMonoidHom =
      V.subgroup.map (centralCharacterQuotientMap P psi)) :
    V.subgroup.comap alpha.toMonoidHom = V.subgroup := by
  let Qbar := V.subgroup.map (centralCharacterQuotientMap P psi)
  have hNbar : (Subgroup.normalizer (Qbar : Set (CentralCharacterQuotient P psi))).comap
      beta.toMonoidHom = Subgroup.normalizer (Qbar : Set (CentralCharacterQuotient P psi)) := by
    rw [Subgroup.comap_normalizer_eq_of_surjective Qbar beta.surjective, hQbar]
  apply radical_stable_of_normalizer_stable V.subgroup V.radical alpha
  ext x
  change alpha x ∈ Subgroup.normalizer (V.subgroup : Set P.H) ↔
    x ∈ Subgroup.normalizer (V.subgroup : Set P.H)
  rw [own_normalizer_saturated P psi V hprimeTo normalizers (alpha x),
    own_normalizer_saturated P psi V hprimeTo normalizers x, hsquare x]
  change centralCharacterQuotientMap P psi x ∈
    (Subgroup.normalizer (Qbar : Set (CentralCharacterQuotient P psi))).comap beta.toMonoidHom ↔ _
  rw [hNbar]

theorem ownNormalizerBrauer_fixed_of_quotient_match
    (source : CanonicalRawReduction P.iota V)
    (compatibility : CanonicalLocalBlockCompatibility P.iota P.blockSource.operations)
    (hrawBlock :
      letI := P.blockSource.operations.ambientBlockData.fintypeBlock
      P.blockSource.operations.rawWeightBlock V =
        irreducibleBrauerCharacterBlock P.iota P.irreducibleBrauerInjective
          P.blockSource.operations.ambientBlockData.blocks psi.1)
    (Omega : IBr P.iota ≃ ConjugacyClass (p := P.p) (K := P.K) (G := P.H))
    (hOmega : ∀ (a : (MulAut P.H)ᵐᵒᵖ) (chi : IBr P.iota),
      Omega (a • chi) = a • Omega chi)
    (hclass : (Quotient.mk'' (Quotient.mk'' V) :
      ConjugacyClass (p := P.p) (K := P.K) (G := P.H)) = Omega psi.1)
    (alpha : MulAut P.H) (beta : MulAut (CentralCharacterQuotient P psi))
    (hsquare : ∀ x, centralCharacterQuotientMap P psi (alpha x) =
      beta (centralCharacterQuotientMap P psi x))
    (hfixed : MulOpposite.op alpha • psi.1 = psi.1)
    (hQbar : (V.subgroup.map (centralCharacterQuotientMap P psi)).comap beta.toMonoidHom =
      V.subgroup.map (centralCharacterQuotientMap P psi)) :
    (ownNormalizerBrauer P psi V source compatibility hrawBlock hprimeTo normalizers).1.twist
        (stableNormalizerAut (V.subgroup.map (centralCharacterQuotientMap P psi)) beta hQbar) =
      (ownNormalizerBrauer P psi V source compatibility hrawBlock hprimeTo normalizers).1 := by
  have hQ := own_radical_stable_of_quotient_stable P psi V hprimeTo normalizers alpha beta hsquare hQbar
  have hIso := raw_isomorphic_of_equivariant_match P psi V Omega hOmega hclass alpha hfixed hQ
  let alphaN := stableNormalizerAut V.subgroup alpha hQ
  let betaN := stableNormalizerAut (V.subgroup.map (centralCharacterQuotientMap P psi)) beta hQbar
  have hlocal : source.localBrauer.1.twist alphaN = source.localBrauer.1 := by
    ext n
    change source.localBrauer.1 (PrimeRegularElement.map alphaN.toMonoidHom n) = source.localBrauer.1 n
    calc
      source.localBrauer.1 (PrimeRegularElement.map alphaN.toMonoidHom n) =
          V.localCharacter (QuotientGroup.mk (alphaN n.1)) := (source.localBrauer_reduction _).symm
      _ = V.localCharacter (QuotientGroup.mk n.1) :=
        inflated_ordinary_fixed_of_isomorphic V alpha hIso n.1 (alphaN n.1)
          (stableNormalizerAut_coe V.subgroup alpha hQ n.1)
      _ = source.localBrauer.1 n := source.localBrauer_reduction n
  have hNormalizerSquare : ∀ n, ownNormalizerMap P psi V (alphaN n) =
      betaN (ownNormalizerMap P psi V n) := by
    intro n
    apply Subtype.ext
    change centralCharacterQuotientMap P psi (alphaN n : P.H) =
      (betaN (ownNormalizerMap P psi V n) : CentralCharacterQuotient P psi)
    rw [stableNormalizerAut_coe, stableNormalizerAut_coe]
    exact hsquare n.1
  have hcoprime : (Nat.card (ownNormalizerMap P psi V).ker).Coprime P.p := by
    rw [own_normalizer_ker_card P psi V]
    exact (P.iota.prime.coprime_iff_not_dvd.mpr hprimeTo).symm
  apply primeRegularClassFunction_pullback_injective_of_ker_card_coprime
    (ownNormalizerMap P psi V) (ownNormalizerMap_surjective P psi V hprimeTo normalizers) hcoprime
  have hinflate := ownNormalizerBrauer_pullback P psi V source compatibility hrawBlock
    hprimeTo normalizers
  exact (pullback_twist_of_square (ownNormalizerMap P psi V) alphaN betaN hNormalizerSquare
    (ownNormalizerBrauer P psi V source compatibility hrawBlock hprimeTo normalizers).1).trans
      ((congrArg (fun chi : PrimeRegularClassFunction P.K
        (Subgroup.normalizer (V.subgroup : Set P.H)) P.p => chi.twist alphaN) hinflate).trans
        (hlocal.trans hinflate.symm))

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnNormalizerInvariance


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
