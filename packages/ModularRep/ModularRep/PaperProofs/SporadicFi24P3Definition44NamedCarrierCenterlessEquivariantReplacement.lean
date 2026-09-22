import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualLocalInvariance
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRadicalInnerCorrection
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorBaseInvariance
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAssociatedProjectiveModel
import ModularRep.BrauerCharacterExtensionBridge

/-! The centreless case of the manuscript's equivariant-replacement argument.
Every construction retains the original Brauer character and the ordinary
character of its matched raw weight. Navarro 8.12 is the explicit extension
input; the natural quotient identification and equality of factor classes
are deductions, without a block census or selected outer involution. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessEquivariantReplacement

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierActualNormalizerBase
open SporadicFi24P3Definition44NamedCarrierActualLocalInvariance
open SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
open SporadicFi24P3Definition44NamedCarrierRadicalInnerCorrection
open SporadicFi24P3Definition44NamedCarrierTrivialSectorBaseInvariance
open SporadicFi24P3Definition44NamedCarrierAssociatedProjectiveModel
open SporadicFi24P3Definition44NamedCarrierOwnNormalizerInvariance
  (stableNormalizerAut stableNormalizerAut_coe inflated_ordinary_fixed_of_isomorphic)

universe u

variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G]
variable (iota : PrimeRegularRootEmbedding p k K G) (phi : IBr iota)
variable (V : CharacterWeight p K G)
variable (Omega : IBr iota → ConjugacyClass (p := p) (K := K) (G := G))
variable (hOmega : ∀ (a : (MulAut G)ᵐᵒᵖ) (chi : IBr iota),
  Omega (a • chi) = a • Omega chi)
variable (hclass : (Quotient.mk'' (Quotient.mk'' V) :
  ConjugacyClass (p := p) (K := K) (G := G)) = Omega phi)

include Omega hOmega hclass

theorem raw_isomorphic_of_equivariant_match
    (alpha : MulAut G) (hfixed : MulOpposite.op alpha • phi = phi)
    (hQ : V.subgroup.comap alpha.toMonoidHom = V.subgroup) :
    CharacterWeight.Isomorphic (V.rightTwist alpha) V := by
  apply Quotient.exact (s := CharacterWeight.isomorphicSetoid)
  apply CyclicOuterRawPairNormalizer.isoClass_eq_of_conjugacyClass_eq_of_rawSubgroup_eq
  · change MulOpposite.op alpha • (Quotient.mk'' (Quotient.mk'' V) :
      ConjugacyClass (p := p) (K := K) (G := G)) = Quotient.mk'' (Quotient.mk'' V)
    rw [hclass, ← hOmega, hfixed]
  · exact hQ

theorem inflated_ordinary_fixed_of_equivariant_match
    (alpha : MulAut G) (hfixed : MulOpposite.op alpha • phi = phi)
    (hQ : V.subgroup.comap alpha.toMonoidHom = V.subgroup)
    (n : Subgroup.normalizer (V.subgroup : Set G)) :
    V.localCharacter (QuotientGroup.mk (stableNormalizerAut V.subgroup alpha hQ n)) =
      V.localCharacter (QuotientGroup.mk n) := by
  exact inflated_ordinary_fixed_of_isomorphic V alpha
    (raw_isomorphic_of_equivariant_match iota phi V Omega hOmega hclass alpha hfixed hQ)
    n (stableNormalizerAut V.subgroup alpha hQ n)
    (stableNormalizerAut_coe V.subgroup alpha hQ n)

theorem localBrauer_fixed_of_equivariant_match
    (source : CanonicalRawReduction iota V)
    (alpha : MulAut G) (hfixed : MulOpposite.op alpha • phi = phi)
    (hQ : V.subgroup.comap alpha.toMonoidHom = V.subgroup) :
    IrreducibleBrauerCharacter.twist source.normalizerRoot source.localBrauer
        (stableNormalizerAut V.subgroup alpha hQ) = source.localBrauer := by
  let alphaN := stableNormalizerAut V.subgroup alpha hQ
  apply Subtype.ext
  ext n
  change source.localBrauer.1 (PrimeRegularElement.map alphaN.toMonoidHom n) =
    source.localBrauer.1 n
  calc
    source.localBrauer.1 (PrimeRegularElement.map alphaN.toMonoidHom n) =
        V.localCharacter (QuotientGroup.mk (alphaN n.1)) :=
      (source.localBrauer_reduction _).symm
    _ = V.localCharacter (QuotientGroup.mk n.1) :=
      inflated_ordinary_fixed_of_equivariant_match
        iota phi V Omega hOmega hclass alpha hfixed hQ n.1
    _ = source.localBrauer.1 n := source.localBrauer_reduction n

theorem actualLocalBrauer_fixed_of_equivariant_match
    (source : CanonicalRawReduction iota V) (hcenter : Subgroup.center G = ⊥)
    (d : embeddedNormalizer (innerEmbedding iota phi) V.subgroup) :
    let eN := normalizerBaseEquiv (innerEmbedding iota phi)
      (innerEmbedding_injective iota phi hcenter) V.subgroup
    IrreducibleBrauerCharacter.twist (source.normalizerRoot.alongMulEquiv eN)
        (IrreducibleBrauerCharacter.alongMulEquiv source.normalizerRoot eN source.localBrauer)
        (MulAut.conjNormal d) =
      IrreducibleBrauerCharacter.alongMulEquiv source.normalizerRoot eN source.localBrauer := by
  let alpha := actualConjugation iota phi d.1
  let hQ := embedded_radical_stable iota phi hcenter V.subgroup d
  let alphaN := stableNormalizerAut V.subgroup alpha hQ
  let eN := normalizerBaseEquiv (innerEmbedding iota phi)
    (innerEmbedding_injective iota phi hcenter) V.subgroup
  change IrreducibleBrauerCharacter.twist (source.normalizerRoot.alongMulEquiv eN)
      (IrreducibleBrauerCharacter.alongMulEquiv source.normalizerRoot eN source.localBrauer)
      (MulAut.conjNormal d) =
    IrreducibleBrauerCharacter.alongMulEquiv source.normalizerRoot eN source.localBrauer
  have hlocal : IrreducibleBrauerCharacter.twist source.normalizerRoot source.localBrauer
      alphaN = source.localBrauer :=
    localBrauer_fixed_of_equivariant_match iota phi V Omega hOmega hclass source alpha
      (actualConjugation_brauer_fixed iota phi d.1) hQ
  have hconj : MulAut.congr eN alphaN = MulAut.conjNormal d :=
    normalizerBaseEquiv_congr_conjugation iota phi hcenter V.subgroup d
  have ht := IrreducibleBrauerCharacter.equivAlongMulEquiv_twist
    source.normalizerRoot eN source.localBrauer alphaN
  rw [hlocal, hconj] at ht
  exact ht.symm

omit Omega hOmega hclass in
theorem mem_embeddedNormalizer_of_actualConjugation_stable
    (Q : Subgroup G) (a : ActualAutAmbient iota phi)
    (hQ : Q.comap (actualConjugation iota phi a).toMonoidHom = Q) :
    a ∈ embeddedNormalizer (innerEmbedding iota phi) Q := by
  let beta := actualConjugation iota phi a
  have hmap : Q.map beta.toMonoidHom = Q := by
    have h := congrArg (fun R : Subgroup G => R.map beta.toMonoidHom) hQ
    rw [Subgroup.map_comap_eq_self_of_surjective beta.surjective Q] at h
    exact h.symm
  have hsquare : (innerEmbedding iota phi).comp beta.toMonoidHom =
      (MulAut.conj a).toMonoidHom.comp (innerEmbedding iota phi) := by
    apply MonoidHom.ext
    intro x
    exact innerEmbedding_conjugation iota phi a x
  change a ∈ Subgroup.normalizer (Q.map (innerEmbedding iota phi) : Set _)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  rw [Subgroup.map_map]
  change Q.map ((MulAut.conj a).toMonoidHom.comp (innerEmbedding iota phi)) =
    Q.map (innerEmbedding iota phi)
  rw [← hsquare, ← Subgroup.map_map, hmap]

theorem matchedAmbient_factorization (a : ActualAutAmbient iota phi) :
    ∃ d : embeddedNormalizer (innerEmbedding iota phi) V.subgroup,
      ∃ x : G, a = d.1 * innerEmbedding iota phi x := by
  let beta := actualConjugation iota phi a
  let w : ConjugacyClass (p := p) (K := K) (G := G) :=
    Quotient.mk'' (Quotient.mk'' V)
  let Q : RadicalSubgroup (p := p) (G := G) := ⟨V.subgroup, V.radical⟩
  have hphi : MulOpposite.op beta • phi = phi := actualConjugation_brauer_fixed iota phi a
  have hw : MulOpposite.op beta • w = w := by
    change MulOpposite.op beta •
      (Quotient.mk'' (Quotient.mk'' V) : ConjugacyClass (p := p) (K := K) (G := G)) =
      Quotient.mk'' (Quotient.mk'' V)
    rw [hclass, ← hOmega, hphi]
  have hQclass : MulOpposite.op beta •
      (Quotient.mk'' Q : RadicalConjugacyClass (p := p) (G := G)) = Quotient.mk'' Q :=
    (radicalClass_equivariant (MulOpposite.op beta) w).symm.trans (congrArg radicalClass hw)
  obtain ⟨g, hg⟩ := exists_innerCorrection_of_fixed_radicalClass Q beta hQclass
  let d : ActualAutAmbient iota phi := a * innerEmbedding iota phi g
  have hd : d ∈ embeddedNormalizer (innerEmbedding iota phi) V.subgroup := by
    apply mem_embeddedNormalizer_of_actualConjugation_stable iota phi V.subgroup d
    have hdaut : actualConjugation iota phi d = beta * MulAut.conj g := by
      change actualConjugation iota phi (a * innerEmbedding iota phi g) =
        actualConjugation iota phi a * MulAut.conj g
      rw [map_mul, actualConjugation_inner]
    rw [hdaut]
    exact hg
  refine ⟨⟨d, hd⟩, g⁻¹, ?_⟩
  change a = (a * innerEmbedding iota phi g) * innerEmbedding iota phi g⁻¹
  simp only [map_inv, mul_assoc, mul_inv_cancel, mul_one]

def matchedLocalProjection :
    embeddedNormalizer (innerEmbedding iota phi) V.subgroup →*
      (ActualAutAmbient iota phi ⧸ actualBase iota phi) :=
  (QuotientGroup.mk' (actualBase iota phi)).comp
    (embeddedNormalizer (innerEmbedding iota phi) V.subgroup).subtype

omit Omega hOmega hclass in
theorem matchedLocalProjection_ker :
    (matchedLocalProjection iota phi V).ker =
      embeddedLocalBase (innerEmbedding iota phi) V.subgroup := by
  change ((QuotientGroup.mk' (actualBase iota phi)).comp
      (embeddedNormalizer (innerEmbedding iota phi) V.subgroup).subtype).ker =
    (actualBase iota phi).comap
      (embeddedNormalizer (innerEmbedding iota phi) V.subgroup).subtype
  rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']

theorem matchedLocalProjection_surjective :
    Function.Surjective (matchedLocalProjection iota phi V) := by
  intro z
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (actualBase iota phi) z
  obtain ⟨d, g, ha⟩ := matchedAmbient_factorization iota phi V Omega hOmega hclass a
  refine ⟨d, ?_⟩
  change QuotientGroup.mk' (actualBase iota phi) d.1 =
    QuotientGroup.mk' (actualBase iota phi) a
  rw [ha, map_mul]
  have hi : QuotientGroup.mk' (actualBase iota phi) (innerEmbedding iota phi g) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩
  rw [hi, mul_one]

def matchedLocalQuotientEquiv :
    embeddedNormalizer (innerEmbedding iota phi) V.subgroup ⧸
        embeddedLocalBase (innerEmbedding iota phi) V.subgroup ≃*
      ActualAutAmbient iota phi ⧸ actualBase iota phi :=
  QuotientGroup.liftEquiv (embeddedLocalBase (innerEmbedding iota phi) V.subgroup)
    (matchedLocalProjection_surjective iota phi V Omega hOmega hclass)
    (matchedLocalProjection_ker iota phi V).symm

theorem matchedLocalQuotientEquiv_mk
    (d : embeddedNormalizer (innerEmbedding iota phi) V.subgroup) :
    matchedLocalQuotientEquiv iota phi V Omega hOmega hclass
      (QuotientGroup.mk' (embeddedLocalBase (innerEmbedding iota phi) V.subgroup) d) =
      QuotientGroup.mk' (actualBase iota phi) d.1 := rfl

variable (source : CanonicalRawReduction iota V)
variable (hcenter : Subgroup.center G = ⊥)

local notation "A" => ActualAutAmbient iota phi
local notation "B" => actualBase iota phi
local notation "D" => embeddedNormalizer (innerEmbedding iota phi) V.subgroup
local notation "L" => embeddedLocalBase (innerEmbedding iota phi) V.subgroup
local notation "eG" => actualBaseEquiv iota phi hcenter
local notation "eN" => normalizerBaseEquiv (innerEmbedding iota phi)
  (innerEmbedding_injective iota phi hcenter) V.subgroup
local notation "rG" => iota.alongMulEquiv eG
local notation "phiG" => IrreducibleBrauerCharacter.alongMulEquiv iota eG phi
local notation "rL" => source.normalizerRoot.alongMulEquiv eN
local notation "phiL" => IrreducibleBrauerCharacter.alongMulEquiv
  source.normalizerRoot eN source.localBrauer
local notation "qE" => matchedLocalQuotientEquiv iota phi V Omega hOmega hclass

/-- The centreless, outer-order-two deduction in `lem:equivariant-replacement`.
For every matched pair of the arbitrary supplied equivariant map, the two
actual characters have associated models with the same trivial factor class
under the natural quotient identification. The final coboundary is constant one.
Navarro 8.15 identifies these character-dependent classes independently of the
choice of associated operators. -/
theorem centerless_equivariant_replacement
    (hOuter : Nat.card (LiteralOuterQuotient G) = 2)
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} p k) :
    Subgroup.centralizer (B : Set A) = ⊥ ∧
    ∃ (WG : FDRep k B) (WL : FDRep k L)
      (MG : AssociatedProjectiveModel B WG.ρ)
      (ML : AssociatedProjectiveModel L WL.ρ),
      Representation.IsIrreducible WG.ρ ∧
      phiG.1 = Representation.brauerCharacterOfRootEmbedding WG.ρ rG ∧
      Representation.IsIrreducible WL.ρ ∧
      phiL.1 = Representation.brauerCharacterOfRootEmbedding WL.ρ rL ∧
      MG.factorSet = ScalarFactorSet.trivial ∧
      ML.factorSet = ScalarFactorSet.trivial ∧
      (∀ d : D, qE (QuotientGroup.mk' L d) = QuotientGroup.mk' B d.1) ∧
      ML.factorSet = ScalarFactorSet.pullback qE MG.factorSet ∧
      ScalarFactorSet.Cohomologous ML.factorSet
        (ScalarFactorSet.pullback qE MG.factorSet) := by
  refine ⟨actualBase_centralizer_eq_bot iota phi hcenter, ?_⟩
  have hcyclicG : IsCyclic (A ⧸ B) := actual_quotient_isCyclic iota phi hOuter
  have hcyclicL : IsCyclic (D ⧸ L) := by
    let : IsCyclic (A ⧸ B) := hcyclicG
    exact isCyclic_of_injective (qE).toMonoidHom (qE).injective
  obtain ⟨WG, hWG, hcharG, ⟨EG⟩⟩ :=
    Representation.exists_extension_realisation_of_ibr_fixed_cyclic_quotient
      principle rG phiG hcyclicG (actualGlobalBaseFixed iota phi hcenter)
  obtain ⟨WL, hWL, hcharL, ⟨EL⟩⟩ :=
    Representation.exists_extension_realisation_of_ibr_fixed_cyclic_quotient
      principle rL phiL hcyclicL
      (actualLocalBrauer_fixed_of_equivariant_match
        iota phi V Omega hOmega hclass source hcenter)
  refine ⟨WG, WL, AssociatedProjectiveModel.ofExtension EG,
    AssociatedProjectiveModel.ofExtension EL,
    hWG, hcharG, hWL, hcharL, rfl, rfl, ?_, rfl, ?_⟩
  · exact matchedLocalQuotientEquiv_mk iota phi V Omega hOmega hclass
  · exact ScalarFactorSet.trivial_cohomologous_pullback_trivial qE

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessEquivariantReplacement


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
