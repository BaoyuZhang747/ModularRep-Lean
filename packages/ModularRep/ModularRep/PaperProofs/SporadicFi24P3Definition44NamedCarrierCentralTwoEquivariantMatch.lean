import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralTwoExtensionAmbient

/-! Equivariance on the original common scalar sector gives the local
invariance, normalizer factorization and natural quotient identification.
The correspondence is not extended outside its given sector. -/

noncomputable section
set_option maxHeartbeats 2000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralTwoEquivariantMatch

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open EvenFieldFLZBAWGoodFamily
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierActualNormalizerBase
open SporadicFi24P3Definition44NamedCarrierActualLocalInvariance (actualConjugation_brauer_fixed)
open SporadicFi24P3Definition44NamedCarrierRadicalInnerCorrection
open SporadicFi24P3Definition44NamedCarrierCentralTwoExtensionAmbient
open SporadicFi24P3Definition44NamedCarrierOwnNormalizerInvariance
  (stableNormalizerAut stableNormalizerAut_coe inflated_ordinary_fixed_of_isomorphic)

universe u
variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G]
variable (iota : PrimeRegularRootEmbedding p k K G)

def ScalarBrauerSector (nu : Subgroup.center G →* kˣ) :=
  {chi : IBr iota // ∀ z : Subgroup.center G,
    (chosenIBrRepresentation iota chi).ρ z.1 = (nu z : k) • 1}

variable (nu : Subgroup.center G →* kˣ) (phi : ScalarBrauerSector iota nu)
variable (V : CharacterWeight p K G)
variable (Omega : ScalarBrauerSector iota nu → ConjugacyClass (p := p) (K := K) (G := G))
variable (hOmega : ∀ (a : (MulAut G)ᵐᵒᵖ) (chi chi' : ScalarBrauerSector iota nu),
  chi'.1 = a • chi.1 → Omega chi' = a • Omega chi)
variable (hclass : (Quotient.mk'' (Quotient.mk'' V) :
  ConjugacyClass (p := p) (K := K) (G := G)) = Omega phi)

include Omega hOmega hclass

theorem raw_isomorphic_of_equivariant_match
    (alpha : MulAut G) (hfixed : MulOpposite.op alpha • phi.1 = phi.1)
    (hQ : V.subgroup.comap alpha.toMonoidHom = V.subgroup) :
    CharacterWeight.Isomorphic (V.rightTwist alpha) V := by
  apply Quotient.exact (s := CharacterWeight.isomorphicSetoid)
  apply CyclicOuterRawPairNormalizer.isoClass_eq_of_conjugacyClass_eq_of_rawSubgroup_eq
  · change MulOpposite.op alpha • (Quotient.mk'' (Quotient.mk'' V) :
      ConjugacyClass (p := p) (K := K) (G := G)) = Quotient.mk'' (Quotient.mk'' V)
    rw [hclass]
    exact (hOmega (MulOpposite.op alpha) phi phi hfixed.symm).symm
  · exact hQ

theorem localBrauer_fixed_of_equivariant_match
    (source : CanonicalRawReduction iota V)
    (alpha : MulAut G) (hfixed : MulOpposite.op alpha • phi.1 = phi.1)
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
      inflated_ordinary_fixed_of_isomorphic V alpha
        (raw_isomorphic_of_equivariant_match iota nu phi V Omega hOmega hclass alpha hfixed hQ)
        n.1 (alphaN n.1) (stableNormalizerAut_coe V.subgroup alpha hQ n.1)
    _ = source.localBrauer.1 n := source.localBrauer_reduction n

omit Omega hOmega hclass

variable {T C : Type u} [Group T] [Group C] [Finite T]
variable (E : GroupExtension G T C)

local notation "A" => brauerAmbient E iota (Subtype.val phi)
local notation "i" => brauerEmbedding E iota (Subtype.val phi)
local notation "hi" => brauerEmbedding_injective E iota (Subtype.val phi)
local notation "act" => brauerAction E iota (Subtype.val phi)
local notation "B" => MonoidHom.range i
local notation "D" => embeddedNormalizer i V.subgroup
local notation "L" => embeddedLocalBase i V.subgroup
local notation "eG" => MonoidHom.ofInjective hi
local notation "eN" => normalizerBaseEquiv i hi V.subgroup
local notation "beta" => MonoidHom.comp (actualConjugation iota (Subtype.val phi)) act

instance localBaseNormal : (L).Normal := by
  change ((B).comap (D).subtype).Normal
  infer_instance

omit [Finite T] in
theorem action_inner (x : G) : beta (i x) = MulAut.conj x := by
  change actualConjugation iota phi.1 (act (i x)) = MulAut.conj x
  rw [brauerAction_conjugation]
  exact conjAct_inl E x

omit [Finite T] in
theorem embedded_radical_stable (d : D) :
    V.subgroup.comap (beta d.1).toMonoidHom = V.subgroup := by
  have hsquare : (i).comp (beta d.1).toMonoidHom =
      (MulAut.conj d.1).toMonoidHom.comp i := by
    apply MonoidHom.ext
    intro x
    exact brauerEmbedding_conjugation E iota phi.1 d.1 x
  have hmap : V.subgroup.map (beta d.1).toMonoidHom = V.subgroup := by
    apply Subgroup.map_injective hi
    rw [Subgroup.map_map, hsquare, ← Subgroup.map_map]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp d.2
  have h := congrArg (fun R : Subgroup G => R.comap (beta d.1).toMonoidHom) hmap
  rw [Subgroup.comap_map_eq_self_of_injective (beta d.1).injective V.subgroup] at h
  exact h.symm

omit [Finite T] in
theorem normalizer_conjugation (d : D) :
    MulAut.congr eN (stableNormalizerAut V.subgroup (beta d.1)
      (embedded_radical_stable iota nu phi V E d)) = MulAut.conjNormal d := by
  let emb : G →* A := i
  let e : Subgroup.normalizer (V.subgroup : Set G) ≃* L :=
    normalizerBaseEquiv emb hi V.subgroup
  let alpha : MulAut G := beta d.1
  let hQ : V.subgroup.comap alpha.toMonoidHom = V.subgroup :=
    embedded_radical_stable iota nu phi V E d
  let alphaN : MulAut (Subgroup.normalizer (V.subgroup : Set G)) :=
    stableNormalizerAut V.subgroup alpha hQ
  change MulAut.congr e alphaN = MulAut.conjNormal d
  have hpoint (n : Subgroup.normalizer (V.subgroup : Set G)) :
      e (alphaN n) = MulAut.conjNormal d (e n) := by
    apply Subtype.ext
    apply Subtype.ext
    calc
      ((e (alphaN n)).1 : A) = emb (alphaN n).1 :=
        normalizerBaseEquiv_ambient emb hi V.subgroup (alphaN n)
      _ = emb (alpha n.1) :=
        congrArg emb (stableNormalizerAut_coe V.subgroup alpha hQ n)
      _ = d.1 * emb n.1 * d.1⁻¹ :=
        brauerEmbedding_conjugation E iota phi.1 d.1 n.1
      _ = d.1 * ((e n).1 : A) * d.1⁻¹ :=
        congrArg (fun z : A => d.1 * z * d.1⁻¹)
          (normalizerBaseEquiv_ambient emb hi V.subgroup n).symm
  apply MulEquiv.ext
  intro x
  change e (alphaN (e.symm x)) = MulAut.conjNormal d x
  exact (hpoint (e.symm x)).trans
    (congrArg (fun y : L => MulAut.conjNormal d y) (e.apply_symm_apply x))

theorem globalBase_fixed (a : A) :
    IrreducibleBrauerCharacter.twist (iota.alongMulEquiv eG)
      (IrreducibleBrauerCharacter.alongMulEquiv iota eG phi.1) (MulAut.conjNormal a) =
        IrreducibleBrauerCharacter.alongMulEquiv iota eG phi.1 := by
  have he : MulAut.congr eG (beta a) = MulAut.conjNormal a := by
    apply MulEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := (eG).surjective y
    change eG (beta a ((eG).symm (eG x))) = MulAut.conjNormal a (eG x)
    rw [(eG).symm_apply_apply]
    apply Subtype.ext
    exact brauerEmbedding_conjugation E iota phi.1 a x
  have hf : IrreducibleBrauerCharacter.twist iota phi.1 (beta a) = phi.1 :=
    actualConjugation_brauer_fixed iota phi.1 (act a)
  have ht := IrreducibleBrauerCharacter.equivAlongMulEquiv_twist iota eG phi.1 (beta a)
  rw [hf, he] at ht
  exact ht.symm

include Omega hOmega hclass

theorem localBase_fixed (source : CanonicalRawReduction iota V) (d : D) :
    IrreducibleBrauerCharacter.twist (source.normalizerRoot.alongMulEquiv eN)
      (IrreducibleBrauerCharacter.alongMulEquiv source.normalizerRoot eN source.localBrauer)
      (MulAut.conjNormal d) =
        IrreducibleBrauerCharacter.alongMulEquiv source.normalizerRoot eN source.localBrauer := by
  let e : Subgroup.normalizer (V.subgroup : Set G) ≃* L := eN
  let r := source.normalizerRoot
  let chi : IBr r := source.localBrauer
  let alpha : MulAut G := beta d.1
  let hQ : V.subgroup.comap alpha.toMonoidHom = V.subgroup :=
    embedded_radical_stable iota nu phi V E d
  let alphaN : MulAut (Subgroup.normalizer (V.subgroup : Set G)) :=
    stableNormalizerAut V.subgroup alpha hQ
  change IrreducibleBrauerCharacter.twist (r.alongMulEquiv e)
      (IrreducibleBrauerCharacter.alongMulEquiv r e chi) (MulAut.conjNormal d) =
    IrreducibleBrauerCharacter.alongMulEquiv r e chi
  have hf : IrreducibleBrauerCharacter.twist r chi alphaN = chi :=
    localBrauer_fixed_of_equivariant_match iota nu phi V Omega hOmega hclass source
      alpha (actualConjugation_brauer_fixed iota phi.1 (act d.1)) hQ
  have hc : MulAut.congr e alphaN = MulAut.conjNormal d :=
    normalizer_conjugation iota nu phi V E d
  have ht : IrreducibleBrauerCharacter.alongMulEquiv r e
        (IrreducibleBrauerCharacter.twist r chi alphaN) =
      IrreducibleBrauerCharacter.twist (r.alongMulEquiv e)
        (IrreducibleBrauerCharacter.alongMulEquiv r e chi) (MulAut.congr e alphaN) :=
    IrreducibleBrauerCharacter.equivAlongMulEquiv_twist r e chi alphaN
  have hf' : IrreducibleBrauerCharacter.alongMulEquiv r e
        (IrreducibleBrauerCharacter.twist r chi alphaN) =
      IrreducibleBrauerCharacter.alongMulEquiv r e chi :=
    congrArg (IrreducibleBrauerCharacter.alongMulEquiv r e) hf
  exact (congrArg (fun a : MulAut L =>
      IrreducibleBrauerCharacter.twist (r.alongMulEquiv e)
        (IrreducibleBrauerCharacter.alongMulEquiv r e chi) a) hc.symm).trans
    (ht.symm.trans hf')

omit Omega hOmega hclass [Finite T] in
theorem mem_normalizer_of_stable (a : A)
    (hQ : V.subgroup.comap (beta a).toMonoidHom = V.subgroup) : a ∈ D := by
  have hmap : V.subgroup.map (beta a).toMonoidHom = V.subgroup := by
    have h := congrArg (fun R : Subgroup G => R.map (beta a).toMonoidHom) hQ
    rw [Subgroup.map_comap_eq_self_of_surjective (beta a).surjective V.subgroup] at h
    exact h.symm
  have hsquare : (i).comp (beta a).toMonoidHom = (MulAut.conj a).toMonoidHom.comp i := by
    apply MonoidHom.ext
    intro x
    exact brauerEmbedding_conjugation E iota phi.1 a x
  change a ∈ Subgroup.normalizer (V.subgroup.map i : Set _)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_map]
  change V.subgroup.map ((MulAut.conj a).toMonoidHom.comp i) = V.subgroup.map i
  rw [← hsquare, ← Subgroup.map_map, hmap]

omit [Finite T] in
theorem matchedAmbient_factorization (a : A) : ∃ d : D, ∃ x : G, a = d.1 * i x := by
  let w : ConjugacyClass (p := p) (K := K) (G := G) := Quotient.mk'' (Quotient.mk'' V)
  let Q : RadicalSubgroup (p := p) (G := G) := ⟨V.subgroup, V.radical⟩
  have hphi : MulOpposite.op (beta a) • phi.1 = phi.1 :=
    actualConjugation_brauer_fixed iota phi.1 (act a)
  have hw : MulOpposite.op (beta a) • w = w := by
    change MulOpposite.op (beta a) • (Quotient.mk'' (Quotient.mk'' V) :
      ConjugacyClass (p := p) (K := K) (G := G)) = Quotient.mk'' (Quotient.mk'' V)
    rw [hclass]
    exact (hOmega (MulOpposite.op (beta a)) phi phi hphi.symm).symm
  have hQclass : MulOpposite.op (beta a) •
      (Quotient.mk'' Q : RadicalConjugacyClass (p := p) (G := G)) = Quotient.mk'' Q :=
    (radicalClass_equivariant (MulOpposite.op (beta a)) w).symm.trans (congrArg radicalClass hw)
  obtain ⟨g, hg⟩ := exists_innerCorrection_of_fixed_radicalClass Q (beta a) hQclass
  let d : A := a * i g
  have hd : d ∈ D := by
    apply mem_normalizer_of_stable iota nu phi V E d
    have hdaut : beta d = beta a * MulAut.conj g := by
      change beta (a * i g) = beta a * MulAut.conj g
      rw [map_mul, action_inner]
    rw [hdaut]
    exact hg
  refine ⟨⟨d, hd⟩, g⁻¹, ?_⟩
  change a = (a * i g) * i g⁻¹
  simp only [map_inv, mul_assoc, mul_inv_cancel, mul_one]

def matchedLocalProjection : D →* (A ⧸ B) := (QuotientGroup.mk' B).comp (D).subtype

omit Omega hOmega hclass [Finite T] in
theorem matchedLocalProjection_ker : (matchedLocalProjection iota nu phi V E).ker = L := by
  change ((QuotientGroup.mk' B).comp (D).subtype).ker = (B).comap (D).subtype
  rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']

omit [Finite T] in
theorem matchedLocalProjection_surjective :
    Function.Surjective (matchedLocalProjection iota nu phi V E) := by
  intro z
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective B z
  obtain ⟨d, g, ha⟩ := matchedAmbient_factorization iota nu phi V Omega hOmega hclass E a
  refine ⟨d, ?_⟩
  change QuotientGroup.mk' B d.1 = QuotientGroup.mk' B a
  rw [ha, map_mul]
  have hq : QuotientGroup.mk' B (i g) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩
  rw [hq, mul_one]

def matchedLocalQuotientEquiv : D ⧸ L ≃* A ⧸ B :=
  QuotientGroup.liftEquiv L
    (matchedLocalProjection_surjective iota nu phi V Omega hOmega hclass E)
    (matchedLocalProjection_ker iota nu phi V E).symm

omit [Finite T] in
theorem matchedLocalQuotientEquiv_mk (d : D) :
    matchedLocalQuotientEquiv iota nu phi V Omega hOmega hclass E
      (QuotientGroup.mk' L d) = QuotientGroup.mk' B d.1 := rfl

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralTwoEquivariantMatch


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
