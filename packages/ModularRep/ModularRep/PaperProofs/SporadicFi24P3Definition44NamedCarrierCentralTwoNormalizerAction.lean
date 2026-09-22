import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryInertia
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSmallCenterFamilyComparison

/-! The original extension's normalizer action. The embedding is injective;
its action need only be surjective. No splitting or finite ambient is assumed. -/

noncomputable section
set_option maxHeartbeats 2000000
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralTwoNormalizerAction

open ModularRep ModularRep.CharacterWeight
open TypeBCentralKernelNormalizerInertia
open TypeBCentralKernelWeightTransport (localMk)
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierActualNormalizerBase
open SporadicFi24P3Definition44NamedCarrierActualLocalInvariance (actualConjugation_brauer_fixed)
open SporadicFi24P3Definition44NamedCarrierCentralTwoExtensionAmbient

universe u
section ActualAction
variable {p : ℕ} {k K G T C : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Group T] [Group C] [Finite G]
variable (E : GroupExtension G T C)
variable (iota : PrimeRegularRootEmbedding p k K G) (chi : IBr iota)

def ambientAction : brauerAmbient E iota chi →* MulAut G :=
  (actualConjugation iota chi).comp (brauerAction E iota chi)

def normalizerAction (Q : Subgroup G) :
    embeddedNormalizer (brauerEmbedding E iota chi) Q →* MulAut G :=
  (ambientAction E iota chi).comp (embeddedNormalizer (brauerEmbedding E iota chi) Q).subtype

theorem ambient_brauer_fixed (a : brauerAmbient E iota chi) :
    MulOpposite.op (ambientAction E iota chi a) • chi = chi :=
  actualConjugation_brauer_fixed iota chi (brauerAction E iota chi a)

theorem normalizer_stable (Q : Subgroup G)
    (d : embeddedNormalizer (brauerEmbedding E iota chi) Q) :
    Q.comap (ambientAction E iota chi d.val).toMonoidHom = Q := by
  have hsquare : (brauerEmbedding E iota chi).comp
      (ambientAction E iota chi d.val).toMonoidHom =
        (MulAut.conj d.val).toMonoidHom.comp (brauerEmbedding E iota chi) := by
    apply MonoidHom.ext
    intro x
    exact brauerEmbedding_conjugation E iota chi d.val x
  have hmap : Q.map (ambientAction E iota chi d.val).toMonoidHom = Q := by
    apply Subgroup.map_injective (brauerEmbedding_injective E iota chi)
    rw [Subgroup.map_map, hsquare, ← Subgroup.map_map]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp d.property
  have h := congrArg (fun R : Subgroup G =>
    R.comap (ambientAction E iota chi d.val).toMonoidHom) hmap
  rw [Subgroup.comap_map_eq_self_of_injective (ambientAction E iota chi d.val).injective Q] at h
  exact h.symm

theorem mem_normalizer_iff_stable (Q : Subgroup G) (a : brauerAmbient E iota chi) :
    a ∈ embeddedNormalizer (brauerEmbedding E iota chi) Q ↔
      Q.comap (ambientAction E iota chi a).toMonoidHom = Q := by
  constructor
  · exact fun ha => normalizer_stable E iota chi Q ⟨a, ha⟩
  · intro hQ
    have hmap : Q.map (ambientAction E iota chi a).toMonoidHom = Q := by
      have h := congrArg (fun R : Subgroup G =>
        R.map (ambientAction E iota chi a).toMonoidHom) hQ
      rw [Subgroup.map_comap_eq_self_of_surjective (ambientAction E iota chi a).surjective Q] at h
      exact h.symm
    have hsquare : (brauerEmbedding E iota chi).comp
        (ambientAction E iota chi a).toMonoidHom =
          (MulAut.conj a).toMonoidHom.comp (brauerEmbedding E iota chi) := by
      apply MonoidHom.ext
      intro x
      exact brauerEmbedding_conjugation E iota chi a x
    change a ∈ Subgroup.normalizer (Q.map (brauerEmbedding E iota chi) : Set _)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_map]
    change Q.map ((MulAut.conj a).toMonoidHom.comp (brauerEmbedding E iota chi)) = _
    rw [← hsquare, ← Subgroup.map_map, hmap]

theorem ordinary_quotient_conjugation (Q : Subgroup G)
    (d : embeddedNormalizer (brauerEmbedding E iota chi) Q)
    (n : Subgroup.normalizer (Q : Set G)) :
    localAut Q (ambientAction E iota chi d.val) (normalizer_stable E iota chi Q d)
      (localMk Q n) =
    localMk Q ((normalizerBaseEquiv (brauerEmbedding E iota chi)
      (brauerEmbedding_injective E iota chi) Q).symm
        (MulAut.conjNormal d (normalizerBaseEquiv (brauerEmbedding E iota chi)
          (brauerEmbedding_injective E iota chi) Q n))) := by
  rw [localAut_mk]
  apply congrArg (localMk Q)
  apply (normalizerBaseEquiv (brauerEmbedding E iota chi)
    (brauerEmbedding_injective E iota chi) Q).injective
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  apply Subtype.ext
  change brauerEmbedding E iota chi
      (normalizerAut Q (ambientAction E iota chi d.val)
        (normalizer_stable E iota chi Q d) n : G) =
    d.val * brauerEmbedding E iota chi n.val * d.val⁻¹
  rw [normalizerAut_coe]
  exact brauerEmbedding_conjugation E iota chi d.val n.val

end ActualAction

section Faithful
variable {p : ℕ} {k K G T C : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Group T] [Group C] [Fintype G]
variable (E : GroupExtension G T C)
variable (iota : PrimeRegularRootEmbedding p k K G)
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorCarriers
open SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryInertia

variable {Block : Type u} [Fintype Block]
variable {blockIdempotent : Block → k[G]}
local instance centerFintype : Fintype (Subgroup.center G) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center G) : k)]
variable (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := G))
variable (E1 : RoutineTransportInput iota hinj blocks R)
local notation "FB" => FaithfulIBr iota hinj blocks R E1

/-- Faithfulness forces the embedded centre to be central in the actual ambient. -/
theorem embedded_center_central (phi : FB) :
    (Subgroup.center G).map (brauerEmbedding E iota phi.val) ≤
      Subgroup.center (brauerAmbient E iota phi.val) := by
  rintro _ ⟨z, hz, rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro a
  have h := brauerEmbedding_conjugation E iota phi.val a z
  have hf := faithful_fixed_fixes_center iota hinj blocks R E1 phi
    (ambientAction E iota phi.val a) (ambient_brauer_fixed E iota phi.val a) ⟨z, hz⟩
  change brauerEmbedding E iota phi.val (ambientAction E iota phi.val a z) = _ at h
  rw [hf] at h
  exact (eq_mul_inv_iff_mul_eq.mp h).symm

theorem normalizerAction_mem_range_iff (phi : FB)
    (hAut : Function.Surjective E.conjAct) (Q : Subgroup G) (alpha : MulAut G) :
    alpha ∈ (normalizerAction E iota phi.val Q).range ↔
      (∀ z : Subgroup.center G, alpha z.val = z.val) ∧
      Q.comap alpha.toMonoidHom = Q ∧ MulOpposite.op alpha • phi.val = phi.val := by
  constructor
  · rintro ⟨d, rfl⟩
    refine ⟨?_, normalizer_stable E iota phi.val Q d,
      ambient_brauer_fixed E iota phi.val d.val⟩
    exact faithful_fixed_fixes_center iota hinj blocks R E1 phi
      (ambientAction E iota phi.val d.val) (ambient_brauer_fixed E iota phi.val d.val)
  · rintro ⟨_, hQ, hfixed⟩
    let a0 : ActualAutAmbient iota phi.val :=
      ⟨(MulOpposite.op alpha)⁻¹,
        (MulAction.stabilizer (MulAut G)ᵐᵒᵖ phi.val).inv_mem hfixed⟩
    obtain ⟨a, ha⟩ := brauerAction_surjective E iota phi.val hAut a0
    have hb : ambientAction E iota phi.val a = alpha := by
      change actualConjugation iota phi.val (brauerAction E iota phi.val a) = alpha
      rw [ha]
      change (alpha⁻¹)⁻¹ = alpha
      exact inv_inv alpha
    have hd : a ∈ embeddedNormalizer (brauerEmbedding E iota phi.val) Q := by
      apply (mem_normalizer_iff_stable E iota phi.val Q a).mpr
      rw [hb]
      exact hQ
    exact ⟨⟨a, hd⟩, hb⟩

end Faithful
end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralTwoNormalizerAction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
