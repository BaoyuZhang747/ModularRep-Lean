import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryInertia
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulFamilyComparison

/-! Original-group normalizer action with the identity ambient embedding.
Only realization of the full automorphism range uses centre/outer facts. -/

noncomputable section
set_option maxHeartbeats 2000000
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalNormalizerAction

open ModularRep ModularRep.CharacterWeight
open TypeBCentralKernelNormalizerInertia
open TypeBCentralKernelWeightTransport (localMk)
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierActualLocalInvariance (actualConjugation_brauer_fixed)
open SporadicFi24P3Definition44NamedCarrierFaithfulCenterAmbient
open SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
open SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryInertia
open SporadicFi24P3Definition44NamedCarrierPhysicalScalarBindings

universe u
section Group
variable {G : Type u} [Group G]

def normalizerAction (Q : Subgroup G) :
    Subgroup.normalizer (Q : Set G) →* MulAut G :=
  (MulAut.conj : G →* MulAut G).comp (Subgroup.normalizer (Q : Set G)).subtype

theorem mem_normalizer_iff_stable (Q : Subgroup G) (g : G) :
    g ∈ Subgroup.normalizer (Q : Set G) ↔
      Q.comap (MulAut.conj g).toMonoidHom = Q := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro hg
    apply Subgroup.ext
    intro x
    exact (hg x).symm
  · intro h x
    change x ∈ Q ↔ x ∈ Q.comap (MulAut.conj g).toMonoidHom
    rw [h]

theorem normalizer_stable (Q : Subgroup G) (d : Subgroup.normalizer (Q : Set G)) :
    Q.comap (MulAut.conj d.val).toMonoidHom = Q :=
  (mem_normalizer_iff_stable Q d.val).mp d.property

variable [Finite G]

theorem localAut_conj_mk (Q : Subgroup G) (d : Subgroup.normalizer (Q : Set G))
    (n : Subgroup.normalizer (Q : Set G)) :
    localAut Q (MulAut.conj d.val) (normalizer_stable Q d) (localMk Q n) =
      MulAut.conj (localMk Q d) (localMk Q n) := by
  rw [localAut_mk]
  have hn : normalizerAut Q (MulAut.conj d.val) (normalizer_stable Q d) n =
      d * n * d⁻¹ := by
    apply Subtype.ext
    exact normalizerAut_coe Q (MulAut.conj d.val) (normalizer_stable Q d) n
  rw [hn]
  change localMk Q (d * n * d⁻¹) = localMk Q d * localMk Q n * (localMk Q d)⁻¹
  simp only [map_mul, map_inv]

theorem localAut_conj (Q : Subgroup G) (d : Subgroup.normalizer (Q : Set G)) :
    localAut Q (MulAut.conj d.val) (normalizer_stable Q d) =
      MulAut.conj (localMk Q d) := by
  apply MulEquiv.ext
  intro q
  refine Quotient.inductionOn q ?_
  intro n
  exact localAut_conj_mk Q d n

end Group

section Inner
variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Finite G]

theorem inner_brauer_fixed (iota : PrimeRegularRootEmbedding p k K G)
    (chi : IBr iota) (g : G) : MulOpposite.op (MulAut.conj g) • chi = chi := by
  simpa only [actualConjugation_inner] using
    actualConjugation_brauer_fixed iota chi (innerEmbedding iota chi g)

end Inner

section Faithful
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorCarriers

variable {p : ℕ} {k K G Block : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Fintype Block]
variable {blockIdempotent : Block → k[G]}
local instance centerFintype : Fintype (Subgroup.center G) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center G) : k)]
variable (iota : PrimeRegularRootEmbedding p k K G)
variable (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := G))
variable (E1 : RoutineTransportInput iota hinj blocks R)
local notation "FB" => FaithfulIBr iota hinj blocks R E1

theorem normalizerAction_mem_range_iff (phi : FB)
    (hOuter : Nat.card (LiteralOuterQuotient G) = 2) (tau : MulAut G)
    (hcard : Nat.card (Subgroup.center G) = 3 ∨
      Nat.card (Subgroup.center G) = 4 ∨ Nat.card (Subgroup.center G) = 6)
    (hinverts : ∀ z : Subgroup.center G, tau z.val = z.val⁻¹)
    (Q : Subgroup G) (alpha : MulAut G) :
    alpha ∈ (normalizerAction Q).range ↔
      (∀ z : Subgroup.center G, alpha z.val = z.val) ∧
      Q.comap alpha.toMonoidHom = Q ∧ MulOpposite.op alpha • phi.val = phi.val := by
  constructor
  · rintro ⟨d, rfl⟩
    refine ⟨?_, normalizer_stable Q d, inner_brauer_fixed iota phi.val d.val⟩
    exact faithful_fixed_fixes_center iota hinj blocks R E1 phi
      (MulAut.conj d.val) (inner_brauer_fixed iota phi.val d.val)
  · rintro ⟨_, hQ, hfixed⟩
    have hgt : 2 < Nat.card (Subgroup.center G) := by
      rcases hcard with h | h | h <;> omega
    let a0 : ActualAutAmbient iota phi.val :=
      ⟨(MulOpposite.op alpha)⁻¹,
        (MulAction.stabilizer (MulAut G)ᵐᵒᵖ phi.val).inv_mem hfixed⟩
    have hsurj : Function.Surjective (innerEmbedding iota phi.val) :=
      originalAmbient_surjective iota
        (brauerSector iota hinj blocks phi.val) (scalarBrauer iota hinj blocks phi.val)
        phi.faithful hOuter tau hgt hinverts
    obtain ⟨x, hx⟩ := hsurj a0
    have hxaut : MulAut.conj x = alpha := by
      have h := congrArg (actualConjugation iota phi.val) hx
      rw [actualConjugation_inner] at h
      change MulAut.conj x = (alpha⁻¹)⁻¹ at h
      simpa only [inv_inv] using h
    have hxQ : x ∈ Subgroup.normalizer (Q : Set G) := by
      apply (mem_normalizer_iff_stable Q x).mpr
      rw [hxaut]
      exact hQ
    exact ⟨⟨x, hxQ⟩, hxaut⟩

end Faithful
end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalNormalizerAction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
