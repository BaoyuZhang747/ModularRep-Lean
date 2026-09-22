import ModularRep.PaperProofs.OddTwoFYZPrincipalFullCarrierJoin
import ModularRep.PaperProofs.CyclicOuterRawPairNormalizer

/-!
# Principal weights from arbitrary surviving parameters

The source theorem is Feng, Yu and Zhang, Lemma 2.3, in its quotient
character formulation. Its three conditions retain the centre in the
centraliser, the kernel of the inflated character and the quotient by
the product of the subgroup with its centraliser. The specialisation to
a self centralising subgroup is proved below.

The ordinary character fact that a group with a defect zero character
has trivial 2-core is a separate standard input. Radicality is then
proved by mapping the normaliser core into the actual quotient.
-/

noncomputable section

namespace ManuscriptIBAW.TypeC

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
open ModularRep.PaperProofs.OddTwoPrincipalSelectedCharacterUniqueness
open ModularRep.PaperProofs.OddTwoPrincipalLocalEnumerationJoin
open ModularRep.PaperProofs.OddTwoPrincipalProductAtlas
open ModularRep.PaperProofs.OddTwoPrincipalProductNormalizer
open ModularRep.PaperProofs.OddTwoPrincipalProductCharacterJoin
open ModularRep.PaperProofs.OddTwoWreathCoreCharacterSource
open ModularRep.PaperProofs.OddTwoFYZSourceAdapter

universe u

section GroupFacts

variable {G : Type u} [Group G]

/-- The product `R C_G(R)` inside the actual normaliser. -/
def centralizerProduct (R : Subgroup G) :
    Subgroup (Subgroup.normalizer (R : Set G)) :=
  R.subgroupOf (Subgroup.normalizer (R : Set G)) ⊔
    (Subgroup.centralizer (R : Set G)).subgroupOf
      (Subgroup.normalizer (R : Set G))

instance centralizerProduct_normal (R : Subgroup G) :
    (centralizerProduct R).Normal := by
  unfold centralizerProduct
  infer_instance

theorem centralizerProduct_eq (R : Subgroup G)
    (hC : Subgroup.centralizer (R : Set G) ≤ R) :
    centralizerProduct R = R.subgroupOf (Subgroup.normalizer (R : Set G)) := by
  apply sup_eq_left.mpr
  exact Subgroup.comap_mono hC

theorem centreInCentralizer_eq_top (R : Subgroup G)
    (hC : Subgroup.centralizer (R : Set G) ≤ R) :
    sourceCentreInCentralizer R = ⊤ := by
  apply top_unique
  intro x _
  let r : R := ⟨x.1, hC x.2⟩
  have hr : r ∈ Subgroup.center R := by
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    exact x.2 z.1 z.2
  exact ⟨⟨r, hr⟩, rfl⟩

/-- The centre is the whole centraliser and hence its Sylow subgroup. -/
theorem centre_is_sylow_of_centralizer_le (R : Subgroup G)
    (hR : IsPGroup 2 R) (hC : Subgroup.centralizer (R : Set G) ≤ R) :
    ∃ S : Sylow 2 (Subgroup.centralizer (R : Set G)),
      (S : Subgroup (Subgroup.centralizer (R : Set G))) =
        sourceCentreInCentralizer R := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCentralizer : IsPGroup 2 (Subgroup.centralizer (R : Set G)) :=
    hR.of_injective (Subgroup.inclusion hC) (by
      intro a b h
      exact Subtype.ext (congrArg (fun z : R => (z : G)) h))
  have hTop := hCentralizer.to_subgroup (⊤ : Subgroup
    (Subgroup.centralizer (R : Set G)))
  refine ⟨hTop.toSylow (by simp), ?_⟩
  rw [IsPGroup.toSylow_coe, centreInCentralizer_eq_top R hC]

/-- Triviality of the prime core of the normaliser quotient gives radicality. -/
theorem radical_of_quotient_core_eq_bot (R : Subgroup G)
    (hR : IsPGroup 2 R) (hcore : pCore 2 (NormalizerQuotient R) = ⊥) :
    IsRadicalSubgroup 2 R := by
  let N := Subgroup.normalizer (R : Set G)
  let Q := R.subgroupOf N
  let f := QuotientGroup.mk' Q
  have hQ : IsPGroup 2 Q :=
    hR.of_equiv (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).symm
  have hQcore : Q ≤ pCore 2 N := normal_pSubgroup_le_pCore 2 Q hQ
  have hmap : (pCore 2 N).map f ≤ pCore 2 (NormalizerQuotient R) := by
    let : ((pCore 2 N).map f).Normal :=
      (pCore_normal 2 N).map f (QuotientGroup.mk'_surjective Q)
    exact normal_pSubgroup_le_pCore 2 _ ((pCore_isPGroup 2 N).map f)
  have hcoreQ : pCore 2 N ≤ Q := by
    intro x hx
    have hm : f x ∈ (⊥ : Subgroup (NormalizerQuotient R)) := by
      rw [← hcore]
      exact hmap ⟨x, hx, rfl⟩
    exact (QuotientGroup.eq_one_iff x).mp hm
  change R = (pCore 2 N).map N.subtype
  rw [le_antisymm hcoreQ hQcore]
  exact (Subgroup.map_subgroupOf_eq_of_le Subgroup.le_normalizer).symm

end GroupFacts

section Principal

variable {n : ℕ} {F k K Block : Type u}
variable [Field F] [Fintype F] [Field k] [CharP k 2] [IsAlgClosed k]
variable [Field K] [CharZero K]
variable [MulAction (MulAut (Sp n F))ᵐᵒᵖ Block]

local instance spFintype (r : ℕ) : Fintype (Sp r F) := Fintype.ofFinite _

variable (D : PrincipalCharacterData (n := n) (F := F) (k := k) (K := K)
  (Block := Block))

/-- The standard defect zero core fact for normaliser quotients over an algebraically closed ordinary coefficient field.
The source concerns every subgroup and does not require the principal block condition. -/
structure DefectZeroCoreSource : Prop where
  ordinarySplitting : IsAlgClosed K
  quotient_core : ∀ (R : Subgroup (Sp n F))
    (_chi : LocalDefectZeroCharacters (K := K) R),
    pCore 2 (NormalizerQuotient R) = ⊥

/-- The quotient form of FYZ Lemma 2.3. The character on the normaliser is the
inflation of the weight representative's own quotient character. The last
field of the criterion says that this very function is inflated from a
defect zero character modulo `R C_G(R)`. -/
structure FYZPrincipalCriterion : Prop where
  principal_iff : ∀ W : CharacterWeight 2 K (Sp n F),
    D.blockSource.operations.rawWeightBlock W = D.principalBlock ↔
      (∃ S : Sylow 2 (Subgroup.centralizer (W.subgroup : Set (Sp n F))),
        (S : Subgroup (Subgroup.centralizer (W.subgroup : Set (Sp n F)))) =
          sourceCentreInCentralizer W.subgroup) ∧
      (∀ z : centralizerProduct W.subgroup,
        W.localCharacter (QuotientGroup.mk' _ z.1) = W.localCharacter 1) ∧
      (∃ theta : DZ K ((Subgroup.normalizer (W.subgroup : Set (Sp n F))) ⧸
          centralizerProduct W.subgroup),
        ∀ z : Subgroup.normalizer (W.subgroup : Set (Sp n F)),
          W.localCharacter (QuotientGroup.mk' _ z) =
            theta.1 (QuotientGroup.mk' _ z))

/-- If the centraliser lies in the subgroup, the two quotients in the criterion
agree through the canonical quotient map. -/
theorem principal_of_centralizer_le (S : FYZPrincipalCriterion D)
    (W : CharacterWeight 2 K (Sp n F))
    (hC : Subgroup.centralizer (W.subgroup : Set (Sp n F)) ≤ W.subgroup) :
    D.blockSource.operations.rawWeightBlock W = D.principalBlock := by
  apply (S.principal_iff W).mpr
  refine ⟨centre_is_sylow_of_centralizer_le W.subgroup W.radical.isPGroup hC, ?_, ?_⟩
  · intro z
    have hz : z.1 ∈ W.subgroup.subgroupOf
        (Subgroup.normalizer (W.subgroup : Set (Sp n F))) := by
      rw [← centralizerProduct_eq W.subgroup hC]
      exact z.2
    have hzq : QuotientGroup.mk'
        (W.subgroup.subgroupOf (Subgroup.normalizer (W.subgroup : Set (Sp n F))))
        z.1 = 1 := (QuotientGroup.eq_one_iff z.1).mpr hz
    rw [hzq]
  · let e := QuotientGroup.quotientMulEquivOfEq
      (centralizerProduct_eq W.subgroup hC).symm
    refine ⟨defectZeroEquiv e ⟨W.localCharacter, W.defectZero⟩, ?_⟩
    intro z
    change W.localCharacter (QuotientGroup.mk' _ z) =
      W.localCharacter (e.symm (QuotientGroup.mk' _ z))
    rfl

/-- Construct the weight from any quotient character, with radicality
derived from the quotient core and principal membership from the criterion. -/
def principalPair (core : DefectZeroCoreSource (n := n) (F := F) (K := K))
    (R : Subgroup (Sp n F)) (hR : IsPGroup 2 R)
    (chi : LocalDefectZeroCharacters (K := K) R) : CharacterWeight 2 K (Sp n F) where
  prime := Nat.prime_two
  subgroup := R
  radical := radical_of_quotient_core_eq_bot R hR (core.quotient_core R chi)
  localCharacter := chi.1
  defectZero := chi.2

theorem principalPair_block (core : DefectZeroCoreSource (n := n) (F := F) (K := K))
    (S : FYZPrincipalCriterion D) (R : Subgroup (Sp n F)) (hR : IsPGroup 2 R)
    (chi : LocalDefectZeroCharacters (K := K) R)
    (hC : Subgroup.centralizer (R : Set (Sp n F)) ≤ R) :
    D.blockSource.operations.rawWeightBlock (principalPair core R hR chi) =
      D.principalBlock :=
  principal_of_centralizer_le D S (principalPair core R hR chi) hC

end Principal

end ManuscriptIBAW.TypeC

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
