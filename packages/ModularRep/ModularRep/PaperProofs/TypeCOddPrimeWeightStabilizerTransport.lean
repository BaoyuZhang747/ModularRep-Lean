import ModularRep.PaperProofs.TypeBClassInertiaFactorization

/-!
# The actual Type C raw-weight stabilizer conjugation join

Li (2021), Section 2.C, gives G-conjugation coverage by the standard
product radical subgroups. Lemma 5.5(1), printed p.607, gives the raw
M times G E stabilizer product for every own defect-zero character over
each such standard subgroup. The next sentence replaces E by E^x for a
conjugated radical. This module proves the needed fixed-G-E consequence:
conjugation by an element of G preserves both M and G E.

All results here are K deductions on the criterion's actual natural action.
No source theorem is asserted, no family of standard subgroups is invented,
and no class-level coverage substitutes for transport of the own ordinary
character. The final consumer takes group-only coverage and the standard
subgroup statement; it derives the formula for every actual raw weight,
then uses the existing raw-to-class theorem on that same weight.
-/

noncomputable section

open scoped Pointwise

namespace ModularRep.PaperProofs.TypeCOddPrimeWeightStabilizerTransport

open ModularRep TypeBCriterionHypotheses TypeBLocalOrdinaryGeometry
open TypeBClassInertiaFactorization

section GroupProduct

variable {A : Type} [Group A]

/-- Conjugation by an element in both fixed factors preserves the actual
intersection-product formula. No normality or independent image equality
is required. -/
theorem intersection_product_map_conj
    (I L R : Subgroup A) (h : A) (hL : h ∈ L) (hR : h ∈ R)
    (product : (I : Set A) = (↑(I ⊓ L) : Set A) * (↑(I ⊓ R) : Set A)) :
    let J := I.map (MulAut.conj h).toMonoidHom
    (J : Set A) = (↑(J ⊓ L) : Set A) * (↑(J ⊓ R) : Set A) := by
  dsimp only
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := hz
    change y ∈ (I : Set A) at hy
    rw [product] at hy
    obtain ⟨l, hl, r, hr, rfl⟩ := hy
    refine ⟨MulAut.conj h l, ⟨⟨l, hl.1, rfl⟩, ?_⟩,
      MulAut.conj h r, ⟨⟨r, hr.1, rfl⟩, ?_⟩, (map_mul _ _ _).symm⟩
    · exact L.mul_mem (L.mul_mem hL hl.2) (L.inv_mem hL)
    · exact R.mul_mem (R.mul_mem hR hr.2) (R.inv_mem hR)
  · rintro z ⟨l, hl, r, hr, rfl⟩
    exact (I.map (MulAut.conj h).toMonoidHom).mul_mem hl.1 hr.1

end GroupProduct

section ActualWeights

variable {ell : ℕ} {K M E : Type}
variable [Field K] [CharZero K] [IsAlgClosed K]
variable [Group M] [Finite M] [Group E] [Finite E]
variable (G : Subgroup M) [G.Normal] (field : E →* MulAut M)
variable (action : NaturalAction G field)

/-- Positive base conjugation of the whole raw pair. The manuscript right
twist therefore has the inverse conjugation automorphism. -/
def conjugateWeight (W : CharacterWeight ell K G) (g : G) :
    CharacterWeight ell K G :=
  W.rightTwist (MulAut.conj g⁻¹)

@[simp]
theorem conjugateWeight_subgroup (W : CharacterWeight ell K G) (g : G) :
    (conjugateWeight G W g).subgroup =
      W.subgroup.comap (MulAut.conj g⁻¹).toMonoidHom := rfl

/-- The transported pair retains precisely the original own character
pulled through its canonical normalizer-quotient equivalence. -/
theorem conjugateWeight_localCharacter (W : CharacterWeight ell K G) (g : G)
    (x : NormalizerQuotient (conjugateWeight G W g).subgroup) :
    (conjugateWeight G W g).localCharacter x =
      W.localCharacter (rightNormalizerQuotientEquiv
        (MulAut.conj g⁻¹) W.subgroup x) := rfl

/-- Cancellation is equality of the whole pair, including its own local
ordinary character, by the checked right-twist composition law. -/
theorem conjugateWeight_inverse (W : CharacterWeight ell K G) (g : G) :
    conjugateWeight G (conjugateWeight G W g) g⁻¹ = W := by
  simp only [conjugateWeight, inv_inv]
  have h := CharacterWeight.eq_of_isomorphic
    (CharacterWeight.rightTwist_mul_isomorphic W
      (MulAut.conj g⁻¹) (MulAut.conj g))
  have hproduct : MulAut.conj g⁻¹ * MulAut.conj g = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  rw [hproduct] at h
  exact h.trans (CharacterWeight.eq_of_isomorphic
    (CharacterWeight.rightTwist_one_isomorphic W))

/-- The actual ambient raw stabilizer of the conjugated pair is the image
under conjugation by the same embedded base element. -/
theorem rawInertia_conjugateWeight (W : CharacterWeight ell K G) (g : G) :
    rawInertia G field action (conjugateWeight G W g) =
      (rawInertia G field action W).map
        (MulAut.conj (baseEmbedding G field g)).toMonoidHom := by
  letI := rawAmbientAction (ell := ell) (K := K) G field action
  change MulAction.stabilizer (Ambient field)
      (g • (Quotient.mk'' W : Raw (ell := ell) (K := K) G)) =
    (MulAction.stabilizer (Ambient field)
      (Quotient.mk'' W : Raw (ell := ell) (K := K) G)).map
        (MulAut.conj (baseEmbedding G field g)).toMonoidHom
  rw [← base_smul_raw G field action g]
  exact MulAction.stabilizer_smul_eq_stabilizer_map_conj _ _

/-- The explicit radical normalizer introduces no change to the same
raw-pair stabilizer, so the identical image formula applies to it. -/
theorem rawNormalizerInertia_conjugateWeight
    (W : CharacterWeight ell K G) (g : G) :
    rawNormalizerInertia G field action (conjugateWeight G W g) =
      (rawNormalizerInertia G field action W).map
        (MulAut.conj (baseEmbedding G field g)).toMonoidHom := by
  simp only [rawNormalizerInertia_eq_rawInertia, rawInertia_conjugateWeight]

/-- Unlike the field subgroup alone, both factors M and G E contain the
conjugating base element. The fixed-factor raw formula therefore passes
to every actual G-conjugate pair. -/
theorem rawFactorization_conjugateWeight
    (W : CharacterWeight ell K G) (g : G)
    (raw : RawNormalizerFactorization G field action W) :
    RawNormalizerFactorization G field action (conjugateWeight G W g) := by
  have hM : baseEmbedding G field g ∈ embeddedM field := ⟨g.1, rfl⟩
  have hGE : baseEmbedding G field g ∈ baseFieldGroup G field :=
    (embeddedG_le_baseFieldGroup G field) ⟨g, rfl⟩
  have h := intersection_product_map_conj
    (rawNormalizerInertia G field action W)
    (embeddedM field) (baseFieldGroup G field)
    (baseEmbedding G field g) hM hGE raw
  change (rawNormalizerInertia G field action (conjugateWeight G W g) :
      Set (Ambient field)) =
    (↑(rawNormalizerInertia G field action (conjugateWeight G W g) ⊓
      embeddedM field) : Set (Ambient field)) *
    (↑(rawNormalizerInertia G field action (conjugateWeight G W g) ⊓
      baseFieldGroup G field) : Set (Ambient field))
  rw [rawNormalizerInertia_conjugateWeight]
  exact h

theorem rawFactorization_conjugateWeight_iff
    (W : CharacterWeight ell K G) (g : G) :
    RawNormalizerFactorization G field action (conjugateWeight G W g) ↔
      RawNormalizerFactorization G field action W := by
  constructor
  · intro h
    have hback := rawFactorization_conjugateWeight G field action
      (conjugateWeight G W g) g⁻¹ h
    simpa only [conjugateWeight_inverse] using hback
  · exact rawFactorization_conjugateWeight G field action W g

/-- The source domain is only group-level conjugation coverage and the
standard-subgroup formula for each actual own local character. Twisting W
itself chooses the matching standard pair; no weight/character coverage
or class-level factorization is a source premise.

For Li's application, R must be the actual product-basic subgroup family
of Section 2.C, and `standard` is Lemma 5.5(1). This generic K theorem does
not assert either external input or identify an arbitrary family with it. -/
theorem rawFactorization_of_standard_subgroups
    {Index : Type} (R : Index → Subgroup G)
    (coverage : ∀ Q : Subgroup G, IsRadicalSubgroup ell Q →
      ∃ (i : Index) (g : G),
        Q.comap (MulAut.conj g⁻¹).toMonoidHom = R i)
    (standard : ∀ (i : Index) (W : CharacterWeight ell K G),
      W.subgroup = R i → RawNormalizerFactorization G field action W)
    (W : CharacterWeight ell K G) :
    RawNormalizerFactorization G field action W := by
  obtain ⟨i, g, hsubgroup⟩ := coverage W.subgroup W.radical
  have hstandard := standard i (conjugateWeight G W g) hsubgroup
  exact (rawFactorization_conjugateWeight_iff G field action W g).mp hstandard

/-- The class formula concerns the SAME pair and is obtained from the
accepted generic raw-to-class K bridge, not from a selected representative
or an independently supplied class stabilizer. -/
theorem weightClassFactorization_of_standard_subgroups
    {Index : Type} (R : Index → Subgroup G)
    (coverage : ∀ Q : Subgroup G, IsRadicalSubgroup ell Q →
      ∃ (i : Index) (g : G),
        Q.comap (MulAut.conj g⁻¹).toMonoidHom = R i)
    (standard : ∀ (i : Index) (W : CharacterWeight ell K G),
      W.subgroup = R i → RawNormalizerFactorization G field action W)
    (W : CharacterWeight ell K G) :
    WeightClassFactorization G field action W :=
  weightClassFactorization_of_rawNormalizerFactorization G field action W
    (rawFactorization_of_standard_subgroups G field action R coverage standard W)

/-- Identity is now a valid normalizer conjugator because K has proved the
raw formula for every own pair. Both clauses use exactly the criterion's
computed identity-twisted pair. -/
theorem rawNormalizerClause_of_standard_subgroups
    {Index : Type} (R : Index → Subgroup G)
    (coverage : ∀ Q : Subgroup G, IsRadicalSubgroup ell Q →
      ∃ (i : Index) (g : G),
        Q.comap (MulAut.conj g⁻¹).toMonoidHom = R i)
    (standard : ∀ (i : Index) (W : CharacterWeight ell K G),
      W.subgroup = R i → RawNormalizerFactorization G field action W) :
    RawNormalizerClause (ell := ell) (K := K) G field action := by
  intro W
  refine ⟨1, (Subgroup.normalizer _).one_mem, ?_, ?_⟩
  · exact rawFactorization_of_standard_subgroups G field action R coverage standard _
  · exact weightClassFactorization_of_standard_subgroups
      G field action R coverage standard _

end ActualWeights

end ModularRep.PaperProofs.TypeCOddPrimeWeightStabilizerTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
