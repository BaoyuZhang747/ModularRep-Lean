import ModularRep.WeightCharacterBridge

/-!
# Actual character weights along a finite group equivalence

The subgroup is its actual image. The OWN ordinary character is pulled
through the inverse of the canonical normalizer-quotient equivalence.
Raw composition and invertibility are proved from normalizer coordinates
and own values, then descended through both existing quotient relations.
Conjugated automorphisms intertwine the actual right-twist actions in K.

There is no splitting-character source, root convention, block assignment,
fibre premise, selected relation, FM correspondence, or iBAW assertion.
-/

noncomputable section

namespace ModularRep.CharacterWeight

universe u

variable {p : ℕ} {K G H J : Type u}
variable [Field K] [CharZero K]
variable [Group G] [Finite G] [Group H] [Finite H] [Group J] [Finite J]

/-- Forward transport of an actual own-character weight. -/
def mapGroupEquiv (W : CharacterWeight p K G) (e : G ≃* H) :
    CharacterWeight p K H where
  prime := W.prime
  subgroup := W.subgroup.map e.toMonoidHom
  radical := W.radical.map_equiv e
  localCharacter := OrdinaryIrreducibleCharacter.mapEquiv W.localCharacter
    (normalizerQuotientEquiv e W.subgroup)
  defectZero := W.defectZero.mapEquiv (normalizerQuotientEquiv e W.subgroup)

@[simp] theorem mapGroupEquiv_subgroup (W : CharacterWeight p K G) (e : G ≃* H) :
    (W.mapGroupEquiv e).subgroup = W.subgroup.map e.toMonoidHom := rfl

/-- The local quotient map is exactly the existing map of normalizers. -/
theorem mapGroupEquiv_quotient_mk (W : CharacterWeight p K G) (e : G ≃* H)
    (x : Subgroup.normalizer (W.subgroup : Set G)) :
    normalizerQuotientEquiv e W.subgroup (QuotientGroup.mk x) =
      QuotientGroup.mk (normalizerEquiv e W.subgroup x) := rfl

/-- The displayed normalizer map has the original group coordinates. -/
theorem mapGroupEquiv_normalizer_coe (W : CharacterWeight p K G) (e : G ≃* H)
    (x : Subgroup.normalizer (W.subgroup : Set G)) :
    (normalizerEquiv e W.subgroup x : H) = e (x : G) := rfl

@[simp] theorem mapGroupEquiv_localCharacter_apply (W : CharacterWeight p K G)
    (e : G ≃* H) (x : NormalizerQuotient (W.subgroup.map e.toMonoidHom)) :
    (W.mapGroupEquiv e).localCharacter x =
      W.localCharacter ((normalizerQuotientEquiv e W.subgroup).symm x) := rfl

/-- The character equation is on the OWN local character, on every element. -/
theorem mapGroupEquiv_localCharacter_image (W : CharacterWeight p K G)
    (e : G ≃* H) (x : NormalizerQuotient W.subgroup) :
    (W.mapGroupEquiv e).localCharacter (normalizerQuotientEquiv e W.subgroup x) =
      W.localCharacter x := by
  change W.localCharacter ((normalizerQuotientEquiv e W.subgroup).symm
    (normalizerQuotientEquiv e W.subgroup x)) = W.localCharacter x
  rw [MulEquiv.symm_apply_apply]

theorem mapGroupEquiv_normalizer_values (W : CharacterWeight p K G)
    (e : G ≃* H) (x : Subgroup.normalizer (W.subgroup : Set G)) :
    (W.mapGroupEquiv e).localCharacter (QuotientGroup.mk (normalizerEquiv e W.subgroup x)) =
      W.localCharacter (QuotientGroup.mk x) := by
  exact mapGroupEquiv_localCharacter_image W e (QuotientGroup.mk x)

/-- A raw image is determined by the actual subgroup image and its own
normalizer values through a map with the SAME ambient coordinates. This
is an extensionality lemma, not a source interface. -/
theorem mapGroupEquiv_eq_of_normalizer_coordinates
    (W : CharacterWeight p K G) (e : G ≃* H) (V : CharacterWeight p K H)
    (hQ : V.subgroup = W.subgroup.map e.toMonoidHom)
    (eN : Subgroup.normalizer (W.subgroup : Set G) ≃*
      Subgroup.normalizer (V.subgroup : Set H))
    (coordinates : ∀ x, (eN x : H) = e (x : G))
    (values : ∀ x, V.localCharacter (QuotientGroup.mk (eN x)) =
      W.localCharacter (QuotientGroup.mk x)) :
    W.mapGroupEquiv e = V := by
  rcases V with ⟨hp, Q, hrad, chi, hdz⟩
  change Q = W.subgroup.map e.toMonoidHom at hQ
  subst Q
  have heN : eN = normalizerEquiv e W.subgroup := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    exact coordinates x
  apply eq_of_isomorphic
  refine ⟨rfl, ?_⟩
  apply OrdinaryIrreducibleCharacter.ext
  intro z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
    ((W.subgroup.map e.toMonoidHom).subgroupOf
      (Subgroup.normalizer ((W.subgroup.map e.toMonoidHom : Subgroup H) : Set H))) z
  obtain ⟨y, rfl⟩ := (normalizerEquiv e W.subgroup).surjective x
  change (W.mapGroupEquiv e).localCharacter
      (QuotientGroup.mk (normalizerEquiv e W.subgroup y)) =
    chi (QuotientGroup.mk (normalizerEquiv e W.subgroup y))
  exact (mapGroupEquiv_normalizer_values W e y).trans
    (by simpa only [heN] using (values y).symm)

/-- Literal identity of the entire pair, including its own character. -/
@[simp] theorem mapGroupEquiv_refl (W : CharacterWeight p K G) :
    W.mapGroupEquiv (MulEquiv.refl G) = W := by
  apply mapGroupEquiv_eq_of_normalizer_coordinates W (MulEquiv.refl G) W
    (by simp) (MulEquiv.refl _)
  · intro x
    rfl
  · intro x
    rfl

/-- Actual normalizer coordinates and own values prove raw composition. -/
theorem mapGroupEquiv_trans (W : CharacterWeight p K G) (e : G ≃* H) (d : H ≃* J) :
    (W.mapGroupEquiv e).mapGroupEquiv d = W.mapGroupEquiv (e.trans d) := by
  symm
  apply mapGroupEquiv_eq_of_normalizer_coordinates W (e.trans d)
    ((W.mapGroupEquiv e).mapGroupEquiv d)
    (by simp only [mapGroupEquiv_subgroup, Subgroup.map_map]; rfl)
    ((normalizerEquiv e W.subgroup).trans
      (normalizerEquiv d (W.subgroup.map e.toMonoidHom)))
  · intro x
    rfl
  · intro x
    exact (mapGroupEquiv_normalizer_values (W.mapGroupEquiv e) d
      (normalizerEquiv e W.subgroup x)).trans (mapGroupEquiv_normalizer_values W e x)

@[simp] theorem mapGroupEquiv_symm_mapGroupEquiv (W : CharacterWeight p K G)
    (e : G ≃* H) : (W.mapGroupEquiv e).mapGroupEquiv e.symm = W := by
  rw [mapGroupEquiv_trans, MulEquiv.self_trans_symm, mapGroupEquiv_refl]

@[simp] theorem mapGroupEquiv_mapGroupEquiv_symm (W : CharacterWeight p K H)
    (e : G ≃* H) : (W.mapGroupEquiv e.symm).mapGroupEquiv e = W := by
  rw [mapGroupEquiv_trans, MulEquiv.symm_trans_self, mapGroupEquiv_refl]

theorem mapGroupEquiv_isomorphic (e : G ≃* H) {W V : CharacterWeight p K G}
    (h : Isomorphic W V) : Isomorphic (W.mapGroupEquiv e) (V.mapGroupEquiv e) := by
  cases eq_of_isomorphic h
  exact isomorphic_refl _

theorem mapGroupEquiv_isomorphic_iff (e : G ≃* H) (W V : CharacterWeight p K G) :
    Isomorphic (W.mapGroupEquiv e) (V.mapGroupEquiv e) ↔ Isomorphic W V := by
  constructor
  · intro h
    have hback := mapGroupEquiv_isomorphic e.symm h
    simpa only [mapGroupEquiv_symm_mapGroupEquiv] using hback
  · exact mapGroupEquiv_isomorphic e

/-- Both directions of the raw equivalence are the actual image maps. -/
def rawGroupEquiv (e : G ≃* H) : CharacterWeight p K G ≃ CharacterWeight p K H where
  toFun W := W.mapGroupEquiv e
  invFun V := V.mapGroupEquiv e.symm
  left_inv W := mapGroupEquiv_symm_mapGroupEquiv W e
  right_inv V := mapGroupEquiv_mapGroupEquiv_symm V e

/-- Forward transport by the inverse automorphism is exactly the existing
right twist. This identifies, rather than replaces, its action convention. -/
theorem mapGroupEquiv_mulAut_symm (W : CharacterWeight p K G) (alpha : MulAut G) :
    W.mapGroupEquiv alpha.symm = W.rightTwist alpha := by
  apply mapGroupEquiv_eq_of_normalizer_coordinates W alpha.symm (W.rightTwist alpha)
    ((Subgroup.map_equiv_eq_comap_symm' alpha.symm W.subgroup).symm)
    (rightNormalizerEquiv alpha W.subgroup).symm
  · intro x
    rfl
  · intro x
    change W.localCharacter (rightNormalizerQuotientEquiv alpha W.subgroup
      (QuotientGroup.mk ((rightNormalizerEquiv alpha W.subgroup).symm x))) =
      W.localCharacter (QuotientGroup.mk x)
    rw [rightNormalizerQuotientEquiv_mk, MulEquiv.apply_symm_apply]

/-- Naturality under conjugation of the ACTUAL automorphism by e. -/
theorem mapGroupEquiv_rightTwist (W : CharacterWeight p K G) (e : G ≃* H)
    (alpha : MulAut G) :
    (W.rightTwist alpha).mapGroupEquiv e =
      (W.mapGroupEquiv e).rightTwist (MulAut.congr e alpha) := by
  rw [← mapGroupEquiv_mulAut_symm W alpha,
    ← mapGroupEquiv_mulAut_symm (W.mapGroupEquiv e) (MulAut.congr e alpha),
    mapGroupEquiv_trans, mapGroupEquiv_trans]
  congr 1
  apply MulEquiv.ext
  intro x
  simp [MulAut.congr]

/-- A displayed commuting square specializes the same K naturality law. -/
theorem mapGroupEquiv_rightTwist_of_commutes (W : CharacterWeight p K G)
    (e : G ≃* H) (alpha : MulAut G) (beta : MulAut H)
    (commutes : ∀ g, e (alpha g) = beta (e g)) :
    (W.rightTwist alpha).mapGroupEquiv e = (W.mapGroupEquiv e).rightTwist beta := by
  have hbeta : MulAut.congr e alpha = beta := by
    apply MulEquiv.ext
    intro h
    change e (alpha (e.symm h)) = beta h
    rw [commutes, MulEquiv.apply_symm_apply]
  simpa only [hbeta] using mapGroupEquiv_rightTwist W e alpha

/-- The first quotient map uses only raw isomorphism transport. -/
def mapIsoClassGroupEquiv (e : G ≃* H) :
    IsoClass (p := p) (K := K) (G := G) → IsoClass (p := p) (K := K) (G := H) :=
  Quotient.map (fun W => W.mapGroupEquiv e) (fun _ _ h => mapGroupEquiv_isomorphic e h)

@[simp] theorem mapIsoClassGroupEquiv_mk (e : G ≃* H) (W : CharacterWeight p K G) :
    mapIsoClassGroupEquiv e (Quotient.mk'' W) = Quotient.mk'' (W.mapGroupEquiv e) := rfl

@[simp] theorem mapIsoClassGroupEquiv_symm_map (e : G ≃* H)
    (x : IsoClass (p := p) (K := K) (G := G)) :
    mapIsoClassGroupEquiv e.symm (mapIsoClassGroupEquiv e x) = x := by
  refine Quotient.inductionOn x ?_
  intro W
  exact congrArg Quotient.mk'' (mapGroupEquiv_symm_mapGroupEquiv W e)

/-- The exact first quotient carriers are equivalent in K. -/
def isoClassGroupEquiv (e : G ≃* H) :
    IsoClass (p := p) (K := K) (G := G) ≃ IsoClass (p := p) (K := K) (G := H) where
  toFun := mapIsoClassGroupEquiv e
  invFun := mapIsoClassGroupEquiv e.symm
  left_inv := mapIsoClassGroupEquiv_symm_map e
  right_inv := mapIsoClassGroupEquiv_symm_map e.symm

theorem mapIsoClassGroupEquiv_rightTwist (e : G ≃* H) (alpha : MulAut G)
    (x : IsoClass (p := p) (K := K) (G := G)) :
    mapIsoClassGroupEquiv e (rightTwistIsoClass alpha x) =
      rightTwistIsoClass (MulAut.congr e alpha) (mapIsoClassGroupEquiv e x) := by
  refine Quotient.inductionOn x ?_
  intro W
  exact congrArg Quotient.mk'' (mapGroupEquiv_rightTwist W e alpha)

/-- Actual inner conjugacy travels through the SAME group element image. -/
theorem mapIsoClassGroupEquiv_conjugation (e : G ≃* H) (g : G)
    (x : IsoClass (p := p) (K := K) (G := G)) :
    mapIsoClassGroupEquiv e (g • x) = e g • mapIsoClassGroupEquiv e x := by
  refine Quotient.inductionOn x ?_
  intro W
  apply congrArg Quotient.mk''
  apply mapGroupEquiv_rightTwist_of_commutes W e (MulAut.conj g⁻¹) (MulAut.conj (e g)⁻¹)
  intro a
  simp only [MulAut.conj_apply, MulAut.conj_inv_apply, map_mul, map_inv, inv_inv]

/-- The second quotient map retains ambient conjugacy, with no orbit
bijection or naturality premise. -/
def mapConjugacyClassGroupEquiv (e : G ≃* H) :
    ConjugacyClass (p := p) (K := K) (G := G) →
      ConjugacyClass (p := p) (K := K) (G := H) :=
  Quotient.map (mapIsoClassGroupEquiv e) (by
    intro x y h
    rcases h with ⟨g, rfl⟩
    exact ⟨e g, (mapIsoClassGroupEquiv_conjugation e g y).symm⟩)

@[simp] theorem mapConjugacyClassGroupEquiv_mk (e : G ≃* H)
    (W : CharacterWeight p K G) :
    mapConjugacyClassGroupEquiv e (Quotient.mk'' (Quotient.mk'' W)) =
      Quotient.mk'' (Quotient.mk'' (W.mapGroupEquiv e)) := rfl

@[simp] theorem mapConjugacyClassGroupEquiv_symm_map (e : G ≃* H)
    (x : ConjugacyClass (p := p) (K := K) (G := G)) :
    mapConjugacyClassGroupEquiv e.symm (mapConjugacyClassGroupEquiv e x) = x := by
  refine Quotient.inductionOn x ?_
  intro w
  exact congrArg Quotient.mk'' (mapIsoClassGroupEquiv_symm_map e w)

/-- Actual weight conjugacy classes are equivalent under the displayed
group equivalence. Both directions are computed from raw image pairs. -/
def conjugacyClassGroupEquiv (e : G ≃* H) :
    ConjugacyClass (p := p) (K := K) (G := G) ≃
      ConjugacyClass (p := p) (K := K) (G := H) where
  toFun := mapConjugacyClassGroupEquiv e
  invFun := mapConjugacyClassGroupEquiv e.symm
  left_inv := mapConjugacyClassGroupEquiv_symm_map e
  right_inv := mapConjugacyClassGroupEquiv_symm_map e.symm

@[simp] theorem conjugacyClassGroupEquiv_mk (e : G ≃* H) (W : CharacterWeight p K G) :
    conjugacyClassGroupEquiv e (Quotient.mk'' (Quotient.mk'' W)) =
      Quotient.mk'' (Quotient.mk'' (W.mapGroupEquiv e)) := rfl

theorem conjugacyClassGroupEquiv_rightTwist (e : G ≃* H) (alpha : MulAut G)
    (x : ConjugacyClass (p := p) (K := K) (G := G)) :
    conjugacyClassGroupEquiv e (rightTwistConjugacyClass alpha x) =
      rightTwistConjugacyClass (MulAut.congr e alpha) (conjugacyClassGroupEquiv e x) := by
  refine Quotient.inductionOn x ?_
  intro w
  exact congrArg Quotient.mk'' (mapIsoClassGroupEquiv_rightTwist e alpha w)

/-- Exact equivariance for the existing opposite-group right action. -/
theorem conjugacyClassGroupEquiv_op_smul (e : G ≃* H) (alpha : (MulAut G)ᵐᵒᵖ)
    (x : ConjugacyClass (p := p) (K := K) (G := G)) :
    conjugacyClassGroupEquiv e (alpha • x) =
      MulOpposite.op (MulAut.congr e alpha.unop) • conjugacyClassGroupEquiv e x :=
  conjugacyClassGroupEquiv_rightTwist e alpha.unop x

end ModularRep.CharacterWeight


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
