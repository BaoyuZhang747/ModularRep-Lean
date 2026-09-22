import ModularRep.RadicalSubgroup

/-!
# Transport of `p`-cores and radical subgroups

The `p`-core is natural under group equivalences and hence characteristic.
The corresponding normaliser construction shows that radical subgroups are
preserved by equivalences, automorphisms, and conjugation.  The contravariant
statements match the manuscript's right action `Q ^ alpha = alpha⁻¹(Q)`.
-/

namespace ModularRep

variable {G H : Type*} [Group G] [Group H]

/-- The `p`-core is natural under group equivalences. -/
theorem pCore_map_equiv (p : ℕ) (e : G ≃* H) :
    (pCore p G).map e.toMonoidHom = pCore p H := by
  apply le_antisymm
  · let _ : ((pCore p G).map e.toMonoidHom).Normal :=
      (pCore_normal p G).map e.toMonoidHom e.surjective
    exact normal_pSubgroup_le_pCore p _
      ((pCore_isPGroup p G).map e.toMonoidHom)
  · rw [Subgroup.map_equiv_eq_comap_symm' e (pCore p G)]
    apply Subgroup.map_le_iff_le_comap.mp
    let _ : ((pCore p H).map e.symm.toMonoidHom).Normal :=
      (pCore_normal p H).map e.symm.toMonoidHom e.symm.surjective
    exact normal_pSubgroup_le_pCore p _
      ((pCore_isPGroup p H).map e.symm.toMonoidHom)

/-- Contravariant form of `pCore_map_equiv`. -/
theorem pCore_comap_equiv (p : ℕ) (e : G ≃* H) :
    (pCore p H).comap e.toMonoidHom = pCore p G := by
  rw [Subgroup.comap_equiv_eq_map_symm' e (pCore p H)]
  exact pCore_map_equiv p e.symm

/-- The `p`-core is characteristic. -/
theorem pCore_characteristic (p : ℕ) (G : Type*) [Group G] :
    (pCore p G).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  exact pCore_map_equiv p

/-- A group equivalence restricts to an equivalence of the corresponding
normalisers. -/
def normalizerEquiv (e : G ≃* H) (Q : Subgroup G) :
    Subgroup.normalizer (Q : Set G) ≃*
      Subgroup.normalizer ((Q.map e.toMonoidHom : Subgroup H) : Set H) :=
  (e.subgroupMap (Subgroup.normalizer (Q : Set G))).trans
    (MulEquiv.subgroupCongr (Subgroup.map_equiv_normalizer_eq Q e))

@[simp]
theorem normalizerEquiv_coe (e : G ≃* H) (Q : Subgroup G)
    (x : Subgroup.normalizer (Q : Set G)) :
    ((normalizerEquiv e Q x :
        Subgroup.normalizer ((Q.map e.toMonoidHom : Subgroup H) : Set H)) : H) =
      e x :=
  rfl

/-- The image of the normaliser's `p`-core is natural under group
equivalences. -/
theorem normalizerPCore_map_equiv (p : ℕ) (e : G ≃* H) (Q : Subgroup G) :
    (normalizerPCore p Q).map e.toMonoidHom =
      normalizerPCore p (Q.map e.toMonoidHom) := by
  unfold normalizerPCore
  rw [← pCore_map_equiv p (normalizerEquiv e Q)]
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

/-- Contravariant form of `normalizerPCore_map_equiv`. -/
theorem normalizerPCore_comap_equiv (p : ℕ) (e : G ≃* H)
    (R : Subgroup H) :
    (normalizerPCore p R).comap e.toMonoidHom =
      normalizerPCore p (R.comap e.toMonoidHom) := by
  rw [Subgroup.comap_equiv_eq_map_symm' e (normalizerPCore p R),
    Subgroup.comap_equiv_eq_map_symm' e R]
  exact normalizerPCore_map_equiv p e.symm R

namespace IsRadicalSubgroup

/-- Group equivalences carry radical subgroups to radical subgroups. -/
theorem map_equiv {p : ℕ} {Q : Subgroup G} (hQ : IsRadicalSubgroup p Q)
    (e : G ≃* H) : IsRadicalSubgroup p (Q.map e.toMonoidHom) := by
  rw [IsRadicalSubgroup] at hQ ⊢
  calc
    Q.map e.toMonoidHom = (normalizerPCore p Q).map e.toMonoidHom :=
      congrArg (fun R : Subgroup G ↦ R.map e.toMonoidHom) hQ
    _ = normalizerPCore p (Q.map e.toMonoidHom) :=
      normalizerPCore_map_equiv p e Q

/-- Inverse images under group equivalences preserve radicality. -/
theorem comap_equiv {p : ℕ} {R : Subgroup H} (hR : IsRadicalSubgroup p R)
    (e : G ≃* H) : IsRadicalSubgroup p (R.comap e.toMonoidHom) := by
  rw [Subgroup.comap_equiv_eq_map_symm' e R]
  exact hR.map_equiv e.symm

/-- Automorphism invariance in the manuscript's right-action convention
`Q ^ alpha = alpha⁻¹(Q)`. -/
theorem comap_mulAut {p : ℕ} {Q : Subgroup G}
    (hQ : IsRadicalSubgroup p Q) (alpha : MulAut G) :
    IsRadicalSubgroup p (Q.comap alpha.toMonoidHom) :=
  hQ.comap_equiv alpha

/-- Conjugation invariance in the same convention: the resulting subgroup is
`g⁻¹ Q g`. -/
theorem comap_conj {p : ℕ} {Q : Subgroup G}
    (hQ : IsRadicalSubgroup p Q) (g : G) :
    IsRadicalSubgroup p (Q.comap (MulAut.conj g).toMonoidHom) :=
  hQ.comap_mulAut (MulAut.conj g)

end IsRadicalSubgroup

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
