import ModularRep.RadicalTransport
import ModularRep.Weight

/-!
# Transport of representation theoretic weights

This file deliberately stops at the representation-level notion
`RepresentationWeight`.  It does not identify simple representations with
ordinary characters, transport block membership, or construct block
induction.
-/

open CategoryTheory Module

namespace ModularRep

universe u v

variable {G H : Type v} [Group G] [Group H]

/-- A group equivalence induces an equivalence between the normaliser
quotients attached to a subgroup and its image. -/
def normalizerQuotientEquiv (e : G ≃* H) (Q : Subgroup G) :
    NormalizerQuotient Q ≃* NormalizerQuotient (Q.map e.toMonoidHom) := by
  let ne := normalizerEquiv e Q
  apply QuotientGroup.congr
      (Q.subgroupOf (Subgroup.normalizer (Q : Set G)))
      ((Q.map e.toMonoidHom).subgroupOf
        (Subgroup.normalizer ((Q.map e.toMonoidHom : Subgroup H) : Set H)))
      ne
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change (x : G) ∈ Q at hx
    change ((normalizerEquiv e Q x : _) : H) ∈ Q.map e.toMonoidHom
    rw [normalizerEquiv_coe]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hx
  · intro hy
    change (y : H) ∈ Q.map e.toMonoidHom at hy
    rcases Subgroup.mem_map.mp hy with ⟨q, hq, hqy⟩
    let x : Subgroup.normalizer (Q : Set G) := ⟨q, Q.le_normalizer hq⟩
    refine ⟨x, ?_, ?_⟩
    · change (x : G) ∈ Q
      exact hq
    · apply Subtype.ext
      exact hqy

@[simp]
theorem normalizerQuotientEquiv_mk (e : G ≃* H) (Q : Subgroup G)
    (x : Subgroup.normalizer (Q : Set G)) :
    normalizerQuotientEquiv e Q (QuotientGroup.mk x) =
      QuotientGroup.mk (normalizerEquiv e Q x) :=
  rfl

/-- Contravariant form of `normalizerQuotientEquiv`: an equivalence carries
the normaliser quotient of the inverse-image subgroup to the original
normaliser quotient. -/
def normalizerQuotientComapEquiv (e : G ≃* H) (R : Subgroup H) :
    NormalizerQuotient (R.comap e.toMonoidHom) ≃* NormalizerQuotient R := by
  let Q : Subgroup G := R.comap e.toMonoidHom
  have hmap : Q.map e.toMonoidHom = R :=
    Subgroup.map_comap_eq_self_of_surjective
      (f := e.toMonoidHom) e.surjective R
  exact (normalizerQuotientEquiv e Q).trans
    (MulEquiv.cast (M := fun Q : Subgroup H ↦ NormalizerQuotient Q) hmap)

/-- In the automorphism case, the normaliser equivalence can be written
directly: apply the automorphism to every element. -/
def rightNormalizerEquiv (alpha : MulAut G) (Q : Subgroup G) :
    Subgroup.normalizer ((Q.comap alpha.toMonoidHom : Subgroup G) : Set G) ≃*
      Subgroup.normalizer (Q : Set G) where
  toFun x := by
    refine ⟨alpha x, ?_⟩
    have hxProperty := x.property
    rw [Subgroup.mem_normalizer_iff] at hxProperty ⊢
    intro y
    let z : G := alpha.symm y
    have hx := hxProperty z
    change alpha z ∈ Q ↔ alpha ((x : G) * z * (x : G)⁻¹) ∈ Q at hx
    simpa [z] using hx
  invFun y := by
    refine ⟨alpha.symm y, ?_⟩
    have hyProperty := y.property
    rw [Subgroup.mem_normalizer_iff] at hyProperty ⊢
    intro z
    have hy := hyProperty (alpha z)
    change alpha z ∈ Q ↔
      alpha ((alpha.symm y : G) * z * (alpha.symm y : G)⁻¹) ∈ Q
    simpa using hy
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv y := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    change alpha ((x : G) * (y : G)) = alpha (x : G) * alpha (y : G)
    simp

@[simp]
theorem rightNormalizerEquiv_coe (alpha : MulAut G) (Q : Subgroup G)
    (x : Subgroup.normalizer
      ((Q.comap alpha.toMonoidHom : Subgroup G) : Set G)) :
    ((rightNormalizerEquiv alpha Q x :
      Subgroup.normalizer (Q : Set G)) : G) = alpha x :=
  rfl

/-- Direct automorphism transport on local normaliser quotients. -/
def rightNormalizerQuotientEquiv (alpha : MulAut G) (Q : Subgroup G) :
    NormalizerQuotient (Q.comap alpha.toMonoidHom) ≃*
      NormalizerQuotient Q := by
  apply QuotientGroup.congr
    ((Q.comap alpha.toMonoidHom).subgroupOf
      (Subgroup.normalizer ((Q.comap alpha.toMonoidHom : Subgroup G) : Set G)))
    (Q.subgroupOf (Subgroup.normalizer (Q : Set G)))
    (rightNormalizerEquiv alpha Q)
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    change (x : G) ∈ Q
    change (y : G) ∈ Q.comap alpha.toMonoidHom at hy
    have hxyG : alpha (y : G) = (x : G) := by
      have h := congrArg
        (fun z : Subgroup.normalizer (Q : Set G) ↦ (z : G)) hxy
      change alpha (y : G) = (x : G) at h
      exact h
    rw [← hxyG]
    exact hy
  · intro hx
    change (x : G) ∈ Q at hx
    let y := (rightNormalizerEquiv alpha Q).symm x
    have hyx : rightNormalizerEquiv alpha Q y = x :=
      (rightNormalizerEquiv alpha Q).apply_symm_apply x
    have hyxG : alpha (y : G) = (x : G) := by
      have h := congrArg
        (fun z : Subgroup.normalizer (Q : Set G) ↦ (z : G)) hyx
      change alpha (y : G) = (x : G) at h
      exact h
    refine ⟨y, ?_, ?_⟩
    · change (y : G) ∈ Q.comap alpha.toMonoidHom
      change alpha (y : G) ∈ Q
      rw [hyxG]
      exact hx
    · exact hyx

@[simp]
theorem rightNormalizerQuotientEquiv_mk
    (alpha : MulAut G) (Q : Subgroup G)
    (x : Subgroup.normalizer
      ((Q.comap alpha.toMonoidHom : Subgroup G) : Set G)) :
    rightNormalizerQuotientEquiv alpha Q (QuotientGroup.mk x) =
      QuotientGroup.mk (rightNormalizerEquiv alpha Q x) :=
  rfl

/-- Pull an `FDRep` object across a group equivalence, in the forward
direction.  The target action is obtained by precomposition with the inverse
equivalence. -/
def fdRepMapEquiv {K : Type u} [Field K]
    {A B : Type v} [Group A] [Group B]
    (e : A ≃* B) (V : FDRep K A) : FDRep K B :=
  (Action.res (FGModuleCat K) e.symm.toMonoidHom).obj V

@[simp]
theorem fdRepMapEquiv_rho {K : Type u} [Field K]
    {A B : Type v} [Group A] [Group B]
    (e : A ≃* B) (V : FDRep K A) (b : B) :
    (fdRepMapEquiv e V).ρ b = V.ρ (e.symm b) :=
  rfl

theorem fdRepMapEquiv_simple {K : Type u} [Field K]
    {A B : Type v} [Group A] [Group B]
    (e : A ≃* B) (V : FDRep K A) [Simple V] :
    Simple (fdRepMapEquiv e V) := by
  exact CategoryTheory.simple_obj
    (Action.resEquiv (FGModuleCat K) e.symm).functor V

/-- Successive transport of an `FDRep` object agrees with transport along the
composite, up to the canonical isomorphism of representations. -/
noncomputable def fdRepMapEquiv_transIso {K : Type u} [Field K]
    {A B C : Type v} [Group A] [Group B] [Group C]
    (e : A ≃* B) (d : B ≃* C) (V : FDRep K A) :
    fdRepMapEquiv d (fdRepMapEquiv e V) ≅ fdRepMapEquiv (e.trans d) V :=
  (Action.resComp (FGModuleCat K) d.symm.toMonoidHom
    e.symm.toMonoidHom).app V

theorem fdRepMapEquiv_defectZero {p : ℕ} {K : Type u} [Field K]
    {A B : Type v} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) (V : FDRep K A)
    (hV : IsDefectZeroRepresentation p V) :
    IsDefectZeroRepresentation p (fdRepMapEquiv e V) := by
  unfold IsDefectZeroRepresentation at hV ⊢
  change ordProj[p] (finrank K V) = ordProj[p] (Nat.card B)
  rw [← Nat.card_congr e.toEquiv]
  exact hV

namespace RepresentationWeight

variable {p : ℕ} {K : Type u} [Field K] [CharZero K]
variable [Finite G] [Finite H]

/-- Transport a representation theoretic weight forward along a group
equivalence. -/
noncomputable def mapEquiv (W : RepresentationWeight p K G) (e : G ≃* H) :
    RepresentationWeight p K H where
  prime := W.prime
  subgroup := W.subgroup.map e.toMonoidHom
  radical := W.radical.map_equiv e
  localRepresentation :=
    fdRepMapEquiv (normalizerQuotientEquiv e W.subgroup) W.localRepresentation
  irreducible := by
    let _ : Simple W.localRepresentation := W.irreducible
    exact fdRepMapEquiv_simple
      (normalizerQuotientEquiv e W.subgroup) W.localRepresentation
  defectZero := fdRepMapEquiv_defectZero
    (normalizerQuotientEquiv e W.subgroup) W.localRepresentation W.defectZero

@[simp]
theorem mapEquiv_subgroup (W : RepresentationWeight p K G) (e : G ≃* H) :
    (W.mapEquiv e).subgroup = W.subgroup.map e.toMonoidHom :=
  rfl

@[simp]
theorem mapEquiv_localRepresentation_rho
    (W : RepresentationWeight p K G) (e : G ≃* H)
    (x : NormalizerQuotient (W.subgroup.map e.toMonoidHom)) :
    (W.mapEquiv e).localRepresentation.ρ x =
      W.localRepresentation.ρ
        ((normalizerQuotientEquiv e W.subgroup).symm x) :=
  rfl

/-- Right transport by an automorphism.  The subgroup is definitionally the
inverse image `alpha⁻¹(Q)`, as in the manuscript, and the local
representation is pulled back along the induced map from the new normaliser
quotient to the old one. -/
noncomputable def rightTwist (W : RepresentationWeight p K G) (alpha : MulAut G) :
    RepresentationWeight p K G where
  prime := W.prime
  subgroup := W.subgroup.comap alpha.toMonoidHom
  radical := W.radical.comap_mulAut alpha
  localRepresentation := fdRepMapEquiv
    (rightNormalizerQuotientEquiv alpha W.subgroup).symm
    W.localRepresentation
  irreducible := by
    let _ : Simple W.localRepresentation := W.irreducible
    exact fdRepMapEquiv_simple
      (rightNormalizerQuotientEquiv alpha W.subgroup).symm
      W.localRepresentation
  defectZero := fdRepMapEquiv_defectZero
    (rightNormalizerQuotientEquiv alpha W.subgroup).symm
    W.localRepresentation W.defectZero

@[simp]
theorem rightTwist_subgroup (W : RepresentationWeight p K G) (alpha : MulAut G) :
    (W.rightTwist alpha).subgroup =
      W.subgroup.comap alpha.toMonoidHom :=
  rfl

@[simp]
theorem rightTwist_localRepresentation_rho
    (W : RepresentationWeight p K G) (alpha : MulAut G)
    (x : NormalizerQuotient (W.subgroup.comap alpha.toMonoidHom)) :
    (W.rightTwist alpha).localRepresentation.ρ x =
      W.localRepresentation.ρ
        (rightNormalizerQuotientEquiv alpha W.subgroup x) :=
  rfl

theorem rightTwist_subgroup_mul (W : RepresentationWeight p K G)
    (alpha beta : MulAut G) :
    ((W.rightTwist alpha).rightTwist beta).subgroup =
      (W.rightTwist (alpha * beta)).subgroup := by
  simp only [rightTwist_subgroup, Subgroup.comap_comap]
  rfl

end RepresentationWeight

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
