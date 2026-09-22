import ModularRep.StabilizerFactorizationTransport
import ModularRep.PaperProofs.IntermediateRestrictionIrreducible

/-! Fix the acting subgroup before choosing a character. The restriction uses
the subgroup inclusions and the same representation space. The geometric
choice is a separate assumption. -/

noncomputable section

namespace ManuscriptIBAW.Jordan

open ModularRep.ManuscriptVerification.StabilizerFactorizationTransport

section Actions

variable {D E X : Type*} [Group D] [Group E]
  [MulAction D X] [MulAction E X]

/-- Restrict the original action along the subgroup inclusion. -/
@[instance_reducible] def restrictedAction (A : Subgroup E) : MulAction A X :=
  MulAction.compHom X A.subtype

/-- Compatibility restricts with the original action on the regular group. -/
theorem restricted_compatible (phi : E →* MulAut D)
    (h : Formalisation.SemidirectActionCompatible (X := X) phi)
    (A : Subgroup E) :
    letI := restrictedAction (X := X) A
    Formalisation.SemidirectActionCompatible (X := X) (phi.comp A.subtype) := by
  intro a d x
  exact h a.val d x

/-- The elementwise stabiliser factorisation restricts to any subgroup. -/
theorem product_factorization_restrict (A : Subgroup E) (x : X)
    (h : ProductStabilizerFactorization (D := D) (E := E) x) :
    letI := restrictedAction (X := X) A
    ProductStabilizerFactorization (D := D) (E := A) x := by
  intro d a
  exact h d a.val

/-- The same restriction expressed in the semidirect product. -/
theorem semidirect_factorization_restrict (phi : E →* MulAut D)
    (compatible : Formalisation.SemidirectActionCompatible (X := X) phi)
    (A : Subgroup E) (x : X)
    (h : Formalisation.SemidirectStabilizerFactors phi compatible x) :
    letI := restrictedAction (X := X) A
    Formalisation.SemidirectStabilizerFactors (phi.comp A.subtype)
      (restricted_compatible phi compatible A) x := by
  letI := restrictedAction (X := X) A
  apply (semidirectStabilizerFactors_iff_productStabilizerFactorization
    (phi.comp A.subtype) (restricted_compatible phi compatible A) x).mpr
  exact product_factorization_restrict A x
    ((semidirectStabilizerFactors_iff_productStabilizerFactorization
      phi compatible x).mp h)

/-- The stabiliser inside `A` is the inverse image of the full stabiliser. -/
theorem restricted_stabilizer (A : Subgroup E) (x : X) :
    letI := restrictedAction (X := X) A
    MulAction.stabilizer A x = (MulAction.stabilizer E x).comap A.subtype := by
  rfl

/-- The image of the restricted stabiliser in the original acting group is the
intersection of the two subgroups. -/
theorem restricted_stabilizer_image (A : Subgroup E) (x : X) :
    letI := restrictedAction (X := X) A
    (MulAction.stabilizer A x).map A.subtype = A ⊓ MulAction.stabilizer E x := by
  letI := restrictedAction (X := X) A
  ext e
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.property, ha⟩
  · rintro ⟨ha, he⟩
    exact ⟨⟨e, ha⟩, he, rfl⟩

end Actions

section SemidirectInclusions

variable {G E : Type*} [Group G] [Group E]

/-- The inclusion of semidirect products induced by `A ≤ B`. -/
def semidirectInclusion (phi : E →* MulAut G)
    (A B : Subgroup E) (hAB : A ≤ B) :
    (G ⋊[phi.comp A.subtype] A) →* (G ⋊[phi.comp B.subtype] B) :=
  SemidirectProduct.map (MonoidHom.id G) (Subgroup.inclusion hAB) (by
    intro a
    rfl)

@[simp] theorem semidirectInclusion_inl (phi : E →* MulAut G)
    (A B : Subgroup E) (hAB : A ≤ B) (g : G) :
    semidirectInclusion phi A B hAB (SemidirectProduct.inl g) =
      SemidirectProduct.inl g := rfl

/-- The square on the original group commutes as homomorphisms. -/
theorem semidirectInclusion_comp_inl (phi : E →* MulAut G)
    (A B : Subgroup E) (hAB : A ≤ B) :
    (semidirectInclusion phi A B hAB).comp SemidirectProduct.inl =
      SemidirectProduct.inl := rfl

end SemidirectInclusions

section Extensions

variable {k G E V : Type*} [Field k] [Group G] [Group E]
  [AddCommGroup V] [Module k V]

/-- An extension to the stated semidirect product, with the specified base
representation and left inclusion. -/
structure SemidirectExtension (phi : E →* MulAut G)
    (A : Subgroup E) (rho : Representation k G V) where
  representation : Representation k (G ⋊[phi.comp A.subtype] A) V
  restrictionEquiv : Representation.Equiv
    (representation.pullback SemidirectProduct.inl) rho

/-- Pull back the extension along the commuting square. Its restriction remains
equivalent to the original base representation. -/
def SemidirectExtension.restrict {phi : E →* MulAut G}
    {A B : Subgroup E} {rho : Representation k G V}
    (W : SemidirectExtension phi B rho) (hAB : A ≤ B) :
    SemidirectExtension phi A rho where
  representation := W.representation.pullback (semidirectInclusion phi A B hAB)
  restrictionEquiv := W.restrictionEquiv

@[simp] theorem SemidirectExtension.restrict_apply {phi : E →* MulAut G}
    {A B : Subgroup E} {rho : Representation k G V}
    (W : SemidirectExtension phi B rho) (hAB : A ≤ B)
    (g : G ⋊[phi.comp A.subtype] A) :
    (W.restrict hAB).representation g =
      W.representation (semidirectInclusion phi A B hAB g) := rfl

/-- Irreducibility follows from the same irreducible base representation. No
cyclic extension theorem is used in this restriction. -/
theorem SemidirectExtension.isIrreducible {phi : E →* MulAut G}
    {A : Subgroup E} {rho : Representation k G V}
    (W : SemidirectExtension phi A rho)
    (hirr : Representation.IsIrreducible rho) :
    Representation.IsIrreducible W.representation := by
  letI : Representation.IsIrreducible rho := hirr
  letI : Nontrivial (Submodule k V) :=
    (Subrepresentation.toSubmodule_injective (ρ := rho)).nontrivial
  letI : Nontrivial V := (Submodule.nontrivial_iff k).mp inferInstance
  letI : Nontrivial (Subrepresentation W.representation) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    exact (bot_ne_top : (⊥ : Submodule k V) ≠ ⊤)
      (congrArg Subrepresentation.toSubmodule h)
  refine { eq_bot_or_eq_top := fun U ↦ ?_ }
  let Ubase : Subrepresentation rho := {
    toSubmodule := U.toSubmodule.map W.restrictionEquiv.toLinearMap
    apply_mem_toSubmodule := by
      intro g v hv
      obtain ⟨w, hw, rfl⟩ := hv
      refine ⟨W.representation (SemidirectProduct.inl g) w,
        U.apply_mem_toSubmodule (SemidirectProduct.inl g) hw, ?_⟩
      exact DFunLike.congr_fun (W.restrictionEquiv.isIntertwining' g) w }
  rcases eq_bot_or_eq_top Ubase with hbot | htop
  · left
    apply Subrepresentation.toSubmodule_injective
    have hmap : U.toSubmodule.map W.restrictionEquiv.toLinearMap = ⊥ := by
      change Ubase.toSubmodule = ⊥
      rw [hbot]
      rfl
    exact (Submodule.map_eq_bot_iff (e := W.restrictionEquiv.toLinearEquiv)).mp hmap
  · right
    apply Subrepresentation.toSubmodule_injective
    have hmap : U.toSubmodule.map W.restrictionEquiv.toLinearMap = ⊤ := by
      change Ubase.toSubmodule = ⊤
      rw [htop]
      rfl
    exact (Submodule.map_eq_top_iff (e := W.restrictionEquiv.toLinearEquiv)).mp hmap

end Extensions

end ManuscriptIBAW.Jordan

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
