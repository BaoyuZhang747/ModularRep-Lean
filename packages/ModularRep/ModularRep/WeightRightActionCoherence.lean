import ModularRep.WeightTransport

/-!
# Coherence of the manuscript right action on representation weights

This file checks the composition law behind the direct automorphism transport
on local normaliser quotients.  It is the concrete orientation used by
`RepresentationWeight.rightTwist`.  It then passes to isomorphism classes of
the local representations, quotients by ambient conjugation, and constructs
the resulting automorphism action on conjugacy classes of representation
weights.
-/

namespace ModularRep

universe u v

variable {G : Type v} [Group G]

/-- The direct local quotient maps compose in the manuscript's right-action
order.  The only cast identifies the two extensionally equal inverse-image
subgroups. -/
theorem rightNormalizerQuotientEquiv_mul
    (Q : Subgroup G) (alpha beta : MulAut G) :
    let hQ :
        (Q.comap alpha.toMonoidHom).comap beta.toMonoidHom =
          Q.comap (alpha * beta).toMonoidHom := by
      simp only [Subgroup.comap_comap]
      rfl
    (rightNormalizerQuotientEquiv beta
        (Q.comap alpha.toMonoidHom)).trans
        (rightNormalizerQuotientEquiv alpha Q) =
      (MulEquiv.cast
          (M := fun R : Subgroup G ↦ NormalizerQuotient R) hQ).trans
        (rightNormalizerQuotientEquiv (alpha * beta) Q) := by
  dsimp
  ext x
  refine Quotient.inductionOn x ?_
  intro x
  rfl

/-- The direct local quotient map for the identity automorphism is the
identity map, after the literal identification of the inverse-image
subgroup. -/
theorem rightNormalizerQuotientEquiv_one (Q : Subgroup G) :
    let hQ : Q.comap (1 : MulAut G).toMonoidHom = Q := by
      rfl
    rightNormalizerQuotientEquiv (1 : MulAut G) Q =
      MulEquiv.cast
        (M := fun R : Subgroup G ↦ NormalizerQuotient R) hQ := by
  dsimp
  ext x
  refine Quotient.inductionOn x ?_
  intro x
  rfl

namespace RepresentationWeight

open CategoryTheory Module

variable {p : ℕ} {K : Type u} [Field K] [CharZero K] [Finite G]

/-- Transport a local representation along a literal equality of its radical
subgroup.  This is the dependent cast needed to compare weights before taking
isomorphism classes. -/
def castLocalRepresentation {Q R : Subgroup G} (h : Q = R)
    (V : FDRep K (NormalizerQuotient Q)) :
    FDRep K (NormalizerQuotient R) := by
  subst R
  exact V

/-- An isomorphism of local representations remains an isomorphism after
transport along a subgroup equality. -/
noncomputable def castLocalRepresentationIso {Q R : Subgroup G}
    (h : Q = R) {V V' : FDRep K (NormalizerQuotient Q)} (i : V ≅ V') :
    castLocalRepresentation h V ≅ castLocalRepresentation h V' := by
  subst R
  exact i

/-- Transport along an equality and then its inverse is canonically
isomorphic to the original local representation. -/
noncomputable def castLocalRepresentation_symmIso {Q R : Subgroup G}
    (h : Q = R) (V : FDRep K (NormalizerQuotient Q)) :
    castLocalRepresentation h.symm (castLocalRepresentation h V) ≅ V := by
  subst R
  exact Iso.refl _

/-- Transport along two subgroup equalities agrees, up to the canonical
isomorphism, with transport along their composite. -/
noncomputable def castLocalRepresentation_transIso
    {Q R S : Subgroup G} (h : Q = R) (h' : R = S)
    (V : FDRep K (NormalizerQuotient Q)) :
    castLocalRepresentation (h.trans h') V ≅
      castLocalRepresentation h' (castLocalRepresentation h V) := by
  subst R
  subst S
  exact Iso.refl _

/-- Dependent transport cancels pullback along the quotient equivalence
induced by the same subgroup equality. -/
noncomputable def castLocalRepresentation_fdRepCast_symmIso
    {Q R : Subgroup G} (h : Q = R)
    (V : FDRep K (NormalizerQuotient R)) :
    castLocalRepresentation h
        (fdRepMapEquiv
          (MulEquiv.cast
            (M := fun S : Subgroup G ↦ NormalizerQuotient S) h).symm V) ≅
      V := by
  subst R
  exact (Action.resId (FGModuleCat K)).app V

/-- Two representation weights are isomorphic when their radical subgroups
are equal and, after the resulting dependent cast, their local
representations are isomorphic.  Proof fields in `RepresentationWeight` are
therefore ignored, but neither the subgroup nor the representation class is
discarded. -/
def Isomorphic (W W' : RepresentationWeight p K G) : Prop :=
  ∃ h : W.subgroup = W'.subgroup,
    Nonempty
      (castLocalRepresentation h W.localRepresentation ≅
        W'.localRepresentation)

theorem isomorphic_refl (W : RepresentationWeight p K G) :
    Isomorphic W W := by
  exact ⟨rfl, ⟨Iso.refl _⟩⟩

theorem isomorphic_symm {W W' : RepresentationWeight p K G}
    (h : Isomorphic W W') : Isomorphic W' W := by
  rcases h with ⟨hQ, ⟨i⟩⟩
  refine ⟨hQ.symm, ⟨?_⟩⟩
  exact (castLocalRepresentationIso hQ.symm i.symm).trans
    (castLocalRepresentation_symmIso hQ W.localRepresentation)

theorem isomorphic_trans {W W' W'' : RepresentationWeight p K G}
    (h : Isomorphic W W') (h' : Isomorphic W' W'') :
    Isomorphic W W'' := by
  rcases h with ⟨hQ, ⟨i⟩⟩
  rcases h' with ⟨hQ', ⟨i'⟩⟩
  refine ⟨hQ.trans hQ', ⟨?_⟩⟩
  exact (castLocalRepresentation_transIso hQ hQ'
    W.localRepresentation).trans
      ((castLocalRepresentationIso hQ' i).trans i')

/-- Isomorphism of representation weights is an equivalence relation. -/
@[instance_reducible]
def isomorphicSetoid : Setoid (RepresentationWeight p K G) where
  r := Isomorphic
  iseqv := ⟨isomorphic_refl, isomorphic_symm, isomorphic_trans⟩

/-- Representation weights modulo equality of the radical subgroup and
isomorphism of the local representation. -/
abbrev IsoClass := Quotient (isomorphicSetoid (p := p) (K := K) (G := G))

/-- Automorphism transport preserves isomorphism after the necessary
dependent subgroup cast.  This is the concrete functoriality needed to
descend `rightTwist` to weight isomorphism classes. -/
noncomputable def rightTwist_localRepresentation_iso_of_iso
    {Q R : Subgroup G} (hQ : Q = R)
    {V : FDRep K (NormalizerQuotient Q)}
    {V' : FDRep K (NormalizerQuotient R)}
    (i : castLocalRepresentation hQ V ≅ V') (alpha : MulAut G) :
    let hQalpha : Q.comap alpha.toMonoidHom =
        R.comap alpha.toMonoidHom := congrArg
      (fun S : Subgroup G ↦ S.comap alpha.toMonoidHom) hQ
    castLocalRepresentation hQalpha
        (fdRepMapEquiv
          (rightNormalizerQuotientEquiv alpha Q).symm V) ≅
      fdRepMapEquiv
        (rightNormalizerQuotientEquiv alpha R).symm V' := by
  subst R
  exact (Action.res (FGModuleCat K)
    (rightNormalizerQuotientEquiv alpha Q).toMonoidHom).mapIso i

/-- Right automorphism transport respects isomorphism of representation
weights. -/
theorem rightTwist_isomorphic {W W' : RepresentationWeight p K G}
    (h : Isomorphic W W') (alpha : MulAut G) :
    Isomorphic (W.rightTwist alpha) (W'.rightTwist alpha) := by
  rcases h with ⟨hQ, ⟨i⟩⟩
  refine ⟨congrArg
    (fun S : Subgroup G ↦ S.comap alpha.toMonoidHom) hQ, ⟨?_⟩⟩
  exact rightTwist_localRepresentation_iso_of_iso hQ i alpha

/-- Right transport by a fixed automorphism on weight isomorphism classes. -/
noncomputable def rightTwistIsoClass (alpha : MulAut G) :
    IsoClass (p := p) (K := K) (G := G) →
      IsoClass (p := p) (K := K) (G := G) :=
  Quotient.map (fun W ↦ W.rightTwist alpha)
    (fun _ _ h ↦ rightTwist_isomorphic h alpha)

/-- The identity automorphism gives an isomorphic representation weight. -/
noncomputable def rightTwist_one_localRepresentation_iso
    (W : RepresentationWeight p K G) :
    let hQ : (W.rightTwist (1 : MulAut G)).subgroup = W.subgroup := by
      rfl
    castLocalRepresentation hQ
        (W.rightTwist (1 : MulAut G)).localRepresentation ≅
      W.localRepresentation := by
  change fdRepMapEquiv
      (rightNormalizerQuotientEquiv (1 : MulAut G) W.subgroup).symm
        W.localRepresentation ≅ W.localRepresentation
  rw [rightNormalizerQuotientEquiv_one]
  exact (Action.resId (FGModuleCat K)).app W.localRepresentation

/-- Identity law for right automorphism transport, stated at the honest
isomorphism-class endpoint. -/
theorem rightTwist_one_isomorphic (W : RepresentationWeight p K G) :
    Isomorphic (W.rightTwist (1 : MulAut G)) W := by
  exact ⟨rfl, ⟨rightTwist_one_localRepresentation_iso W⟩⟩

@[simp]
theorem rightTwistIsoClass_one
    (x : IsoClass (p := p) (K := K) (G := G)) :
    rightTwistIsoClass (p := p) (K := K) (G := G) (1 : MulAut G) x = x := by
  refine Quotient.inductionOn x ?_
  intro W
  exact Quotient.sound (rightTwist_one_isomorphic W)

/-- Successive right twists have canonically isomorphic local
representations to the single twist by the product automorphism, after the
literal cast between the two equal inverse-image subgroups. -/
noncomputable def rightTwist_localRepresentation_mulIso
    (W : RepresentationWeight p K G) (alpha beta : MulAut G) :
    let hQ :
        (W.subgroup.comap alpha.toMonoidHom).comap beta.toMonoidHom =
          W.subgroup.comap (alpha * beta).toMonoidHom := by
      simp only [Subgroup.comap_comap]
      rfl
    let castQ :
        NormalizerQuotient
            ((W.subgroup.comap alpha.toMonoidHom).comap beta.toMonoidHom) ≃*
          NormalizerQuotient
            (W.subgroup.comap (alpha * beta).toMonoidHom) :=
      MulEquiv.cast
        (M := fun R : Subgroup G ↦ NormalizerQuotient R) hQ
    ((W.rightTwist alpha).rightTwist beta).localRepresentation ≅
      fdRepMapEquiv castQ.symm
        (W.rightTwist (alpha * beta)).localRepresentation := by
  dsimp
  let eAlpha := rightNormalizerQuotientEquiv alpha W.subgroup
  let eBeta := rightNormalizerQuotientEquiv beta
    (W.subgroup.comap alpha.toMonoidHom)
  let eProduct := rightNormalizerQuotientEquiv (alpha * beta) W.subgroup
  let hQ :
      (W.subgroup.comap alpha.toMonoidHom).comap beta.toMonoidHom =
        W.subgroup.comap (alpha * beta).toMonoidHom := by
    simp only [Subgroup.comap_comap]
    rfl
  let castQ :
      NormalizerQuotient
          ((W.subgroup.comap alpha.toMonoidHom).comap beta.toMonoidHom) ≃*
        NormalizerQuotient
          (W.subgroup.comap (alpha * beta).toMonoidHom) :=
    MulEquiv.cast
      (M := fun R : Subgroup G ↦ NormalizerQuotient R) hQ
  have hcomp : eBeta.trans eAlpha = castQ.trans eProduct := by
    exact rightNormalizerQuotientEquiv_mul W.subgroup alpha beta
  have hinv : eAlpha.symm.trans eBeta.symm =
      eProduct.symm.trans castQ.symm := by
    ext x
    exact congrArg (fun e ↦ e.symm x) hcomp
  let first := fdRepMapEquiv_transIso eAlpha.symm eBeta.symm
    W.localRepresentation
  let second := fdRepMapEquiv_transIso eProduct.symm castQ.symm
    W.localRepresentation
  have first' :
      fdRepMapEquiv eBeta.symm
          (fdRepMapEquiv eAlpha.symm W.localRepresentation) ≅
        fdRepMapEquiv (eProduct.symm.trans castQ.symm)
          W.localRepresentation := by
    simpa only [hinv] using first
  exact first'.trans second.symm

/-- Successive right twists are isomorphic to the twist by the product
automorphism.  Unlike `rightTwist_localRepresentation_mulIso`, this statement
also performs the dependent cast of the radical subgroup and therefore lies
exactly in the weight-isomorphism relation. -/
theorem rightTwist_mul_isomorphic
    (W : RepresentationWeight p K G) (alpha beta : MulAut G) :
    Isomorphic ((W.rightTwist alpha).rightTwist beta)
      (W.rightTwist (alpha * beta)) := by
  let hQ :
      ((W.subgroup.comap alpha.toMonoidHom).comap beta.toMonoidHom) =
        W.subgroup.comap (alpha * beta).toMonoidHom := by
    simp only [Subgroup.comap_comap]
    rfl
  let i := rightTwist_localRepresentation_mulIso W alpha beta
  refine ⟨hQ, ⟨?_⟩⟩
  exact (castLocalRepresentationIso hQ i).trans
    (castLocalRepresentation_fdRepCast_symmIso hQ
      (W.rightTwist (alpha * beta)).localRepresentation)

/-- Composition law for the manuscript right action on weight isomorphism
classes. -/
theorem rightTwistIsoClass_mul
    (x : IsoClass (p := p) (K := K) (G := G))
    (alpha beta : MulAut G) :
    rightTwistIsoClass (p := p) (K := K) (G := G) beta
        (rightTwistIsoClass (p := p) (K := K) (G := G) alpha x) =
      rightTwistIsoClass (p := p) (K := K) (G := G) (alpha * beta) x := by
  refine Quotient.inductionOn x ?_
  intro W
  exact Quotient.sound (rightTwist_mul_isomorphic W alpha beta)

/-- Lean's left-action interface for the manuscript right action.  The
opposite automorphism group makes `(W ^ alpha) ^ beta = W ^ (alpha * beta)`
the ordinary `mul_smul` law. -/
noncomputable instance isoClassMulAction :
    MulAction (MulAut G)ᵐᵒᵖ
      (IsoClass (p := p) (K := K) (G := G)) where
  smul alpha x := rightTwistIsoClass
    (p := p) (K := K) (G := G) alpha.unop x
  one_smul x := rightTwistIsoClass_one x
  mul_smul alpha beta x := by
    exact (rightTwistIsoClass_mul x beta.unop alpha.unop).symm

/-- The left conjugation action on weight isomorphism classes, expressed via
the manuscript right automorphism action.  The inverse makes the radical
subgroup move from `Q` to `gQg⁻¹`. -/
def innerInverseOpHom : G →* (MulAut G)ᵐᵒᵖ where
  toFun g := MulOpposite.op (MulAut.conj g⁻¹)
  map_one' := by simp
  map_mul' g h := by
    apply MulOpposite.unop_injective
    ext x
    simp [mul_assoc]

noncomputable instance isoClassConjugationMulAction :
    MulAction G (IsoClass (p := p) (K := K) (G := G)) :=
  MulAction.compHom _ (innerInverseOpHom (G := G))

/-- Isomorphism classes of representation weights modulo conjugation by the
ambient group.  This is the representation theoretic carrier corresponding
to the manuscript's set of conjugacy classes of weights. -/
abbrev ConjugacyClass := MulAction.orbitRel.Quotient G
  (IsoClass (p := p) (K := K) (G := G))

/-- Automorphism transport carries a conjugate weight to the corresponding
conjugate of the transported weight. -/
theorem rightTwistIsoClass_conjugation
    (alpha : MulAut G) (g : G)
    (x : IsoClass (p := p) (K := K) (G := G)) :
    rightTwistIsoClass (p := p) (K := K) (G := G) alpha (g • x) =
      alpha.symm g •
        rightTwistIsoClass (p := p) (K := K) (G := G) alpha x := by
  change rightTwistIsoClass alpha
      (rightTwistIsoClass (MulAut.conj g⁻¹) x) =
    rightTwistIsoClass (MulAut.conj (alpha.symm g)⁻¹)
      (rightTwistIsoClass alpha x)
  rw [rightTwistIsoClass_mul, rightTwistIsoClass_mul]
  congr 1
  ext y
  simp [mul_assoc]

/-- Right automorphism transport descends from weight isomorphism classes to
ambient conjugacy classes. -/
noncomputable def rightTwistConjugacyClass (alpha : MulAut G) :
    ConjugacyClass (p := p) (K := K) (G := G) →
      ConjugacyClass (p := p) (K := K) (G := G) :=
  Quotient.map
    (rightTwistIsoClass (p := p) (K := K) (G := G) alpha) (by
      intro x y hxy
      rcases hxy with ⟨g, rfl⟩
      exact ⟨alpha.symm g,
        (rightTwistIsoClass_conjugation alpha g y).symm⟩)

@[simp]
theorem rightTwistConjugacyClass_one
    (x : ConjugacyClass (p := p) (K := K) (G := G)) :
    rightTwistConjugacyClass (p := p) (K := K) (G := G)
      (1 : MulAut G) x = x := by
  refine Quotient.inductionOn x ?_
  intro W
  exact congrArg
    (fun z : IsoClass (p := p) (K := K) (G := G) ↦
      (Quotient.mk'' z : ConjugacyClass (p := p) (K := K) (G := G)))
    (rightTwistIsoClass_one W)

/-- The manuscript right-action composition law on conjugacy classes of
representation weights. -/
theorem rightTwistConjugacyClass_mul
    (x : ConjugacyClass (p := p) (K := K) (G := G))
    (alpha beta : MulAut G) :
    rightTwistConjugacyClass (p := p) (K := K) (G := G) beta
        (rightTwistConjugacyClass (p := p) (K := K) (G := G) alpha x) =
      rightTwistConjugacyClass (p := p) (K := K) (G := G)
        (alpha * beta) x := by
  refine Quotient.inductionOn x ?_
  intro W
  exact congrArg
    (fun z : IsoClass (p := p) (K := K) (G := G) ↦
      (Quotient.mk'' z : ConjugacyClass (p := p) (K := K) (G := G)))
    (rightTwistIsoClass_mul W alpha beta)

/-- The actual automorphism action on ambient conjugacy classes of
representation weights. -/
noncomputable instance conjugacyClassMulAction :
    MulAction (MulAut G)ᵐᵒᵖ
      (ConjugacyClass (p := p) (K := K) (G := G)) where
  smul alpha x := rightTwistConjugacyClass
    (p := p) (K := K) (G := G) alpha.unop x
  one_smul x := rightTwistConjugacyClass_one x
  mul_smul alpha beta x := by
    exact (rightTwistConjugacyClass_mul x beta.unop alpha.unop).symm

end RepresentationWeight

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
