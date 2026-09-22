import ModularRep.BlockInduction
import ModularRep.BlockIdempotentDecompositionEquivTransport

/-!
# Covering calculations for central characters

This file supplies the coefficient-level calculation behind transitivity of
block covering through an intersection.  Covering is expressed solely as an
equality of central characters on central group algebra elements supported on
the subgroup.  The main theorem pastes a local covering equality into two
defined induced central characters.

No concrete block catalogue, Brauer map, or block-theoretic definedness
theorem is introduced here.  The generic transport theorem is conditional on
explicit local and ambient central character matches.  Source adapters must
justify those matches and identify the relevant central characters with
actual blocks.
-/

namespace ModularRep

open scoped MonoidAlgebra

noncomputable section

/-- Transport the centre of a group algebra along a multiplicative
equivalence of the indexing monoids. -/
def centerDomCongr
    {k G G' : Type*} [CommSemiring k] [Monoid G] [Monoid G']
    (e : G ≃* G') :
    GroupAlgebraCenter k G ≃ₐ[k] GroupAlgebraCenter k G' where
  toRingEquiv :=
    Subsemiring.centerCongr
      (MonoidAlgebra.domCongr k k e).toRingEquiv
  commutes' r := by
    apply Subtype.ext
    change MonoidAlgebra.domCongr k k e
      (algebraMap k k[G] r) = algebraMap k k[G'] r
    exact (MonoidAlgebra.domCongr k k e).commutes r

@[simp]
theorem centerDomCongr_coe
    {k G G' : Type*} [CommSemiring k] [Monoid G] [Monoid G']
    (e : G ≃* G') (z : GroupAlgebraCenter k G) :
    ((centerDomCongr (k := k) e z :
        GroupAlgebraCenter k G') : k[G']) =
      MonoidAlgebra.domCongr k k e (z : k[G]) :=
  rfl

/-- Covariant transport of a central character.  A character on the source
centre becomes one on the target centre by precomposition with the inverse
centre equivalence. -/
def centralCharacterAlongMulEquiv
    {k G G' : Type*} [CommSemiring k] [Monoid G] [Monoid G']
    (e : G ≃* G')
    (lambda : GroupAlgebraCenter k G →ₐ[k] k) :
    GroupAlgebraCenter k G' →ₐ[k] k :=
  lambda.comp (centerDomCongr (k := k) e).symm.toAlgHom

@[simp]
theorem centralCharacterAlongMulEquiv_apply
    {k G G' : Type*} [CommSemiring k] [Monoid G] [Monoid G']
    (e : G ≃* G')
    (lambda : GroupAlgebraCenter k G →ₐ[k] k)
    (z : GroupAlgebraCenter k G') :
    centralCharacterAlongMulEquiv e lambda z =
      lambda ((centerDomCongr (k := k) e).symm z) :=
  rfl

namespace BlockIdempotentDecomposition

/-- Transporting a centred block idempotent agrees with centring the
transported decomposition. -/
@[simp]
theorem centerDomCongr_blockIdempotentInCenter_alongMulEquiv
    {k G G' Block : Type*}
    [Field k] [Group G] [Group G'] [Fintype Block]
    {blockIdempotent : Block → k[G]}
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (e : G ≃* G') (B : Block) :
    centerDomCongr (k := k) e (blocks.blockIdempotentInCenter B) =
      (blocks.alongMulEquiv e).blockIdempotentInCenter B := by
  apply Subtype.ext
  rfl

end BlockIdempotentDecomposition

namespace BlockCentralCharacterCatalogue

/-- Transport a complete catalogue of block central characters along an
equivalence of the underlying groups. -/
def alongMulEquiv
    {k G G' Block : Type*}
    [Field k] [IsAlgClosed k]
    [Group G] [Fintype G] [Group G'] [Fintype G'] [Fintype Block]
    {blockIdempotent : Block → k[G]}
    {blocks : BlockIdempotentDecomposition blockIdempotent}
    (catalogue : BlockCentralCharacterCatalogue blocks)
    (e : G ≃* G') :
    BlockCentralCharacterCatalogue (blocks.alongMulEquiv e) where
  centralCharacter B :=
    centralCharacterAlongMulEquiv e (catalogue.centralCharacter B)
  delta_own B := by
    change catalogue.centralCharacter B
      ((centerDomCongr (k := k) e).symm
        ((blocks.alongMulEquiv e).blockIdempotentInCenter B)) = 1
    rw [← blocks.centerDomCongr_blockIdempotentInCenter_alongMulEquiv e B,
      AlgEquiv.symm_apply_apply]
    exact catalogue.delta_own B
  delta_other B C hBC := by
    change catalogue.centralCharacter B
      ((centerDomCongr (k := k) e).symm
        ((blocks.alongMulEquiv e).blockIdempotentInCenter C)) = 0
    rw [← blocks.centerDomCongr_blockIdempotentInCenter_alongMulEquiv e C,
      AlgEquiv.symm_apply_apply]
    exact catalogue.delta_other B C hBC
  exhaustive := by
    intro lambda
    obtain ⟨B, hB⟩ := catalogue.exhaustive
      (lambda.comp (centerDomCongr (k := k) e).toAlgHom)
    refine ⟨B, ?_⟩
    ext z
    change catalogue.centralCharacter B
      ((centerDomCongr (k := k) e).symm z) = lambda z
    rw [hB]
    change lambda
      (centerDomCongr (k := k) e
        ((centerDomCongr (k := k) e).symm z)) = lambda z
    rw [AlgEquiv.apply_symm_apply]

end BlockCentralCharacterCatalogue

/-- A central group algebra element whose coefficients vanish outside `L`. -/
def CentralElementSupportedOn
    {k G : Type*} [CommSemiring k] [Group G]
    (L : Subgroup G) (z : GroupAlgebraCenter k G) : Prop :=
  ∀ g : G, g ∉ L → (z : k[G]).coeff g = 0

/-- Character-level covering.  The ambient character is followed by the
character on the subgroup. -/
def CentralCharacterCovers
    {k G : Type*} [CommSemiring k] [Group G]
    (L : Subgroup G)
    (lambdaG : GroupAlgebraCenter k G →ₐ[k] k)
    (lambdaL : GroupAlgebraCenter k L →ₐ[k] k) : Prop :=
  ∀ z : GroupAlgebraCenter k G,
    CentralElementSupportedOn L z →
      lambdaG z = lambdaL (centerCoeffRestrict L z)

/-- The two subtype presentations of an intersection are multiplicatively
equivalent.  The source presents the intersection inside `H`, and the target
presents it inside `K`. -/
def subgroupIntersectionEquiv
    {G : Type*} [Group G] (H K : Subgroup G) :
    K.comap H.subtype ≃* H.comap K.subtype where
  toFun x :=
    ⟨⟨((x : H) : G), x.property⟩, (x : H).property⟩
  invFun x :=
    ⟨⟨((x : K) : G), x.property⟩, (x : K).property⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_mul' x y := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

@[simp]
theorem subgroupIntersectionEquiv_coe
    {G : Type*} [Group G] (H K : Subgroup G)
    (x : K.comap H.subtype) :
    ((((subgroupIntersectionEquiv H K) x :
        H.comap K.subtype) : K) : G) =
      ((x : H) : G) :=
  rfl

@[simp]
theorem subgroupIntersectionEquiv_symm_coe
    {G : Type*} [Group G] (H K : Subgroup G)
    (x : H.comap K.subtype) :
    ((((subgroupIntersectionEquiv H K).symm x :
        K.comap H.subtype) : H) : G) =
      ((x : K) : G) :=
  rfl

/-- Coefficient restriction is natural under a commuting square of subgroup
inclusions and multiplicative equivalences. -/
theorem coeffRestrict_domCongr
    {k G G' : Type*} [CommSemiring k] [Group G] [Group G']
    (H : Subgroup G) (H' : Subgroup G')
    (eG : G ≃* G') (eH : H ≃* H')
    (hsquare :
      eG.toMonoidHom.comp H.subtype =
        H'.subtype.comp eH.toMonoidHom)
    (z : k[G]) :
    coeffRestrict H' (MonoidAlgebra.domCongr k k eG z) =
      MonoidAlgebra.domCongr k k eH (coeffRestrict H z) := by
  ext h'
  simp only [coeffRestrict_apply, MonoidAlgebra.coeff_domCongr]
  apply congrArg (fun g : G => z.coeff g)
  apply eG.injective
  rw [eG.apply_symm_apply]
  have hpoint :
      eG (((eH.symm h' : H) : G)) = (h' : G') := by
    have h := congrArg
      (fun f : H →* G' => f (eH.symm h')) hsquare
    simpa using h
  exact hpoint.symm

/-- Centre-valued coefficient restriction is natural under the same
commuting square. -/
theorem centerCoeffRestrict_centerDomCongr
    {k G G' : Type*} [CommSemiring k] [Group G] [Group G']
    (H : Subgroup G) (H' : Subgroup G')
    (eG : G ≃* G') (eH : H ≃* H')
    (hsquare :
      eG.toMonoidHom.comp H.subtype =
        H'.subtype.comp eH.toMonoidHom)
    (z : GroupAlgebraCenter k G) :
    centerCoeffRestrict H' (centerDomCongr (k := k) eG z) =
      centerDomCongr (k := k) eH (centerCoeffRestrict H z) := by
  apply Subtype.ext
  change coeffRestrict H'
      (MonoidAlgebra.domCongr k k eG (z : k[G])) =
    MonoidAlgebra.domCongr k k eH
      (coeffRestrict H (z : k[G]))
  exact coeffRestrict_domCongr H H' eG eH hsquare (z : k[G])

/-- Evaluating an induced central function after transporting both the
ambient group and the subgroup gives its original value. -/
theorem inducedCentralFunction_centerDomCongr
    {k G G' : Type*} [CommSemiring k] [Group G] [Group G']
    (H : Subgroup G) (H' : Subgroup G')
    (eG : G ≃* G') (eH : H ≃* H')
    (hsquare :
      eG.toMonoidHom.comp H.subtype =
        H'.subtype.comp eH.toMonoidHom)
    (lambda : GroupAlgebraCenter k H →ₐ[k] k)
    (z : GroupAlgebraCenter k G) :
    inducedCentralFunction H'
        (centralCharacterAlongMulEquiv eH lambda)
        (centerDomCongr (k := k) eG z) =
      inducedCentralFunction H lambda z := by
  rw [inducedCentralFunction_apply, inducedCentralFunction_apply,
    centerCoeffRestrict_centerDomCongr H H' eG eH hsquare]
  simp only [centralCharacterAlongMulEquiv_apply,
    AlgEquiv.symm_apply_apply]

/-- Pointwise form of transport naturality for induced central functions. -/
theorem inducedCentralFunction_alongMulEquiv
    {k G G' : Type*} [CommSemiring k] [Group G] [Group G']
    (H : Subgroup G) (H' : Subgroup G')
    (eG : G ≃* G') (eH : H ≃* H')
    (hsquare :
      eG.toMonoidHom.comp H.subtype =
        H'.subtype.comp eH.toMonoidHom)
    (lambda : GroupAlgebraCenter k H →ₐ[k] k)
    (z' : GroupAlgebraCenter k G') :
    inducedCentralFunction H'
        (centralCharacterAlongMulEquiv eH lambda) z' =
      inducedCentralFunction H lambda
        ((centerDomCongr (k := k) eG).symm z') := by
  calc
    inducedCentralFunction H'
        (centralCharacterAlongMulEquiv eH lambda) z' =
      inducedCentralFunction H'
        (centralCharacterAlongMulEquiv eH lambda)
        (centerDomCongr (k := k) eG
          ((centerDomCongr (k := k) eG).symm z')) := by
            rw [(centerDomCongr (k := k) eG).apply_symm_apply]
    _ = inducedCentralFunction H lambda
        ((centerDomCongr (k := k) eG).symm z') :=
      inducedCentralFunction_centerDomCongr
        H H' eG eH hsquare lambda _

/-- Definedness of block induction is preserved by a commuting square of
group equivalences. -/
theorem isBlockInductionDefined_alongMulEquiv
    {k G G' : Type*} [Field k] [Group G] [Group G']
    (H : Subgroup G) (H' : Subgroup G')
    (eG : G ≃* G') (eH : H ≃* H')
    (hsquare :
      eG.toMonoidHom.comp H.subtype =
        H'.subtype.comp eH.toMonoidHom)
    (lambda : GroupAlgebraCenter k H →ₐ[k] k)
    (hdefined : IsBlockInductionDefined H lambda) :
    IsBlockInductionDefined H'
      (centralCharacterAlongMulEquiv eH lambda) := by
  intro x y
  calc
    inducedCentralFunction H'
        (centralCharacterAlongMulEquiv eH lambda) (x * y) =
      inducedCentralFunction H lambda
        ((centerDomCongr (k := k) eG).symm (x * y)) :=
      inducedCentralFunction_alongMulEquiv
        H H' eG eH hsquare lambda _
    _ = inducedCentralFunction H lambda
        ((centerDomCongr (k := k) eG).symm x *
          (centerDomCongr (k := k) eG).symm y) := by
      rw [map_mul]
    _ = inducedCentralFunction H lambda
          ((centerDomCongr (k := k) eG).symm x) *
        inducedCentralFunction H lambda
          ((centerDomCongr (k := k) eG).symm y) :=
      hdefined _ _
    _ = inducedCentralFunction H'
          (centralCharacterAlongMulEquiv eH lambda) x *
        inducedCentralFunction H'
          (centralCharacterAlongMulEquiv eH lambda) y := by
      rw [inducedCentralFunction_alongMulEquiv
            H H' eG eH hsquare lambda x,
          inducedCentralFunction_alongMulEquiv
            H H' eG eH hsquare lambda y]

/-- The bundled induced central character is natural under a commuting
square of group equivalences. -/
theorem inducedCentralCharacter_alongMulEquiv
    {k G G' : Type*} [Field k] [Group G] [Group G']
    (H : Subgroup G) (H' : Subgroup G')
    (eG : G ≃* G') (eH : H ≃* H')
    (hsquare :
      eG.toMonoidHom.comp H.subtype =
        H'.subtype.comp eH.toMonoidHom)
    (lambda : GroupAlgebraCenter k H →ₐ[k] k)
    (hdefined : IsBlockInductionDefined H lambda) :
    inducedCentralCharacter H'
        (centralCharacterAlongMulEquiv eH lambda)
        (isBlockInductionDefined_alongMulEquiv
          H H' eG eH hsquare lambda hdefined) =
      centralCharacterAlongMulEquiv eG
        (inducedCentralCharacter H lambda hdefined) := by
  ext z'
  simpa only [inducedCentralCharacter_apply,
    centralCharacterAlongMulEquiv_apply] using
      inducedCentralFunction_alongMulEquiv
        H H' eG eH hsquare lambda z'

section BlockCentralCharacterTransport

variable {k G G' Block Block' : Type*}
variable [Field k] [IsAlgClosed k]
variable [Group G] [Fintype G] [Group G'] [Fintype G']
variable [Fintype Block] [Fintype Block']
variable {blockIdempotent : Block → k[G]}
variable {blockIdempotent' : Block' → k[G']}
variable {blocks : BlockIdempotentDecomposition blockIdempotent}
variable {blocks' : BlockIdempotentDecomposition blockIdempotent'}

/-- Matching one transported primitive block idempotent identifies the
corresponding transported central character. -/
theorem centralCharacterAlongMulEquiv_eq_of_blockIdempotent
    (e : G ≃* G')
    (catalogue : BlockCentralCharacterCatalogue blocks)
    (catalogue' : BlockCentralCharacterCatalogue blocks')
    {b : Block} {b' : Block'}
    (hmatch :
      centerDomCongr (k := k) e (blocks.blockIdempotentInCenter b) =
        blocks'.blockIdempotentInCenter b') :
    centralCharacterAlongMulEquiv e
        (catalogue.centralCharacter b) =
      catalogue'.centralCharacter b' := by
  obtain ⟨c, hc⟩ := catalogue'.exhaustive
    (centralCharacterAlongMulEquiv e
      (catalogue.centralCharacter b))
  have hvalue :
      catalogue'.centralCharacter c
          (blocks'.blockIdempotentInCenter b') = 1 := by
    rw [hc]
    simp only [centralCharacterAlongMulEquiv_apply]
    rw [← hmatch, AlgEquiv.symm_apply_apply]
    exact catalogue.centralCharacter_own b
  have hcb : c = b' := by
    by_contra hne
    have hzero := catalogue'.centralCharacter_other hne
    exact zero_ne_one (hzero.symm.trans hvalue)
  subst c
  exact hc.symm

end BlockCentralCharacterTransport

section BlockInductionTransport

variable {k G G' : Type*}
variable [Field k] [IsAlgClosed k]
variable [Group G] [Fintype G] [Group G'] [Fintype G']
variable (H : Subgroup G) (H' : Subgroup G')
local instance centralCharacterCoveringHFintype : Fintype H :=
  Fintype.ofFinite H
local instance centralCharacterCoveringHPrimeFintype : Fintype H' :=
  Fintype.ofFinite H'

variable {LocalBlock AmbientBlock LocalBlock' AmbientBlock' : Type*}
variable [Fintype LocalBlock] [Fintype AmbientBlock]
variable [Fintype LocalBlock'] [Fintype AmbientBlock']
variable {localBlockIdempotent : LocalBlock → k[H]}
variable {ambientBlockIdempotent : AmbientBlock → k[G]}
variable {localBlockIdempotent' : LocalBlock' → k[H']}
variable {ambientBlockIdempotent' : AmbientBlock' → k[G']}
variable {localBlocks :
  BlockIdempotentDecomposition localBlockIdempotent}
variable {ambientBlocks :
  BlockIdempotentDecomposition ambientBlockIdempotent}
variable {localBlocks' :
  BlockIdempotentDecomposition localBlockIdempotent'}
variable {ambientBlocks' :
  BlockIdempotentDecomposition ambientBlockIdempotent'}

/-- A block-induction relation transports across a commuting square once
the selected local and ambient central characters have been identified. -/
theorem blockInducesTo_alongMulEquiv
    (eG : G ≃* G') (eH : H ≃* H')
    (hsquare :
      eG.toMonoidHom.comp H.subtype =
        H'.subtype.comp eH.toMonoidHom)
    (localCatalogue : BlockCentralCharacterCatalogue localBlocks)
    (ambientCatalogue : BlockCentralCharacterCatalogue ambientBlocks)
    (localCatalogue' : BlockCentralCharacterCatalogue localBlocks')
    (ambientCatalogue' : BlockCentralCharacterCatalogue ambientBlocks')
    {b : LocalBlock} {B : AmbientBlock}
    {b' : LocalBlock'} {B' : AmbientBlock'}
    (hlocal :
      centralCharacterAlongMulEquiv eH
          (localCatalogue.centralCharacter b) =
        localCatalogue'.centralCharacter b')
    (hglobal :
      centralCharacterAlongMulEquiv eG
          (ambientCatalogue.centralCharacter B) =
        ambientCatalogue'.centralCharacter B')
    (hinduces :
      BlockInducesTo H localCatalogue ambientCatalogue b B) :
    BlockInducesTo H' localCatalogue' ambientCatalogue' b' B' := by
  obtain ⟨hdefined, hcharacter⟩ := hinduces
  have hdefinedTransport :
      IsBlockInductionDefined H'
        (centralCharacterAlongMulEquiv eH
          (localCatalogue.centralCharacter b)) :=
    isBlockInductionDefined_alongMulEquiv
      H H' eG eH hsquare
      (localCatalogue.centralCharacter b) hdefined
  have hdefined' :
      IsBlockInductionDefined H'
        (localCatalogue'.centralCharacter b') := by
    rw [← hlocal]
    exact hdefinedTransport
  refine ⟨hdefined', ?_⟩
  ext z'
  simp only [inducedCentralCharacter_apply]
  rw [← hlocal]
  calc
    inducedCentralFunction H'
        (centralCharacterAlongMulEquiv eH
          (localCatalogue.centralCharacter b)) z' =
      inducedCentralFunction H
        (localCatalogue.centralCharacter b)
        ((centerDomCongr (k := k) eG).symm z') :=
      inducedCentralFunction_alongMulEquiv
        H H' eG eH hsquare
        (localCatalogue.centralCharacter b) z'
    _ = ambientCatalogue.centralCharacter B
        ((centerDomCongr (k := k) eG).symm z') := by
      simpa only [inducedCentralCharacter_apply] using
        congrArg
          (fun f : GroupAlgebraCenter k G →ₐ[k] k =>
            f ((centerDomCongr (k := k) eG).symm z'))
          hcharacter
    _ = centralCharacterAlongMulEquiv eG
        (ambientCatalogue.centralCharacter B) z' :=
      (centralCharacterAlongMulEquiv_apply
        eG (ambientCatalogue.centralCharacter B) z').symm
    _ = ambientCatalogue'.centralCharacter B' z' :=
      congrArg
        (fun f : GroupAlgebraCenter k G' →ₐ[k] k => f z')
        hglobal

end BlockInductionTransport

/-- Restriction first to `H` and then to its intersection with `K` agrees,
up to the canonical intersection equivalence, with restriction in the other
order. -/
theorem coeffRestrict_subgroupIntersection
    {k G : Type*} [CommSemiring k] [Group G]
    (H K : Subgroup G) (z : k[G]) :
    MonoidAlgebra.domCongr k k (subgroupIntersectionEquiv H K)
        (coeffRestrict (K.comap H.subtype) (coeffRestrict H z)) =
      coeffRestrict (H.comap K.subtype) (coeffRestrict K z) := by
  ext x
  simp only [MonoidAlgebra.coeff_domCongr, coeffRestrict_apply,
    subgroupIntersectionEquiv_symm_coe]

/-- Centre-valued version of the subgroup-intersection restriction square. -/
theorem centerCoeffRestrict_subgroupIntersection
    {k G : Type*} [CommSemiring k] [Group G]
    (H K : Subgroup G) (z : GroupAlgebraCenter k G) :
    centerDomCongr (k := k) (subgroupIntersectionEquiv H K)
        (centerCoeffRestrict (K.comap H.subtype)
          (centerCoeffRestrict H z)) =
      centerCoeffRestrict (H.comap K.subtype)
        (centerCoeffRestrict K z) := by
  apply Subtype.ext
  change
    MonoidAlgebra.domCongr k k (subgroupIntersectionEquiv H K)
        (coeffRestrict (K.comap H.subtype)
          (coeffRestrict H (z : k[G]))) =
      coeffRestrict (H.comap K.subtype)
        (coeffRestrict K (z : k[G]))
  exact coeffRestrict_subgroupIntersection H K (z : k[G])

/-- Support in `K` descends to support in the intersection after coefficient
restriction to `H`. -/
theorem centralElementSupportedOn_centerCoeffRestrict
    {k G : Type*} [CommSemiring k] [Group G]
    (H K : Subgroup G) {z : GroupAlgebraCenter k G}
    (hz : CentralElementSupportedOn K z) :
    CentralElementSupportedOn (K.comap H.subtype)
      (centerCoeffRestrict H z) := by
  intro h hh
  change (coeffRestrict H (z : k[G])).coeff h = 0
  rw [coeffRestrict_apply]
  apply hz (h : G)
  intro hhK
  exact hh hhK

/-- A covering equality over the intersection pastes to the two induced
central characters, provided both induced central functions are defined. -/
theorem inducedCentralCharacter_covers_of_local_cover
    {k G : Type*} [Field k] [Group G]
    (H X : Subgroup G)
    (lambdaH : GroupAlgebraCenter k H →ₐ[k] k)
    (lambdaHX :
      GroupAlgebraCenter k (X.comap H.subtype) →ₐ[k] k)
    (hlocal :
      CentralCharacterCovers (X.comap H.subtype) lambdaH lambdaHX)
    (hdefinedH : IsBlockInductionDefined H lambdaH)
    (hdefinedX :
      IsBlockInductionDefined (H.comap X.subtype)
        (centralCharacterAlongMulEquiv
          (subgroupIntersectionEquiv H X) lambdaHX)) :
    CentralCharacterCovers X
      (inducedCentralCharacter H lambdaH hdefinedH)
      (inducedCentralCharacter (H.comap X.subtype)
        (centralCharacterAlongMulEquiv
          (subgroupIntersectionEquiv H X) lambdaHX)
        hdefinedX) := by
  intro z hz
  simp only [inducedCentralCharacter_apply,
    inducedCentralFunction_apply]
  calc
    lambdaH (centerCoeffRestrict H z) =
        lambdaHX
          (centerCoeffRestrict (X.comap H.subtype)
            (centerCoeffRestrict H z)) :=
      hlocal _
        (centralElementSupportedOn_centerCoeffRestrict H X hz)
    _ =
        centralCharacterAlongMulEquiv
          (subgroupIntersectionEquiv H X) lambdaHX
          (centerCoeffRestrict (H.comap X.subtype)
            (centerCoeffRestrict X z)) := by
      rw [← centerCoeffRestrict_subgroupIntersection
        (k := k) H X z]
      simp only [centralCharacterAlongMulEquiv_apply,
        AlgEquiv.symm_apply_apply]

end

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
