import ModularRep.OrdinaryIrreducibleCharacter
import ModularRep.OrdinaryCharacterDefectZero
import ModularRep.WeightRightActionCoherence

/-!
# Weights defined by representations and characters

This file identifies weights defined by representations with weights
defined by ordinary irreducible characters of defect zero.
It also constructs the automorphism and conjugation actions on weights
defined by characters.

The only representation theoretic input is
`LocalSplittingCharacterInput`: trace characters of simple local
representations are ordinary irreducible characters and separate simple
representations.  This is the precise splitting-field identification that is
left to the cited ordinary character theory.  It contains no block, weight
bijection, or iBAW conclusion.
-/

noncomputable section

open CategoryTheory Module

namespace ModularRep

universe u

namespace OrdinaryIrreducibleCharacter

variable {K A B C : Type u} [Field K] [CharZero K]
variable [Group A] [Group B] [Group C]

/-- Transport an ordinary irreducible character forward along a group
equivalence.  On functions this is pullback along the inverse equivalence. -/
def mapEquiv (chi : Irr K A) (e : A ≃* B) : Irr K B :=
  ⟨fun b ↦ chi (e.symm b), by
    rcases chi.property with ⟨R⟩
    exact ⟨
      { dimension := R.dimension
        representation := R.representation.pullback e.symm.toMonoidHom
        irreducible := R.irreducible.pullback e.symm.toMonoidHom
          e.symm.surjective
        character_eq := by
          funext b
          change R.representation.character (e.symm b) = chi (e.symm b)
          exact congrFun R.character_eq (e.symm b) }⟩⟩

@[simp]
theorem mapEquiv_apply (chi : Irr K A) (e : A ≃* B) (b : B) :
    mapEquiv chi e b = chi (e.symm b) :=
  rfl

@[simp]
theorem mapEquiv_refl (chi : Irr K A) :
    mapEquiv chi (MulEquiv.refl A) = chi := by
  ext a
  rfl

theorem mapEquiv_trans (chi : Irr K A) (e : A ≃* B) (d : B ≃* C) :
    mapEquiv (mapEquiv chi e) d = mapEquiv chi (e.trans d) := by
  ext c
  rfl

end OrdinaryIrreducibleCharacter


theorem IsDefectZeroOrdinaryCharacter.mapEquiv
    {p : ℕ} {K A B : Type u} [Field K] [CharZero K]
    [Group A] [Group B] [Finite A] [Finite B]
    {chi : OrdinaryIrreducibleCharacter.Irr K A}
    (hchi : IsDefectZeroOrdinaryCharacter p chi) (e : A ≃* B) :
    IsDefectZeroOrdinaryCharacter p
      (OrdinaryIrreducibleCharacter.mapEquiv chi e) := by
  rcases hchi with ⟨V, hVsimple, hVcharacter, hVdefect⟩
  let _ : Simple V := hVsimple
  refine ⟨fdRepMapEquiv e V, fdRepMapEquiv_simple e V, ?_,
    fdRepMapEquiv_defectZero e V hVdefect⟩
  funext b
  change V.character (e.symm b) = chi (e.symm b)
  exact congrFun hVcharacter (e.symm b)

/-- Exact external input identifying simple representations of every local
normaliser quotient with their ordinary trace characters over the selected
splitting field.  The first field says that the trace is irreducible.  The
second says that equal trace characters determine the simple representation
up to isomorphism. -/
structure LocalSplittingCharacterInput
    (K G : Type u) [Field K] [CharZero K] [Group G] [Finite G] where
  trace_is_irreducible :
    ∀ (Q : Subgroup G) (V : FDRep K (NormalizerQuotient Q)),
      Simple V →
        Nonempty
          (OrdinaryIrreducibleCharacter.Realisation K
            (NormalizerQuotient Q) V.character)
  trace_separates :
    ∀ (Q : Subgroup G) (V W : FDRep K (NormalizerQuotient Q)),
      Simple V → Simple W → V.character = W.character →
        Nonempty (V ≅ W)

namespace LocalSplittingCharacterInput

variable {K G : Type u} [Field K] [CharZero K] [Group G] [Finite G]

/-- The canonical function-valued irreducible character attached to a simple
local representation. -/
def characterOfSimple (C : LocalSplittingCharacterInput K G)
    (Q : Subgroup G) (V : FDRep K (NormalizerQuotient Q))
    (hV : Simple V) :
    OrdinaryIrreducibleCharacter.Irr K (NormalizerQuotient Q) :=
  ⟨V.character, C.trace_is_irreducible Q V hV⟩

@[simp]
theorem characterOfSimple_apply (C : LocalSplittingCharacterInput K G)
    (Q : Subgroup G) (V : FDRep K (NormalizerQuotient Q))
    (hV : Simple V) (x : NormalizerQuotient Q) :
    C.characterOfSimple Q V hV x = V.character x :=
  rfl

end LocalSplittingCharacterInput

/-- A conventional character-level `p`-weight: a radical subgroup together
with an irreducible ordinary defect-zero character of its normaliser
quotient. -/
structure CharacterWeight
    (p : ℕ) (K G : Type u)
    [Field K] [CharZero K] [Group G] [Finite G] where
  prime : p.Prime
  subgroup : Subgroup G
  radical : IsRadicalSubgroup p subgroup
  localCharacter :
    OrdinaryIrreducibleCharacter.Irr K (NormalizerQuotient subgroup)
  defectZero : IsDefectZeroOrdinaryCharacter p localCharacter

namespace CharacterWeight

variable {p : ℕ} {K G : Type u}
variable [Field K] [CharZero K] [Group G] [Finite G]

/-- Transport a local character along a literal equality of its radical
subgroup. -/
def castLocalCharacter {Q R : Subgroup G} (h : Q = R)
    (chi : OrdinaryIrreducibleCharacter.Irr K (NormalizerQuotient Q)) :
    OrdinaryIrreducibleCharacter.Irr K (NormalizerQuotient R) := by
  subst R
  exact chi

@[simp]
theorem castLocalCharacter_rfl {Q : Subgroup G}
    (chi : OrdinaryIrreducibleCharacter.Irr K (NormalizerQuotient Q)) :
    castLocalCharacter rfl chi = chi :=
  rfl

theorem castLocalCharacter_symm {Q R : Subgroup G} (h : Q = R)
    (chi : OrdinaryIrreducibleCharacter.Irr K (NormalizerQuotient Q)) :
    castLocalCharacter h.symm (castLocalCharacter h chi) = chi := by
  subst R
  rfl

theorem castLocalCharacter_trans {Q R S : Subgroup G}
    (h : Q = R) (h' : R = S)
    (chi : OrdinaryIrreducibleCharacter.Irr K (NormalizerQuotient Q)) :
    castLocalCharacter (h.trans h') chi =
      castLocalCharacter h' (castLocalCharacter h chi) := by
  subst R
  subst S
  rfl

/-- Character weights are isomorphic when their radical subgroups agree and
their transported local character functions agree. -/
def Isomorphic (W W' : CharacterWeight p K G) : Prop :=
  ∃ h : W.subgroup = W'.subgroup,
    castLocalCharacter h W.localCharacter = W'.localCharacter

/-- Character-weight isomorphism is literal equality: the subgroup and local
character are the only data fields, while primality, radicality, and defect
zero are proposition-valued proof fields. -/
theorem eq_of_isomorphic {W W' : CharacterWeight p K G}
    (h : Isomorphic W W') : W = W' := by
  rcases W with ⟨hp, Q, hrad, chi, hdz⟩
  rcases W' with ⟨hp', Q', hrad', chi', hdz'⟩
  rcases h with ⟨hQ, hchi⟩
  change Q = Q' at hQ
  subst Q'
  have hchi' : chi = chi' := by
    simpa only [castLocalCharacter_rfl] using hchi
  subst chi'
  rfl

theorem isomorphic_refl (W : CharacterWeight p K G) : Isomorphic W W :=
  ⟨rfl, rfl⟩

theorem isomorphic_symm {W W' : CharacterWeight p K G}
    (h : Isomorphic W W') : Isomorphic W' W := by
  rcases h with ⟨hQ, hchi⟩
  refine ⟨hQ.symm, ?_⟩
  calc
    castLocalCharacter hQ.symm W'.localCharacter =
        castLocalCharacter hQ.symm
          (castLocalCharacter hQ W.localCharacter) := by rw [hchi]
    _ = W.localCharacter := castLocalCharacter_symm hQ W.localCharacter

theorem isomorphic_trans {W W' W'' : CharacterWeight p K G}
    (h : Isomorphic W W') (h' : Isomorphic W' W'') :
    Isomorphic W W'' := by
  rcases h with ⟨hQ, hchi⟩
  rcases h' with ⟨hQ', hchi'⟩
  refine ⟨hQ.trans hQ', ?_⟩
  rw [castLocalCharacter_trans hQ hQ', hchi, hchi']

@[instance_reducible]
def isomorphicSetoid : Setoid (CharacterWeight p K G) where
  r := Isomorphic
  iseqv := ⟨isomorphic_refl, isomorphic_symm, isomorphic_trans⟩

/-- Character weights modulo equality of the radical subgroup and equality
of the transported local character function. -/
abbrev IsoClass := Quotient (isomorphicSetoid (p := p) (K := K) (G := G))

/-- Right automorphism transport on character weights. -/
def rightTwist (W : CharacterWeight p K G) (alpha : MulAut G) :
    CharacterWeight p K G where
  prime := W.prime
  subgroup := W.subgroup.comap alpha.toMonoidHom
  radical := W.radical.comap_mulAut alpha
  localCharacter := OrdinaryIrreducibleCharacter.mapEquiv W.localCharacter
    (rightNormalizerQuotientEquiv alpha W.subgroup).symm
  defectZero := W.defectZero.mapEquiv
    (rightNormalizerQuotientEquiv alpha W.subgroup).symm

@[simp]
theorem rightTwist_subgroup (W : CharacterWeight p K G)
    (alpha : MulAut G) :
    (W.rightTwist alpha).subgroup =
      W.subgroup.comap alpha.toMonoidHom :=
  rfl

theorem rightTwist_castLocalCharacter
    {Q R : Subgroup G} (hQ : Q = R)
    {chi : OrdinaryIrreducibleCharacter.Irr K (NormalizerQuotient Q)}
    {psi : OrdinaryIrreducibleCharacter.Irr K (NormalizerQuotient R)}
    (hchi : castLocalCharacter hQ chi = psi) (alpha : MulAut G) :
    castLocalCharacter
        (congrArg
          (fun S : Subgroup G ↦ S.comap alpha.toMonoidHom) hQ)
        (OrdinaryIrreducibleCharacter.mapEquiv chi
          (rightNormalizerQuotientEquiv alpha Q).symm) =
      OrdinaryIrreducibleCharacter.mapEquiv psi
        (rightNormalizerQuotientEquiv alpha R).symm := by
  subst R
  change OrdinaryIrreducibleCharacter.mapEquiv chi
      (rightNormalizerQuotientEquiv alpha Q).symm =
    OrdinaryIrreducibleCharacter.mapEquiv psi
      (rightNormalizerQuotientEquiv alpha Q).symm
  change chi = psi at hchi
  exact congrArg
    (fun theta ↦ OrdinaryIrreducibleCharacter.mapEquiv theta
      (rightNormalizerQuotientEquiv alpha Q).symm) hchi

theorem rightTwist_isomorphic {W W' : CharacterWeight p K G}
    (h : Isomorphic W W') (alpha : MulAut G) :
    Isomorphic (W.rightTwist alpha) (W'.rightTwist alpha) := by
  rcases h with ⟨hQ, hchi⟩
  exact ⟨congrArg
    (fun S : Subgroup G ↦ S.comap alpha.toMonoidHom) hQ,
    rightTwist_castLocalCharacter hQ hchi alpha⟩

/-- Right transport by a fixed automorphism on character-weight isomorphism
classes. -/
def rightTwistIsoClass (alpha : MulAut G) :
    IsoClass (p := p) (K := K) (G := G) →
      IsoClass (p := p) (K := K) (G := G) :=
  Quotient.map (fun W ↦ W.rightTwist alpha)
    (fun _ _ h ↦ rightTwist_isomorphic h alpha)

/-- Identity transport is isomorphic to the original character weight. -/
theorem rightTwist_one_isomorphic (W : CharacterWeight p K G) :
    Isomorphic (W.rightTwist (1 : MulAut G)) W := by
  refine ⟨rfl, ?_⟩
  apply OrdinaryIrreducibleCharacter.ext
  intro x
  change W.localCharacter
      (rightNormalizerQuotientEquiv (1 : MulAut G) W.subgroup x) =
    W.localCharacter x
  rw [rightNormalizerQuotientEquiv_one]
  rfl

@[simp]
theorem rightTwistIsoClass_one
    (x : IsoClass (p := p) (K := K) (G := G)) :
    rightTwistIsoClass (p := p) (K := K) (G := G)
      (1 : MulAut G) x = x := by
  refine Quotient.inductionOn x ?_
  intro W
  exact Quotient.sound (rightTwist_one_isomorphic W)

/-- Successive character twists agree with twisting by the product
automorphism, at the weight-isomorphism level. -/
theorem rightTwist_mul_isomorphic
    (W : CharacterWeight p K G) (alpha beta : MulAut G) :
    Isomorphic ((W.rightTwist alpha).rightTwist beta)
      (W.rightTwist (alpha * beta)) := by
  let hQ :
      (W.subgroup.comap alpha.toMonoidHom).comap beta.toMonoidHom =
        W.subgroup.comap (alpha * beta).toMonoidHom := by
    simp only [Subgroup.comap_comap]
    rfl
  refine ⟨hQ, ?_⟩
  apply OrdinaryIrreducibleCharacter.ext
  intro x
  let eAlpha := rightNormalizerQuotientEquiv alpha W.subgroup
  let eBeta := rightNormalizerQuotientEquiv beta
    (W.subgroup.comap alpha.toMonoidHom)
  let eProduct := rightNormalizerQuotientEquiv (alpha * beta) W.subgroup
  let castQ :
      NormalizerQuotient
          ((W.subgroup.comap alpha.toMonoidHom).comap beta.toMonoidHom) ≃*
        NormalizerQuotient
          (W.subgroup.comap (alpha * beta).toMonoidHom) :=
    MulEquiv.cast
      (M := fun R : Subgroup G ↦ NormalizerQuotient R) hQ
  have hcomp : eBeta.trans eAlpha = castQ.trans eProduct :=
    rightNormalizerQuotientEquiv_mul W.subgroup alpha beta
  have hx : eAlpha (eBeta x) = eProduct (castQ x) :=
    congrArg (fun e ↦ e x) hcomp
  change W.localCharacter (eAlpha (eBeta x)) =
    W.localCharacter (eProduct (castQ x))
  exact congrArg W.localCharacter hx

/-- Composition law for the manuscript right action on character-weight
isomorphism classes. -/
theorem rightTwistIsoClass_mul
    (x : IsoClass (p := p) (K := K) (G := G))
    (alpha beta : MulAut G) :
    rightTwistIsoClass (p := p) (K := K) (G := G) beta
        (rightTwistIsoClass (p := p) (K := K) (G := G) alpha x) =
      rightTwistIsoClass (p := p) (K := K) (G := G)
        (alpha * beta) x := by
  refine Quotient.inductionOn x ?_
  intro W
  exact Quotient.sound (rightTwist_mul_isomorphic W alpha beta)

instance isoClassMulAction :
    MulAction (MulAut G)ᵐᵒᵖ
      (IsoClass (p := p) (K := K) (G := G)) where
  smul alpha x := rightTwistIsoClass
    (p := p) (K := K) (G := G) alpha.unop x
  one_smul x := rightTwistIsoClass_one x
  mul_smul alpha beta x := by
    exact (rightTwistIsoClass_mul x beta.unop alpha.unop).symm

instance isoClassConjugationMulAction :
    MulAction G (IsoClass (p := p) (K := K) (G := G)) :=
  MulAction.compHom _
    (RepresentationWeight.innerInverseOpHom (G := G))

/-- Character weights modulo ambient conjugation. -/
abbrev ConjugacyClass := MulAction.orbitRel.Quotient G
  (IsoClass (p := p) (K := K) (G := G))

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

/-- Right automorphism transport descends to ambient conjugacy classes of
character weights. -/
def rightTwistConjugacyClass (alpha : MulAut G) :
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

instance conjugacyClassMulAction :
    MulAction (MulAut G)ᵐᵒᵖ
      (ConjugacyClass (p := p) (K := K) (G := G)) where
  smul alpha x := rightTwistConjugacyClass
    (p := p) (K := K) (G := G) alpha.unop x
  one_smul x := rightTwistConjugacyClass_one x
  mul_smul alpha beta x := by
    exact (rightTwistConjugacyClass_mul x beta.unop alpha.unop).symm

end CharacterWeight

namespace RepresentationWeight

variable {p : ℕ} {K G : Type u}
variable [Field K] [CharZero K] [Group G] [Finite G]

theorem cast_characterOfSimple_eq_of_iso
    (C : LocalSplittingCharacterInput K G)
    {Q R : Subgroup G} (hQ : Q = R)
    {V : FDRep K (NormalizerQuotient Q)}
    {V' : FDRep K (NormalizerQuotient R)}
    (hV : Simple V) (hV' : Simple V')
    (i : castLocalRepresentation hQ V ≅ V') :
    CharacterWeight.castLocalCharacter hQ
        (C.characterOfSimple Q V hV) =
      C.characterOfSimple R V' hV' := by
  subst R
  apply OrdinaryIrreducibleCharacter.ext
  intro x
  exact congrFun (FDRep.char_iso i) x

/-- Forget a representation weight to its canonical trace-character weight,
relative to the exact local splitting-character input. -/
def toCharacterWeight (C : LocalSplittingCharacterInput K G)
    (W : RepresentationWeight p K G) : CharacterWeight p K G where
  prime := W.prime
  subgroup := W.subgroup
  radical := W.radical
  localCharacter := C.characterOfSimple W.subgroup W.localRepresentation
    W.irreducible
  defectZero := ⟨W.localRepresentation, W.irreducible, rfl, W.defectZero⟩

theorem toCharacterWeight_isomorphic
    (C : LocalSplittingCharacterInput K G)
    {W W' : RepresentationWeight p K G} (h : Isomorphic W W') :
    CharacterWeight.Isomorphic (W.toCharacterWeight C)
      (W'.toCharacterWeight C) := by
  rcases h with ⟨hQ, ⟨i⟩⟩
  refine ⟨hQ, ?_⟩
  exact cast_characterOfSimple_eq_of_iso C hQ W.irreducible
    W'.irreducible i

/-- The induced map from representation-weight isomorphism classes to
character-weight isomorphism classes. -/
def toCharacterIsoClass (C : LocalSplittingCharacterInput K G) :
    IsoClass (p := p) (K := K) (G := G) →
      CharacterWeight.IsoClass (p := p) (K := K) (G := G) :=
  Quotient.map (toCharacterWeight C)
    (fun _ _ h ↦ toCharacterWeight_isomorphic C h)

/-- Trace-character transport commutes with the manuscript right action. -/
theorem toCharacterWeight_rightTwist_isomorphic
    (C : LocalSplittingCharacterInput K G)
    (W : RepresentationWeight p K G) (alpha : MulAut G) :
    CharacterWeight.Isomorphic
      ((W.rightTwist alpha).toCharacterWeight C)
      ((W.toCharacterWeight C).rightTwist alpha) := by
  refine ⟨rfl, ?_⟩
  apply OrdinaryIrreducibleCharacter.ext
  intro x
  rfl

theorem toCharacterIsoClass_rightTwist
    (C : LocalSplittingCharacterInput K G)
    (x : IsoClass (p := p) (K := K) (G := G))
    (alpha : MulAut G) :
    toCharacterIsoClass C
        (rightTwistIsoClass (p := p) (K := K) (G := G) alpha x) =
      CharacterWeight.rightTwistIsoClass
        (p := p) (K := K) (G := G) alpha
        (toCharacterIsoClass C x) := by
  refine Quotient.inductionOn x ?_
  intro W
  exact Quotient.sound
    (toCharacterWeight_rightTwist_isomorphic C W alpha)

end RepresentationWeight

namespace CharacterWeight

variable {p : ℕ} {K G : Type u}
variable [Field K] [CharZero K] [Group G] [Finite G]

/-- A representation affording the local character and witnessing its
defect-zero property. -/
def chosenLocalRepresentation (W : CharacterWeight p K G) :
    FDRep K (NormalizerQuotient W.subgroup) :=
  Classical.choose W.defectZero

theorem chosenLocalRepresentation_simple (W : CharacterWeight p K G) :
    Simple W.chosenLocalRepresentation :=
  (Classical.choose_spec W.defectZero).1

theorem chosenLocalRepresentation_character (W : CharacterWeight p K G) :
    W.chosenLocalRepresentation.character = W.localCharacter :=
  (Classical.choose_spec W.defectZero).2.1

theorem chosenLocalRepresentation_defectZero (W : CharacterWeight p K G) :
    IsDefectZeroRepresentation p W.chosenLocalRepresentation :=
  (Classical.choose_spec W.defectZero).2.2

/-- Choose a simple defect-zero representation affording a character
weight. -/
def toRepresentationWeight (W : CharacterWeight p K G) :
    RepresentationWeight p K G where
  prime := W.prime
  subgroup := W.subgroup
  radical := W.radical
  localRepresentation := W.chosenLocalRepresentation
  irreducible := W.chosenLocalRepresentation_simple
  defectZero := W.chosenLocalRepresentation_defectZero

theorem characterOfChosenRepresentation
    (C : LocalSplittingCharacterInput K G)
    (W : CharacterWeight p K G) :
    C.characterOfSimple W.subgroup W.chosenLocalRepresentation
        W.chosenLocalRepresentation_simple =
      W.localCharacter := by
  apply OrdinaryIrreducibleCharacter.ext
  intro x
  exact congrFun W.chosenLocalRepresentation_character x

theorem castLocalRepresentation_simple
    {Q R : Subgroup G} (hQ : Q = R)
    (V : FDRep K (NormalizerQuotient Q)) (hV : Simple V) :
    Simple (RepresentationWeight.castLocalRepresentation hQ V) := by
  subst R
  exact hV

/-- Equality of transported local characters gives isomorphism of the
chosen local representations, using exactly the separation field of the
splitting-character input. -/
theorem toRepresentationWeight_isomorphic
    (C : LocalSplittingCharacterInput K G)
    {W W' : CharacterWeight p K G} (h : Isomorphic W W') :
    RepresentationWeight.Isomorphic W.toRepresentationWeight
      W'.toRepresentationWeight := by
  rcases h with ⟨hQ, hchi⟩
  let V := W.chosenLocalRepresentation
  let V' := W'.chosenLocalRepresentation
  have hV : Simple V := W.chosenLocalRepresentation_simple
  have hV' : Simple V' := W'.chosenLocalRepresentation_simple
  have hcastV :
      Simple (RepresentationWeight.castLocalRepresentation hQ V) :=
    castLocalRepresentation_simple hQ V hV
  have hcV :
      C.characterOfSimple W.subgroup V hV = W.localCharacter :=
    characterOfChosenRepresentation C W
  have hcV' :
      C.characterOfSimple W'.subgroup V' hV' = W'.localCharacter :=
    characterOfChosenRepresentation C W'
  have hcastCharacter :
      C.characterOfSimple W'.subgroup
          (RepresentationWeight.castLocalRepresentation hQ V) hcastV =
        C.characterOfSimple W'.subgroup V' hV' := by
    calc
      C.characterOfSimple W'.subgroup
          (RepresentationWeight.castLocalRepresentation hQ V) hcastV =
          castLocalCharacter hQ
            (C.characterOfSimple W.subgroup V hV) :=
        (RepresentationWeight.cast_characterOfSimple_eq_of_iso C hQ hV
          hcastV (Iso.refl _)).symm
      _ = castLocalCharacter hQ W.localCharacter :=
        congrArg (castLocalCharacter hQ) hcV
      _ = W'.localCharacter := hchi
      _ = C.characterOfSimple W'.subgroup V' hV' := hcV'.symm
  refine ⟨hQ, C.trace_separates W'.subgroup
    (RepresentationWeight.castLocalRepresentation hQ V) V' hcastV hV' ?_⟩
  exact congrArg Subtype.val hcastCharacter

/-- The induced map from character-weight isomorphism classes back to
representation-weight isomorphism classes. -/
def toRepresentationIsoClass (C : LocalSplittingCharacterInput K G) :
    IsoClass (p := p) (K := K) (G := G) →
      RepresentationWeight.IsoClass (p := p) (K := K) (G := G) :=
  Quotient.map toRepresentationWeight
    (fun _ _ h ↦ toRepresentationWeight_isomorphic C h)

theorem toCharacterWeight_toRepresentationWeight_isomorphic
    (C : LocalSplittingCharacterInput K G)
    (W : CharacterWeight p K G) :
    Isomorphic (W.toRepresentationWeight.toCharacterWeight C) W := by
  exact ⟨rfl, characterOfChosenRepresentation C W⟩

theorem toRepresentationWeight_toCharacterWeight_isomorphic
    (C : LocalSplittingCharacterInput K G)
    (W : RepresentationWeight p K G) :
    RepresentationWeight.Isomorphic
      (W.toCharacterWeight C).toRepresentationWeight W := by
  let V := (W.toCharacterWeight C).chosenLocalRepresentation
  have hV : Simple V :=
    (W.toCharacterWeight C).chosenLocalRepresentation_simple
  have hchar : V.character = W.localRepresentation.character := by
    exact (W.toCharacterWeight C).chosenLocalRepresentation_character
  exact ⟨rfl, C.trace_separates W.subgroup V W.localRepresentation hV
    W.irreducible hchar⟩

@[simp]
theorem toRepresentationIsoClass_toCharacterIsoClass
    (C : LocalSplittingCharacterInput K G)
    (x : IsoClass (p := p) (K := K) (G := G)) :
    RepresentationWeight.toCharacterIsoClass C
        (toRepresentationIsoClass C x) = x := by
  refine Quotient.inductionOn x ?_
  intro W
  exact Quotient.sound
    (toCharacterWeight_toRepresentationWeight_isomorphic C W)

@[simp]
theorem toCharacterIsoClass_toRepresentationIsoClass
    (C : LocalSplittingCharacterInput K G)
    (x : RepresentationWeight.IsoClass (p := p) (K := K) (G := G)) :
    toRepresentationIsoClass C
        (RepresentationWeight.toCharacterIsoClass C x) = x := by
  refine Quotient.inductionOn x ?_
  intro W
  exact Quotient.sound
    (toRepresentationWeight_toCharacterWeight_isomorphic C W)

/-- The splitting-field character input identifies the two honest
isomorphism-class carriers. -/
def isoClassEquiv (C : LocalSplittingCharacterInput K G) :
    RepresentationWeight.IsoClass (p := p) (K := K) (G := G) ≃
      IsoClass (p := p) (K := K) (G := G) where
  toFun := RepresentationWeight.toCharacterIsoClass C
  invFun := toRepresentationIsoClass C
  left_inv := toCharacterIsoClass_toRepresentationIsoClass C
  right_inv := toRepresentationIsoClass_toCharacterIsoClass C

theorem toRepresentationIsoClass_rightTwist
    (C : LocalSplittingCharacterInput K G)
    (x : IsoClass (p := p) (K := K) (G := G))
    (alpha : MulAut G) :
    toRepresentationIsoClass C
        (rightTwistIsoClass (p := p) (K := K) (G := G) alpha x) =
      RepresentationWeight.rightTwistIsoClass
        (p := p) (K := K) (G := G) alpha
        (toRepresentationIsoClass C x) := by
  apply (isoClassEquiv C).injective
  calc
    RepresentationWeight.toCharacterIsoClass C
        (toRepresentationIsoClass C
          (rightTwistIsoClass alpha x)) =
        rightTwistIsoClass alpha x :=
      toRepresentationIsoClass_toCharacterIsoClass C _
    _ = rightTwistIsoClass alpha
          (RepresentationWeight.toCharacterIsoClass C
            (toRepresentationIsoClass C x)) := by
      rw [toRepresentationIsoClass_toCharacterIsoClass]
    _ = RepresentationWeight.toCharacterIsoClass C
          (RepresentationWeight.rightTwistIsoClass alpha
            (toRepresentationIsoClass C x)) :=
      (RepresentationWeight.toCharacterIsoClass_rightTwist C _ alpha).symm

end CharacterWeight

namespace RepresentationWeight

variable {p : ℕ} {K G : Type u}
variable [Field K] [CharZero K] [Group G] [Finite G]

theorem toCharacterIsoClass_conjugation
    (C : LocalSplittingCharacterInput K G) (g : G)
    (x : IsoClass (p := p) (K := K) (G := G)) :
    toCharacterIsoClass C (g • x) =
      g • toCharacterIsoClass C x := by
  exact toCharacterIsoClass_rightTwist C x (MulAut.conj g⁻¹)

/-- The map from representation-weight classes to character-weight classes
descends through ambient conjugation. -/
def toCharacterConjugacyClass (C : LocalSplittingCharacterInput K G) :
    ConjugacyClass (p := p) (K := K) (G := G) →
      CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G) :=
  Quotient.map (toCharacterIsoClass C) (by
    intro x y hxy
    rcases hxy with ⟨g, rfl⟩
    exact ⟨g, (toCharacterIsoClass_conjugation C g y).symm⟩)

theorem toCharacterConjugacyClass_rightTwist
    (C : LocalSplittingCharacterInput K G)
    (x : ConjugacyClass (p := p) (K := K) (G := G))
    (alpha : MulAut G) :
    toCharacterConjugacyClass C
        (rightTwistConjugacyClass (p := p) (K := K) (G := G) alpha x) =
      CharacterWeight.rightTwistConjugacyClass
        (p := p) (K := K) (G := G) alpha
        (toCharacterConjugacyClass C x) := by
  refine Quotient.inductionOn x ?_
  intro W
  exact congrArg
    (fun z : CharacterWeight.IsoClass
        (p := p) (K := K) (G := G) ↦
      (Quotient.mk'' z : CharacterWeight.ConjugacyClass
        (p := p) (K := K) (G := G)))
    (toCharacterIsoClass_rightTwist C W alpha)

end RepresentationWeight

namespace CharacterWeight

variable {p : ℕ} {K G : Type u}
variable [Field K] [CharZero K] [Group G] [Finite G]

theorem toRepresentationIsoClass_conjugation
    (C : LocalSplittingCharacterInput K G) (g : G)
    (x : IsoClass (p := p) (K := K) (G := G)) :
    toRepresentationIsoClass C (g • x) =
      g • toRepresentationIsoClass C x := by
  exact toRepresentationIsoClass_rightTwist C x (MulAut.conj g⁻¹)

def toRepresentationConjugacyClass
    (C : LocalSplittingCharacterInput K G) :
    ConjugacyClass (p := p) (K := K) (G := G) →
      RepresentationWeight.ConjugacyClass
        (p := p) (K := K) (G := G) :=
  Quotient.map (toRepresentationIsoClass C) (by
    intro x y hxy
    rcases hxy with ⟨g, rfl⟩
    exact ⟨g, (toRepresentationIsoClass_conjugation C g y).symm⟩)

@[simp]
theorem toRepresentationConjugacyClass_toCharacterConjugacyClass
    (C : LocalSplittingCharacterInput K G)
    (x : ConjugacyClass (p := p) (K := K) (G := G)) :
    RepresentationWeight.toCharacterConjugacyClass C
        (toRepresentationConjugacyClass C x) = x := by
  refine Quotient.inductionOn x ?_
  intro W
  exact congrArg
    (fun z : IsoClass (p := p) (K := K) (G := G) ↦
      (Quotient.mk'' z : ConjugacyClass (p := p) (K := K) (G := G)))
    (toRepresentationIsoClass_toCharacterIsoClass C W)

@[simp]
theorem toCharacterConjugacyClass_toRepresentationConjugacyClass
    (C : LocalSplittingCharacterInput K G)
    (x : RepresentationWeight.ConjugacyClass
      (p := p) (K := K) (G := G)) :
    toRepresentationConjugacyClass C
        (RepresentationWeight.toCharacterConjugacyClass C x) = x := by
  refine Quotient.inductionOn x ?_
  intro W
  exact congrArg
    (fun z : RepresentationWeight.IsoClass
        (p := p) (K := K) (G := G) ↦
      (Quotient.mk'' z : RepresentationWeight.ConjugacyClass
        (p := p) (K := K) (G := G)))
    (toCharacterIsoClass_toRepresentationIsoClass C W)

/-- Under the exact splitting-character input, representation-weight and
character-weight conjugacy classes are equivalent. -/
def conjugacyClassEquiv (C : LocalSplittingCharacterInput K G) :
    RepresentationWeight.ConjugacyClass
        (p := p) (K := K) (G := G) ≃
      ConjugacyClass (p := p) (K := K) (G := G) where
  toFun := RepresentationWeight.toCharacterConjugacyClass C
  invFun := toRepresentationConjugacyClass C
  left_inv := toCharacterConjugacyClass_toRepresentationConjugacyClass C
  right_inv := toRepresentationConjugacyClass_toCharacterConjugacyClass C

theorem conjugacyClassEquiv_smul
    (C : LocalSplittingCharacterInput K G)
    (alpha : (MulAut G)ᵐᵒᵖ)
    (x : RepresentationWeight.ConjugacyClass
      (p := p) (K := K) (G := G)) :
    conjugacyClassEquiv C (alpha • x) =
      alpha • conjugacyClassEquiv C x :=
  RepresentationWeight.toCharacterConjugacyClass_rightTwist
    C x alpha.unop

/-- An abstract block assignment on the set of weights defined by characters.  It is
deliberately limited to a block label and its automorphism compatibility.
Constructing the manuscript's assignment by local block induction is a
separate representation theoretic obligation. -/
structure EquivariantBlockAssignment
    (Block : Type u) [MulAction (MulAut G)ᵐᵒᵖ Block] where
  blockOf : ConjugacyClass (p := p) (K := K) (G := G) → Block
  map_smul : ∀ (alpha : (MulAut G)ᵐᵒᵖ)
    (W : ConjugacyClass (p := p) (K := K) (G := G)),
    blockOf (alpha • W) = alpha • blockOf W

namespace EquivariantBlockAssignment

variable {Block : Type u} [MulAction (MulAut G)ᵐᵒᵖ Block]

/-- Character-weight conjugacy classes assigned to one block. -/
def Fibre (D : EquivariantBlockAssignment
    (p := p) (K := K) (G := G) Block) (b : Block) :=
  {W : ConjugacyClass (p := p) (K := K) (G := G) // D.blockOf W = b}

/-- The stabiliser of a block acts on its character-weight fibre. -/
instance fibreMulAction
    (D : EquivariantBlockAssignment
      (p := p) (K := K) (G := G) Block) (b : Block) :
    MulAction (MulAction.stabilizer (MulAut G)ᵐᵒᵖ b) (D.Fibre b) where
  smul alpha W := ⟨(alpha : (MulAut G)ᵐᵒᵖ) • W.1, by
    rw [D.map_smul, W.2, alpha.2]⟩
  one_smul W := by
    apply Subtype.ext
    change (1 : (MulAut G)ᵐᵒᵖ) • W.1 = W.1
    exact one_smul _ W.1
  mul_smul alpha beta W := by
    apply Subtype.ext
    change
      ((alpha : (MulAut G)ᵐᵒᵖ) * (beta : (MulAut G)ᵐᵒᵖ)) • W.1 =
        (alpha : (MulAut G)ᵐᵒᵖ) •
          ((beta : (MulAut G)ᵐᵒᵖ) • W.1)
    exact mul_smul _ _ W.1

@[simp]
theorem fibre_smul_val
    (D : EquivariantBlockAssignment
      (p := p) (K := K) (G := G) Block) (b : Block)
    (alpha : MulAction.stabilizer (MulAut G)ᵐᵒᵖ b)
    (W : D.Fibre b) :
    ((alpha • W : D.Fibre b).1) =
      (alpha : (MulAut G)ᵐᵒᵖ) • W.1 :=
  rfl

end EquivariantBlockAssignment

end CharacterWeight

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
