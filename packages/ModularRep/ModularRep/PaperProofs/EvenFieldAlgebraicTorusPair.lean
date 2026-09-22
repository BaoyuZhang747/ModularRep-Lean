import ModularRep.OrdinaryIrreducibleCharacter
import Mathlib.Algebra.Group.Action.Hom
import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Algebraic-torus labels with finite normaliser characters

The first entry of a generic weight is an algebraic torus, whereas its
character is a character of a finite normaliser.  These are different sorts.
This file therefore uses an abstract label type `A` for the algebraic tori.
The finite normaliser of a label is defined as its stabiliser under the inner
action of `H`.

Automorphisms of `H` act genuinely on `A`.  The normaliser equivalences and
all action laws on dependent character pairs are derived from that action.

The last theorem is the elementary orbit step in Lemma 3.6 of the manuscript:
if `tau = Int(h) ∘ sigma` fixes a pair, then `sigma` fixes its `H`-conjugacy
class.  Fixation by `tau` remains a separate input; in the manuscript it is the
output of the extension, Gallagher, Clifford, and induction argument.
-/

namespace ModularRep.PaperProofs.EvenFieldAlgebraicTorusPair

open ModularRep.OrdinaryIrreducibleCharacter

universe u

variable {k H A K : Type u}

section CharacterTransport

variable [Field k] [Group H] [Group K]

/-- Covariant transport of an irreducible character along a group
equivalence. -/
def transportIrr (e : H ≃* K) (chi : Irr k H) : Irr k K :=
  ⟨fun y ↦ chi (e.symm y), by
    rcases chi.property with ⟨R⟩
    refine ⟨
      { dimension := R.dimension
        representation := R.representation.pullback e.symm.toMonoidHom
        irreducible := R.irreducible.pullback e.symm.toMonoidHom
          e.symm.surjective
        character_eq := ?_ }⟩
    funext y
    change R.representation.character (e.symm y) = chi (e.symm y)
    exact congrFun R.character_eq (e.symm y)⟩

@[simp]
theorem transportIrr_apply (e : H ≃* K) (chi : Irr k H) (y : K) :
    transportIrr e chi y = chi (e.symm y) :=
  rfl

end CharacterTransport

section AlgebraicTorusLabels

variable [Group H] [MulAction (MulAut H) A]

/-- The action of the finite group on algebraic-torus labels by inner
automorphisms.  It is kept as a named action to avoid imposing a second
global action instance on `A`. -/
@[instance_reducible]
def innerAction : MulAction H A :=
  MulAction.compHom A (MulAut.conj : H →* MulAut H)

/-- The finite normaliser of an algebraic-torus label is its stabiliser under
inner conjugation by `H`. -/
def finiteNormalizer (T : A) : Subgroup H := by
  letI : MulAction H A := innerAction (H := H) (A := A)
  exact MulAction.stabilizer H T

@[simp]
theorem mem_finiteNormalizer_iff (T : A) (h : H) :
    h ∈ finiteNormalizer T ↔ (MulAut.conj h) • T = T :=
  Iff.rfl

/-- Conjugation commutes with transport by a group automorphism. -/
theorem conj_map (alpha : MulAut H) (h : H) :
    MulAut.conj (alpha h) =
      alpha * MulAut.conj h * alpha.symm := by
  ext x
  simp [mul_assoc]

/-- An automorphism carries the finite normaliser of `T` into the finite
normaliser of the transported label. -/
theorem map_mem_finiteNormalizer (alpha : MulAut H) (T : A) (h : H)
    (hh : h ∈ finiteNormalizer T) :
    alpha h ∈ finiteNormalizer (alpha • T) := by
  rw [mem_finiteNormalizer_iff] at hh ⊢
  rw [conj_map]
  simp only [mul_smul]
  calc
    alpha • (MulAut.conj h • (alpha.symm • (alpha • T))) =
        alpha • (MulAut.conj h • T) := by
          congr 2
          change alpha⁻¹ • (alpha • T) = T
          exact inv_smul_smul alpha T
    _ = alpha • T := congrArg (fun U : A ↦ alpha • U) hh

/-- The coherent equivalence between the two finite normalisers.  Its
underlying map on `H` is the given automorphism. -/
def finiteNormalizerEquiv (alpha : MulAut H) (T : A) :
    finiteNormalizer (H := H) (A := A) T ≃*
      finiteNormalizer (H := H) (A := A) (alpha • T) where
  toFun h := ⟨alpha h,
    map_mem_finiteNormalizer (H := H) (A := A) alpha T h h.2⟩
  invFun h := ⟨alpha.symm h, by
    have hm := map_mem_finiteNormalizer (H := H) (A := A)
      alpha.symm (alpha • T) h h.2
    have hlabel : alpha.symm • (alpha • T) = T := by
      change alpha⁻¹ • (alpha • T) = T
      exact inv_smul_smul alpha T
    rw [hlabel] at hm
    exact hm⟩
  left_inv h := by ext; simp
  right_inv h := by ext; simp
  map_mul' _ _ := by ext; simp

@[simp]
theorem finiteNormalizerEquiv_coe (alpha : MulAut H) (T : A)
    (h : finiteNormalizer (H := H) (A := A) T) :
    ((finiteNormalizerEquiv (H := H) (A := A) alpha T h :
      finiteNormalizer (H := H) (A := A) (alpha • T)) : H) = alpha h :=
  rfl

@[simp]
theorem finiteNormalizerEquiv_symm_coe (alpha : MulAut H) (T : A)
    (h : finiteNormalizer (H := H) (A := A) (alpha • T)) :
    (((finiteNormalizerEquiv (H := H) (A := A) alpha T).symm h :
      finiteNormalizer (H := H) (A := A) T) : H) = alpha.symm h :=
  rfl

end AlgebraicTorusLabels

section PairDefinitions

variable [Field k] [Group H] [MulAction (MulAut H) A]

/-- A two-sorted local pair: `T` is an algebraic-torus label and `eta` is an
irreducible character of its finite normaliser. -/
abbrev LocalPair (k H A : Type u) [Field k] [Group H]
    [MulAction (MulAut H) A] :=
  Σ T : A, Irr k (finiteNormalizer (H := H) T)

/-- Covariant transport by an automorphism of the finite group. -/
def transportPair (alpha : MulAut H) (P : LocalPair k H A) :
    LocalPair k H A :=
  ⟨alpha • P.1, transportIrr
    (finiteNormalizerEquiv (H := H) (A := A) alpha P.1) P.2⟩

@[simp]
theorem transportPair_label (alpha : MulAut H)
    (P : LocalPair k H A) :
    (transportPair alpha P).1 = alpha • P.1 :=
  rfl

@[simp]
theorem transportPair_character_apply (alpha : MulAut H)
    (P : LocalPair k H A)
    (y : finiteNormalizer (H := H) (A := A) (alpha • P.1)) :
    (transportPair alpha P).2 y =
      P.2 ((finiteNormalizerEquiv (H := H) (A := A) alpha P.1).symm y) :=
  rfl

/-- The canonical equivalence between the finite normalisers of equal
algebraic-torus labels. -/
def finiteNormalizerCongr {T U : A} (h : T = U) :
    finiteNormalizer (H := H) (A := A) T ≃*
      finiteNormalizer (H := H) (A := A) U :=
  MulEquiv.subgroupCongr
    (congrArg (finiteNormalizer (H := H) (A := A)) h)

@[simp]
theorem finiteNormalizerCongr_coe {T U : A} (h : T = U)
    (x : finiteNormalizer (H := H) (A := A) T) :
    ((finiteNormalizerCongr (H := H) (A := A) h x :
      finiteNormalizer (H := H) (A := A) U) : H) = x := by
  subst U
  rfl

@[simp]
theorem finiteNormalizerCongr_symm_coe {T U : A} (h : T = U)
    (x : finiteNormalizer (H := H) (A := A) U) :
    (((finiteNormalizerCongr (H := H) (A := A) h).symm x :
      finiteNormalizer (H := H) (A := A) T) : H) = x := by
  subst U
  rfl

/-- Transport a finite-normaliser element when the target label is given by
an equality rather than definitional reduction. -/
def transportedNormalizerElement (alpha : MulAut H)
    (P Q : LocalPair k H A) (h : Q.1 = alpha • P.1)
    (x : finiteNormalizer (H := H) (A := A) P.1) :
    finiteNormalizer (H := H) (A := A) Q.1 :=
  (finiteNormalizerCongr (H := H) (A := A) h).symm
    (finiteNormalizerEquiv (H := H) (A := A) alpha P.1 x)

@[simp]
theorem transportedNormalizerElement_coe (alpha : MulAut H)
    (P Q : LocalPair k H A) (h : Q.1 = alpha • P.1)
    (x : finiteNormalizer (H := H) (A := A) P.1) :
    ((transportedNormalizerElement alpha P Q h x :
      finiteNormalizer (H := H) (A := A) Q.1) : H) = alpha x := by
  rw [transportedNormalizerElement, finiteNormalizerCongr_symm_coe,
    finiteNormalizerEquiv_coe]

/-- Inverse transport of a finite-normaliser element. -/
def sourceNormalizerElement (alpha : MulAut H)
    (P Q : LocalPair k H A) (h : Q.1 = alpha • P.1)
    (y : finiteNormalizer (H := H) (A := A) Q.1) :
    finiteNormalizer (H := H) (A := A) P.1 :=
  (finiteNormalizerEquiv (H := H) (A := A) alpha P.1).symm
    (finiteNormalizerCongr (H := H) (A := A) h y)

@[simp]
theorem sourceNormalizerElement_coe (alpha : MulAut H)
    (P Q : LocalPair k H A) (h : Q.1 = alpha • P.1)
    (y : finiteNormalizer (H := H) (A := A) Q.1) :
    ((sourceNormalizerElement alpha P Q h y :
      finiteNormalizer (H := H) (A := A) P.1) : H) = alpha.symm y := by
  rw [sourceNormalizerElement, finiteNormalizerEquiv_symm_coe,
    finiteNormalizerCongr_coe]

/-- The graph of covariant transport by `alpha`, formulated without
identifying propositionally equal dependent character domains. -/
structure IsTransportedBy (alpha : MulAut H)
    (P Q : LocalPair k H A) : Prop where
  label_eq : Q.1 = alpha • P.1
  character_eq :
    ∀ x : finiteNormalizer (H := H) (A := A) P.1,
      Q.2 (transportedNormalizerElement alpha P Q label_eq x) = P.2 x

/-- The explicitly transported pair satisfies the semantic transport
relation. -/
theorem transportPair_isTransported (alpha : MulAut H)
    (P : LocalPair k H A) :
    IsTransportedBy alpha P (transportPair alpha P) := by
  unfold transportPair
  refine ⟨rfl, ?_⟩
  intro x
  change P.2 ((finiteNormalizerEquiv (H := H) (A := A) alpha P.1).symm
    (transportedNormalizerElement alpha P
      ⟨alpha • P.1, transportIrr
        (finiteNormalizerEquiv (H := H) (A := A) alpha P.1) P.2⟩ rfl x)) =
      P.2 x
  apply congrArg P.2
  apply Subtype.ext
  rw [finiteNormalizerEquiv_symm_coe,
    transportedNormalizerElement_coe]
  exact alpha.symm_apply_apply x

/-- Identity transport satisfies the semantic transport relation. -/
theorem isTransportedBy_one (P : LocalPair k H A) :
    IsTransportedBy (1 : MulAut H) P P := by
  refine ⟨(one_smul (MulAut H) P.1).symm, ?_⟩
  intro x
  apply congrArg P.2
  apply Subtype.ext
  rw [transportedNormalizerElement_coe]
  rfl

/-- Successive semantic transports compose. -/
theorem IsTransportedBy.trans {alpha beta : MulAut H}
    {P Q R : LocalPair k H A}
    (hPQ : IsTransportedBy alpha P Q)
    (hQR : IsTransportedBy beta Q R) :
    IsTransportedBy (beta * alpha) P R := by
  have hlabel : R.1 = (beta * alpha) • P.1 := by
    calc
      R.1 = beta • Q.1 := hQR.label_eq
      _ = beta • (alpha • P.1) :=
        congrArg (fun T : A ↦ beta • T) hPQ.label_eq
      _ = (beta * alpha) • P.1 := (mul_smul beta alpha P.1).symm
  refine ⟨hlabel, ?_⟩
  intro x
  let y : finiteNormalizer (H := H) (A := A) Q.1 :=
    transportedNormalizerElement alpha P Q hPQ.label_eq x
  have hargs :
      transportedNormalizerElement (beta * alpha) P R hlabel x =
        transportedNormalizerElement beta Q R hQR.label_eq y := by
    apply Subtype.ext
    rw [transportedNormalizerElement_coe,
      transportedNormalizerElement_coe]
    rfl
  rw [hargs, hQR.character_eq y, hPQ.character_eq x]

/-- Semantic transport by a fixed automorphism has a unique target. -/
theorem IsTransportedBy.right_unique {alpha : MulAut H}
    {P Q R : LocalPair k H A}
    (hPQ : IsTransportedBy alpha P Q)
    (hPR : IsTransportedBy alpha P R) :
    Q = R := by
  rcases P with ⟨T, eta⟩
  rcases Q with ⟨U, theta⟩
  rcases R with ⟨V, zeta⟩
  have hUV : U = V := hPQ.label_eq.trans hPR.label_eq.symm
  subst V
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  apply Subtype.ext
  funext y
  let xQ : finiteNormalizer (H := H) (A := A) T :=
    sourceNormalizerElement alpha ⟨T, eta⟩ ⟨U, theta⟩ hPQ.label_eq y
  let xR : finiteNormalizer (H := H) (A := A) T :=
    sourceNormalizerElement alpha ⟨T, eta⟩ ⟨U, zeta⟩ hPR.label_eq y
  have hx : xQ = xR := by
    apply Subtype.ext
    rw [sourceNormalizerElement_coe, sourceNormalizerElement_coe]
  have hyQ : transportedNormalizerElement alpha
      ⟨T, eta⟩ ⟨U, theta⟩ hPQ.label_eq xQ = y := by
    apply Subtype.ext
    rw [transportedNormalizerElement_coe, sourceNormalizerElement_coe]
    exact alpha.apply_symm_apply y
  have hyR : transportedNormalizerElement alpha
      ⟨T, eta⟩ ⟨U, zeta⟩ hPR.label_eq xR = y := by
    apply Subtype.ext
    rw [transportedNormalizerElement_coe, sourceNormalizerElement_coe]
    exact alpha.apply_symm_apply y
  calc
    theta y = theta (transportedNormalizerElement alpha
        ⟨T, eta⟩ ⟨U, theta⟩ hPQ.label_eq xQ) :=
      congrArg theta hyQ.symm
    _ = eta xQ := hPQ.character_eq xQ
    _ = eta xR := congrArg eta hx
    _ = zeta (transportedNormalizerElement alpha
        ⟨T, eta⟩ ⟨U, zeta⟩ hPR.label_eq xR) :=
      (hPR.character_eq xR).symm
    _ = zeta y := congrArg zeta hyR

@[simp]
theorem transportPair_one
    (P : LocalPair k H A) :
    transportPair (1 : MulAut H) P = P :=
  (transportPair_isTransported (1 : MulAut H) P).right_unique
    (isTransportedBy_one P)

/-- Covariant transports compose according to multiplication in
`MulAut H`: `(alpha * beta)(x) = alpha(beta(x))`. -/
theorem transportPair_mul (alpha beta : MulAut H)
    (P : LocalPair k H A) :
    transportPair alpha (transportPair beta P) =
      transportPair (alpha * beta) P := by
  have hleft : IsTransportedBy (alpha * beta) P
      (transportPair alpha (transportPair beta P)) :=
    (transportPair_isTransported beta P).trans
      (transportPair_isTransported alpha (transportPair beta P))
  exact hleft.right_unique
    (transportPair_isTransported (alpha * beta) P)

/-- The genuine left action of finite group automorphisms on the two-sorted
pairs. -/
instance pairMulAction :
    MulAction (MulAut H) (LocalPair k H A) where
  smul := transportPair
  one_smul := transportPair_one
  mul_smul alpha beta P := (transportPair_mul alpha beta P).symm

/-- Right transport in the manuscript's convention. -/
def rightTransportPair
    (P : LocalPair k H A) (alpha : MulAut H) :
    LocalPair k H A :=
  alpha.symm • P

@[simp]
theorem rightTransportPair_one
    (P : LocalPair k H A) :
    rightTransportPair P (1 : MulAut H) = P := by
  change (1 : MulAut H).symm • P = P
  rw [show (1 : MulAut H).symm = 1 by ext; rfl]
  exact one_smul (MulAut H) P

/-- Successive right transports match the manuscript convention. -/
theorem rightTransportPair_mul
    (P : LocalPair k H A)
    (alpha beta : MulAut H) :
    rightTransportPair (rightTransportPair P alpha) beta =
      rightTransportPair P (alpha * beta) := by
  change beta.symm • (alpha.symm • P) = (alpha * beta).symm • P
  have hsymm : (alpha * beta).symm = beta.symm * alpha.symm := by
    ext x
    rfl
  rw [hsymm, mul_smul]

/-- Conjugation by `H` gives the action used to form generic-weight
conjugacy classes. -/
instance conjugationPairMulAction :
    MulAction H (LocalPair k H A) :=
  MulAction.compHom (LocalPair k H A) (MulAut.conj : H →* MulAut H)

/-- A predicate defining the generic weights belonging to a fixed block.
Only invariance under inner conjugation is required. -/
structure InnerStablePredicate (k H A : Type u) [Field k] [Group H]
    [MulAction (MulAut H) A] where
  predicate : LocalPair k H A → Prop
  inner_stable : ∀ (h : H) (P : LocalPair k H A),
    predicate P → predicate (h • P)

variable (V : InnerStablePredicate k H A)

/-- The actual carrier to be quotiented: generic weights belonging to the
chosen block. -/
abbrev ValidPair (k H A : Type u) [Field k] [Group H]
    [MulAction (MulAut H) A] (V : InnerStablePredicate k H A) :=
  {P : LocalPair k H A // V.predicate P}

/-- Inner conjugation acts on the valid pairs. -/
instance validPairMulAction :
    MulAction H (ValidPair k H A V) where
  smul h P := ⟨h • P.1, V.inner_stable h P.1 P.2⟩
  one_smul P := by
    apply Subtype.ext
    exact one_smul H P.1
  mul_smul h g P := by
    apply Subtype.ext
    exact mul_smul h g P.1

/-- The set of `H`-conjugacy classes of valid generic/block pairs. -/
abbrev ValidConjugacyClass :=
  MulAction.orbitRel.Quotient H (ValidPair k H A V)

/-- The valid conjugacy class represented by a pair. -/
def validConjugacyClass (P : ValidPair k H A V) : ValidConjugacyClass V :=
  Quotient.mk'' P

/-- If `tau = Int(h) ∘ sigma` fixes a valid pair in the manuscript's
right-action convention, then right transport by `sigma` is again valid and
represents the same `H`-conjugacy class. -/
theorem validConjugacyClass_fixed_of_innerTwist_right
    (sigma tau : MulAut H) (h : H)
    (htau : tau = MulAut.conj h * sigma)
    (P : LocalPair k H A)
    (hP : V.predicate P)
    (hfixed : rightTransportPair P tau = P) :
    ∃ hSigma : V.predicate (rightTransportPair P sigma),
      validConjugacyClass V ⟨rightTransportPair P sigma, hSigma⟩ =
        validConjugacyClass V ⟨P, hP⟩ := by
  let h' : H := sigma.symm h⁻¹
  have hfactor : tau.symm = MulAut.conj h' * sigma.symm := by
    rw [htau]
    ext x
    apply (MulAut.conj h * sigma).injective
    rw [(MulAut.conj h * sigma).apply_symm_apply]
    simp [h', mul_assoc]
  let Q := rightTransportPair P sigma
  have hconj : h' • Q = P := by
    change (MulAut.conj h') • (sigma.symm • P) = P
    rw [← mul_smul, ← hfactor]
    exact hfixed
  have hQeq : h'⁻¹ • P = Q := by
    calc
      h'⁻¹ • P = h'⁻¹ • (h' • Q) := congrArg (fun R ↦ h'⁻¹ • R) hconj.symm
      _ = Q := inv_smul_smul h' Q
  have hQ : V.predicate Q := by
    rw [← hQeq]
    exact V.inner_stable h'⁻¹ P hP
  refine ⟨hQ, ?_⟩
  apply Quotient.sound
  change (⟨Q, hQ⟩ : ValidPair k H A V) ∈
    MulAction.orbit H (⟨P, hP⟩ : ValidPair k H A V)
  apply MulAction.mem_orbit_iff.mpr
  refine ⟨h'⁻¹, ?_⟩
  apply Subtype.ext
  exact hQeq

end PairDefinitions

end ModularRep.PaperProofs.EvenFieldAlgebraicTorusPair


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
