import ModularRep.OrdinaryIrreducibleCharacter
import ModularRep.RadicalTransport
import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Finite-subgroup model of dependent local pairs

This file gives a dependent carrier in which `T` is a subgroup of a group
`G` and `eta` is an ordinary irreducible character of `N_G(T)`.  The domain
of `eta` therefore depends on `T`.  This is an action-theoretic prototype
only.  The generic weights in manuscript Lemma 3.6 use algebraic `e`-tori
and finite stabilisers of those algebraic objects, so this file is not
credited as their semantic formalisation.

We first use covariant transport along group equivalences.  Conjugation then
gives a left action of `G` on these dependent pairs.  This is the natural
orientation for the calculation with `MulAut.conj`.  The manuscript writes
automorphisms on the right, so its action by `alpha` corresponds to the
covariant action below by `alpha.symm`.
-/

namespace ModularRep.PaperProofs.EvenFieldDependentGenericPair

open ModularRep
open ModularRep.OrdinaryIrreducibleCharacter

universe u

variable {k G H K : Type u}

section CharacterTransport

variable [Field k] [Group G] [Group H] [Group K]

/-- Covariant transport of an irreducible character along a group
equivalence.  The transported character on `H` is obtained by precomposition
with the inverse equivalence. -/
def transportIrr (e : G ≃* H) (chi : Irr k G) : Irr k H :=
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
theorem transportIrr_apply (e : G ≃* H) (chi : Irr k G) (y : H) :
    transportIrr e chi y = chi (e.symm y) :=
  rfl

@[simp]
theorem transportIrr_refl (chi : Irr k G) :
    transportIrr (MulEquiv.refl G) chi = chi := by
  apply Subtype.ext
  funext x
  rfl

@[simp]
theorem transportIrr_trans (e : G ≃* H) (d : H ≃* K)
    (chi : Irr k G) :
    transportIrr d (transportIrr e chi) = transportIrr (e.trans d) chi := by
  apply Subtype.ext
  funext x
  rfl

end CharacterTransport

section Pairs

variable [Field k] [Group G]

/-- A finite-subgroup local pair whose character is genuinely a character of
the normaliser of its subgroup. -/
def GenericLocalPair (k G : Type u) [Field k] [Group G] :=
  Σ T : Subgroup G, Irr k (Subgroup.normalizer (T : Set G))

/-- Covariant transport of a dependent local pair along a group
automorphism. -/
def transportPair (alpha : MulAut G) (P : GenericLocalPair k G) :
    GenericLocalPair k G :=
  ⟨P.1.map alpha.toMonoidHom,
    transportIrr (normalizerEquiv alpha P.1) P.2⟩

@[simp]
theorem transportPair_subgroup (alpha : MulAut G)
    (P : GenericLocalPair k G) :
    (transportPair alpha P).1 = P.1.map alpha.toMonoidHom :=
  rfl

@[simp]
theorem transportPair_character_apply (alpha : MulAut G)
    (P : GenericLocalPair k G)
    (y : Subgroup.normalizer
      ((P.1.map alpha.toMonoidHom : Subgroup G) : Set G)) :
    (transportPair alpha P).2 y =
      P.2 ((normalizerEquiv alpha P.1).symm y) :=
  rfl

@[simp]
theorem normalizerEquiv_symm_coe (alpha : MulAut G) (T : Subgroup G)
    (y : Subgroup.normalizer
      ((T.map alpha.toMonoidHom : Subgroup G) : Set G)) :
    (((normalizerEquiv alpha T).symm y :
      Subgroup.normalizer (T : Set G)) : G) = alpha.symm y := by
  apply alpha.injective
  rw [alpha.apply_symm_apply]
  calc
    alpha (((normalizerEquiv alpha T).symm y :
        Subgroup.normalizer (T : Set G)) : G) =
        (((normalizerEquiv alpha T)
          ((normalizerEquiv alpha T).symm y) :
            Subgroup.normalizer
              ((T.map alpha.toMonoidHom : Subgroup G) : Set G)) : G) := by
          rw [normalizerEquiv_coe]
    _ = (y : G) := congrArg Subtype.val
      ((normalizerEquiv alpha T).apply_symm_apply y)

/-- The canonical equivalence between the normalisers of equal subgroups. -/
def normalizerCongr {T U : Subgroup G} (h : T = U) :
    Subgroup.normalizer (T : Set G) ≃*
      Subgroup.normalizer (U : Set G) :=
  MulEquiv.subgroupCongr
    (congrArg (fun V : Subgroup G ↦
      Subgroup.normalizer (V : Set G)) h)

@[simp]
theorem normalizerCongr_coe {T U : Subgroup G} (h : T = U)
    (x : Subgroup.normalizer (T : Set G)) :
    ((normalizerCongr h x :
      Subgroup.normalizer (U : Set G)) : G) = x := by
  subst U
  rfl

@[simp]
theorem normalizerCongr_symm_coe {T U : Subgroup G} (h : T = U)
    (x : Subgroup.normalizer (U : Set G)) :
    (((normalizerCongr h).symm x :
      Subgroup.normalizer (T : Set G)) : G) = (x : G) := by
  subst U
  rfl

/-- The element of `N_G(Q)` obtained from an element of `N_G(P)` when
`Q = alpha(P)`.  The equality of subgroups is used only to reconcile the
dependent normaliser types. -/
def transportedNormalizerElement (alpha : MulAut G)
    (P Q : GenericLocalPair k G)
    (h : Q.1 = P.1.map alpha.toMonoidHom)
    (x : Subgroup.normalizer (P.1 : Set G)) :
    Subgroup.normalizer (Q.1 : Set G) :=
  (normalizerCongr h).symm (normalizerEquiv alpha P.1 x)

@[simp]
theorem transportedNormalizerElement_coe (alpha : MulAut G)
    (P Q : GenericLocalPair k G)
    (h : Q.1 = P.1.map alpha.toMonoidHom)
    (x : Subgroup.normalizer (P.1 : Set G)) :
    ((transportedNormalizerElement alpha P Q h x :
      Subgroup.normalizer (Q.1 : Set G)) : G) = alpha x := by
  rw [transportedNormalizerElement, normalizerCongr_symm_coe,
    normalizerEquiv_coe]

/-- The inverse transport of a normaliser element. -/
def sourceNormalizerElement (alpha : MulAut G)
    (P Q : GenericLocalPair k G)
    (h : Q.1 = P.1.map alpha.toMonoidHom)
    (y : Subgroup.normalizer (Q.1 : Set G)) :
    Subgroup.normalizer (P.1 : Set G) :=
  (normalizerEquiv alpha P.1).symm (normalizerCongr h y)

@[simp]
theorem sourceNormalizerElement_coe (alpha : MulAut G)
    (P Q : GenericLocalPair k G)
    (h : Q.1 = P.1.map alpha.toMonoidHom)
    (y : Subgroup.normalizer (Q.1 : Set G)) :
    ((sourceNormalizerElement alpha P Q h y :
      Subgroup.normalizer (P.1 : Set G)) : G) = alpha.symm y := by
  rw [sourceNormalizerElement, normalizerEquiv_symm_coe,
    normalizerCongr_coe]

@[simp]
theorem transported_sourceNormalizerElement (alpha : MulAut G)
    (P Q : GenericLocalPair k G)
    (h : Q.1 = P.1.map alpha.toMonoidHom)
    (y : Subgroup.normalizer (Q.1 : Set G)) :
    transportedNormalizerElement alpha P Q h
      (sourceNormalizerElement alpha P Q h y) = y := by
  apply Subtype.ext
  rw [transportedNormalizerElement_coe, sourceNormalizerElement_coe]
  simp

@[simp]
theorem source_transportedNormalizerElement (alpha : MulAut G)
    (P Q : GenericLocalPair k G)
    (h : Q.1 = P.1.map alpha.toMonoidHom)
    (x : Subgroup.normalizer (P.1 : Set G)) :
    sourceNormalizerElement alpha P Q h
      (transportedNormalizerElement alpha P Q h x) = x := by
  apply Subtype.ext
  rw [sourceNormalizerElement_coe, transportedNormalizerElement_coe]
  simp

/-- `IsTransportedBy alpha P Q` is the graph of covariant transport by
`alpha`, expressed without identifying propositionally equal dependent
character domains.  It contains no fixedness assumption. -/
structure IsTransportedBy (alpha : MulAut G)
    (P Q : GenericLocalPair k G) : Prop where
  subgroup_eq : Q.1 = P.1.map alpha.toMonoidHom
  character_eq :
    ∀ x : Subgroup.normalizer (P.1 : Set G),
      Q.2 (transportedNormalizerElement alpha P Q subgroup_eq x) = P.2 x

/-- The explicitly transported pair satisfies the semantic transport
relation. -/
theorem transportPair_isTransported (alpha : MulAut G)
    (P : GenericLocalPair k G) :
    IsTransportedBy alpha P (transportPair alpha P) := by
  refine ⟨rfl, ?_⟩
  intro x
  change P.2 ((normalizerEquiv alpha P.1).symm
    (transportedNormalizerElement alpha P (transportPair alpha P) rfl x)) =
      P.2 x
  apply congrArg P.2
  apply Subtype.ext
  calc
    (((normalizerEquiv alpha P.1).symm
      (transportedNormalizerElement alpha P (transportPair alpha P) rfl x) :
        Subgroup.normalizer (P.1 : Set G)) : G) =
        alpha.symm (transportedNormalizerElement alpha P
          (transportPair alpha P) rfl x) :=
      normalizerEquiv_symm_coe alpha P.1 _
    _ = alpha.symm (alpha x) := congrArg alpha.symm
      (transportedNormalizerElement_coe alpha P
        (transportPair alpha P) rfl x)
    _ = x := alpha.symm_apply_apply x

/-- Identity is the first action law for the semantic transport relation. -/
theorem isTransportedBy_refl (P : GenericLocalPair k G) :
    IsTransportedBy (MulEquiv.refl G) P P := by
  rcases P with ⟨T, eta⟩
  refine ⟨(Subgroup.map_id T).symm, ?_⟩
  intro x
  apply congrArg eta
  apply Subtype.ext
  exact transportedNormalizerElement_coe (MulEquiv.refl G)
    ⟨T, eta⟩ ⟨T, eta⟩ (Subgroup.map_id T).symm x

/-- Successive covariant transports compose in the order
`beta * alpha`, because multiplication of automorphisms is composition and
`(beta * alpha)(x) = beta(alpha(x))`. -/
theorem IsTransportedBy.trans {alpha beta : MulAut G}
    {P Q R : GenericLocalPair k G}
    (hPQ : IsTransportedBy alpha P Q)
    (hQR : IsTransportedBy beta Q R) :
    IsTransportedBy (beta * alpha) P R := by
  have hsub : R.1 = P.1.map (beta * alpha).toMonoidHom := by
    calc
      R.1 = Q.1.map beta.toMonoidHom := hQR.subgroup_eq
      _ = (P.1.map alpha.toMonoidHom).map beta.toMonoidHom :=
        congrArg (fun T : Subgroup G ↦ T.map beta.toMonoidHom)
          hPQ.subgroup_eq
      _ = P.1.map (beta.toMonoidHom.comp alpha.toMonoidHom) :=
        Subgroup.map_map P.1 beta.toMonoidHom alpha.toMonoidHom
      _ = P.1.map (beta * alpha).toMonoidHom := rfl
  refine ⟨hsub, ?_⟩
  intro x
  let y : Subgroup.normalizer (Q.1 : Set G) :=
    transportedNormalizerElement alpha P Q hPQ.subgroup_eq x
  have hargs :
      transportedNormalizerElement (beta * alpha) P R hsub x =
        transportedNormalizerElement beta Q R hQR.subgroup_eq y := by
    apply Subtype.ext
    rw [transportedNormalizerElement_coe,
      transportedNormalizerElement_coe]
    rfl
  rw [hargs, hQR.character_eq y, hPQ.character_eq x]

/-- Transport by a fixed automorphism has a unique output pair. -/
theorem IsTransportedBy.right_unique {alpha : MulAut G}
    {P Q R : GenericLocalPair k G}
    (hPQ : IsTransportedBy alpha P Q)
    (hPR : IsTransportedBy alpha P R) :
    Q = R := by
  rcases P with ⟨T, eta⟩
  rcases Q with ⟨U, theta⟩
  rcases R with ⟨V, zeta⟩
  have hUV : U = V := hPQ.subgroup_eq.trans hPR.subgroup_eq.symm
  subst V
  refine Sigma.ext
    (β := fun W : Subgroup G ↦
      Irr k (Subgroup.normalizer (W : Set G))) rfl ?_
  apply heq_of_eq
  apply Subtype.ext
  funext y
  let xQ : Subgroup.normalizer (T : Set G) :=
    sourceNormalizerElement alpha ⟨T, eta⟩ ⟨U, theta⟩
      hPQ.subgroup_eq y
  let xR : Subgroup.normalizer (T : Set G) :=
    sourceNormalizerElement alpha ⟨T, eta⟩ ⟨U, zeta⟩
      hPR.subgroup_eq y
  have hx : xQ = xR := by
    apply Subtype.ext
    calc
      (xQ : G) = alpha.symm y :=
        sourceNormalizerElement_coe alpha ⟨T, eta⟩ ⟨U, theta⟩
          hPQ.subgroup_eq y
      _ = (xR : G) :=
        (sourceNormalizerElement_coe alpha ⟨T, eta⟩ ⟨U, zeta⟩
          hPR.subgroup_eq y).symm
  have hyQ : transportedNormalizerElement alpha
      ⟨T, eta⟩ ⟨U, theta⟩ hPQ.subgroup_eq xQ = y :=
    transported_sourceNormalizerElement alpha ⟨T, eta⟩ ⟨U, theta⟩
      hPQ.subgroup_eq y
  have hyR : transportedNormalizerElement alpha
      ⟨T, eta⟩ ⟨U, zeta⟩ hPR.subgroup_eq xR = y :=
    transported_sourceNormalizerElement alpha ⟨T, eta⟩ ⟨U, zeta⟩
      hPR.subgroup_eq y
  calc
    theta y = theta (transportedNormalizerElement alpha
        ⟨T, eta⟩ ⟨U, theta⟩ hPQ.subgroup_eq xQ) := by
      exact congrArg theta hyQ.symm
    _ = eta xQ := hPQ.character_eq xQ
    _ = eta xR := congrArg eta hx
    _ = zeta (transportedNormalizerElement alpha
        ⟨T, eta⟩ ⟨U, zeta⟩ hPR.subgroup_eq xR) :=
      (hPR.character_eq xR).symm
    _ = zeta y := congrArg zeta hyR

/-- The transport relation depends only on the automorphism, not on the
particular expression used for it. -/
theorem IsTransportedBy.congr {alpha beta : MulAut G}
    {P Q : GenericLocalPair k G}
    (h : IsTransportedBy alpha P Q) (hab : alpha = beta) :
    IsTransportedBy beta P Q := by
  subst beta
  exact h

/-- Transport by the inverse automorphism reverses semantic transport. -/
theorem IsTransportedBy.symm {alpha : MulAut G}
    {P Q : GenericLocalPair k G}
    (hPQ : IsTransportedBy alpha P Q) :
    IsTransportedBy alpha.symm Q P := by
  let R := transportPair alpha.symm Q
  have hQR : IsTransportedBy alpha.symm Q R :=
    transportPair_isTransported alpha.symm Q
  have hPR : IsTransportedBy (alpha.symm * alpha) P R := hPQ.trans hQR
  have hinv : alpha.symm * alpha = MulEquiv.refl G := by
    ext x
    simp
  have hPRrefl : IsTransportedBy (MulEquiv.refl G) P R := by
    exact hPR.congr hinv
  have hRP : R = P := hPRrefl.right_unique (isTransportedBy_refl P)
  simpa only [hRP] using hQR

/-- Identity law for the explicitly transported dependent pair.  It is
derived from the semantic relation and its uniqueness rather than from a
fixedness field. -/
@[simp]
theorem transportPair_refl (P : GenericLocalPair k G) :
    transportPair (MulEquiv.refl G) P = P :=
  (transportPair_isTransported (MulEquiv.refl G) P).right_unique
    (isTransportedBy_refl P)

/-- Composition law for explicit transport. -/
theorem transportPair_mul (alpha beta : MulAut G)
    (P : GenericLocalPair k G) :
    transportPair beta (transportPair alpha P) =
      transportPair (beta * alpha) P := by
  have hleft : IsTransportedBy (beta * alpha) P
      (transportPair beta (transportPair alpha P)) :=
    (transportPair_isTransported alpha P).trans
      (transportPair_isTransported beta (transportPair alpha P))
  exact hleft.right_unique
    (transportPair_isTransported (beta * alpha) P)

/-- Conjugation gives a genuine left action on dependent generic local
pairs. -/
instance conjugationSMul : SMul G (GenericLocalPair k G) where
  smul g P := transportPair (MulAut.conj g) P

/-- The conjugation action laws are consequences of the transport laws. -/
instance conjugationMulAction : MulAction G (GenericLocalPair k G) where
  one_smul P := by
    change transportPair (MulAut.conj (1 : G)) P = P
    have hconj : MulAut.conj (1 : G) = MulEquiv.refl G := by
      ext x
      simp
    rw [hconj]
    exact transportPair_refl P
  mul_smul g h P := by
    change transportPair (MulAut.conj (g * h)) P =
      transportPair (MulAut.conj g) (transportPair (MulAut.conj h) P)
    rw [transportPair_mul]
    congr 1
    ext x
    simp [mul_assoc]

/-- Conjugacy of dependent pairs, expressed using the standard orbit
relation of the preceding action. -/
def IsConjugate (P Q : GenericLocalPair k G) : Prop :=
  MulAction.orbitRel G (GenericLocalPair k G) P Q

/-- The set of `G`-conjugacy classes of dependent generic local pairs. -/
abbrev ConjugacyClass (k G : Type u) [Field k] [Group G] :=
  MulAction.orbitRel.Quotient G (GenericLocalPair k G)

/-- The conjugacy class represented by a dependent generic local pair. -/
def conjugacyClass (P : GenericLocalPair k G) : ConjugacyClass k G :=
  Quotient.mk'' P

/-- A semantic conjugation witness gives equality of conjugacy classes. -/
theorem conjugacyClass_eq_of_isTransportedBy_conj
    (g : G) (P Q : GenericLocalPair k G)
    (h : IsTransportedBy (MulAut.conj g) P Q) :
    conjugacyClass P = conjugacyClass Q := by
  apply Quotient.sound
  change MulAction.orbitRel G (GenericLocalPair k G) P Q
  rw [MulAction.orbitRel_apply]
  apply MulAction.mem_orbit_iff.mpr
  refine ⟨g⁻¹, ?_⟩
  change transportPair (MulAut.conj g⁻¹) Q = P
  have hinv : (MulAut.conj g).symm = MulAut.conj g⁻¹ := by
    ext x
    simp [mul_assoc]
  have hrev : IsTransportedBy (MulAut.conj g⁻¹) Q P :=
    h.symm.congr hinv
  exact (transportPair_isTransported (MulAut.conj g⁻¹) Q).right_unique hrev

/-- If `tau = Int(h) ∘ sigma` fixes a representative, then `sigma`
fixes its `G`-conjugacy class.  This is the exact elementary orbit step used
in the manuscript; the hypothesis supplies fixation under `tau`, not
fixation under `sigma`. -/
theorem conjugacyClass_fixed_of_innerTwist
    (sigma tau : MulAut G) (h : G)
    (htau : tau = MulAut.conj h * sigma)
    (P : GenericLocalPair k G)
    (hfixed : IsTransportedBy tau P P) :
    conjugacyClass (transportPair sigma P) = conjugacyClass P := by
  let Q := transportPair sigma P
  let R := transportPair (MulAut.conj h) Q
  have hPQ : IsTransportedBy sigma P Q :=
    transportPair_isTransported sigma P
  have hQR : IsTransportedBy (MulAut.conj h) Q R :=
    transportPair_isTransported (MulAut.conj h) Q
  have hPR0 : IsTransportedBy (MulAut.conj h * sigma) P R :=
    hPQ.trans hQR
  have hPR : IsTransportedBy tau P R := hPR0.congr htau.symm
  have hRP : R = P := hPR.right_unique hfixed
  have hconj : IsTransportedBy (MulAut.conj h) Q P := by
    simpa only [hRP] using hQR
  exact conjugacyClass_eq_of_isTransportedBy_conj h Q P hconj

/-- Right transport in the manuscript's convention.  Since covariant
transport sends `T` to `alpha(T)`, right transport by `alpha` is covariant
transport by `alpha⁻¹` and sends `T` to `alpha⁻¹(T)`. -/
def rightTransportPair (P : GenericLocalPair k G) (alpha : MulAut G) :
    GenericLocalPair k G :=
  transportPair alpha.symm P

@[simp]
theorem rightTransportPair_subgroup (P : GenericLocalPair k G)
    (alpha : MulAut G) :
    (rightTransportPair P alpha).1 =
      P.1.comap alpha.toMonoidHom := by
  exact (Subgroup.comap_equiv_eq_map_symm' alpha P.1).symm

@[simp]
theorem rightTransportPair_refl (P : GenericLocalPair k G) :
    rightTransportPair P (MulEquiv.refl G) = P := by
  change transportPair (MulEquiv.refl G).symm P = P
  exact transportPair_refl P

/-- Successive right transports follow the manuscript convention: first
`alpha`, then `beta`, is transport by `alpha * beta`. -/
theorem rightTransportPair_mul (P : GenericLocalPair k G)
    (alpha beta : MulAut G) :
    rightTransportPair (rightTransportPair P alpha) beta =
      rightTransportPair P (alpha * beta) := by
  change transportPair beta.symm (transportPair alpha.symm P) =
    transportPair (alpha * beta).symm P
  rw [transportPair_mul]
  congr 1

/-- Right-action form of the inner-twist orbit calculation.  The inverse of
`Int(h) ∘ sigma` is
`Int(sigma⁻¹(h⁻¹)) ∘ sigma⁻¹`, which explains the conjugating
element in the proof. -/
theorem conjugacyClass_fixed_of_innerTwist_right
    (sigma tau : MulAut G) (h : G)
    (htau : tau = MulAut.conj h * sigma)
    (P : GenericLocalPair k G)
    (hfixed : rightTransportPair P tau = P) :
    conjugacyClass (rightTransportPair P sigma) = conjugacyClass P := by
  have hfactor : tau.symm =
      MulAut.conj (sigma.symm h⁻¹) * sigma.symm := by
    rw [htau]
    ext x
    apply (MulAut.conj h * sigma).injective
    rw [(MulAut.conj h * sigma).apply_symm_apply]
    simp [mul_assoc]
  have hrel0 : IsTransportedBy tau.symm P
      (rightTransportPair P tau) :=
    transportPair_isTransported tau.symm P
  have hrel : IsTransportedBy tau.symm P P := by
    simpa only [hfixed] using hrel0
  exact conjugacyClass_fixed_of_innerTwist sigma.symm tau.symm
    (sigma.symm h⁻¹) hfactor P hrel

end Pairs

end ModularRep.PaperProofs.EvenFieldDependentGenericPair


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
