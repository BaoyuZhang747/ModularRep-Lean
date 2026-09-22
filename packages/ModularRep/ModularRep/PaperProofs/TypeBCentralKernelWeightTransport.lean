import ModularRep.NormalCoreTransport
import ModularRep.WeightCharacterBridge

/-!
# Actual character weights across a normal ell-subgroup

The map is an arbitrary surjective homomorphism of finite groups whose
kernel is an ell-group.  Its kernel need not equal the ell-core.  Radicals
and local normalizer quotients use the checked `NormalCoreTransport` maps.
Local ordinary characters are transported by those literal equivalences.
Inverse laws and automorphism naturality are proved on actual normalizer
representatives, without a weight-correspondence source input.

This file makes no assertion about blocks or a Brauer-to-weight bijection.
The central-kernel application is obtained by specializing the homomorphism
to the actual quotient map; centrality is unnecessary for this weight part.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBCentralKernelWeightTransport

open CharacterWeight

universe u

variable {p : ℕ} {K G H : Type u}
  [Field K] [CharZero K] [Group G] [Group H] [Finite G] [Finite H]

/-- The literal quotient homomorphism from a subgroup's normalizer. -/
abbrev localMk (Q : Subgroup G) :
    Subgroup.normalizer (Q : Set G) →* NormalizerQuotient Q :=
  QuotientGroup.mk' (Q.subgroupOf (Subgroup.normalizer (Q : Set G)))

/-- Equality of weights can be checked using the same underlying
normalizer elements, without transporting a character by an opaque cast. -/
theorem weight_eq_of_values (W V : CharacterWeight p K G)
    (hQ : W.subgroup = V.subgroup)
    (hvalue : ∀ (x : Subgroup.normalizer (W.subgroup : Set G))
      (y : Subgroup.normalizer (V.subgroup : Set G)),
      (x : G) = y →
      W.localCharacter (localMk W.subgroup x) =
        V.localCharacter (localMk V.subgroup y)) : W = V := by
  apply CharacterWeight.eq_of_isomorphic
  refine ⟨hQ, ?_⟩
  rcases W with ⟨hp, Q, hrad, chi, hdz⟩
  rcases V with ⟨hp', R, hrad', psi, hdz'⟩
  change Q = R at hQ
  subst R
  apply OrdinaryIrreducibleCharacter.ext
  intro x
  refine Quotient.inductionOn x ?_
  intro x
  exact hvalue x x rfl

theorem localCharacter_eq_of_eq {W V : CharacterWeight p K G}
    (h : W = V)
    (x : Subgroup.normalizer (W.subgroup : Set G))
    (y : Subgroup.normalizer (V.subgroup : Set G)) (hxy : (x : G) = y) :
    W.localCharacter (localMk W.subgroup x) =
      V.localCharacter (localMk V.subgroup y) := by
  subst V
  have : x = y := Subtype.ext hxy
  subst y
  rfl

theorem rightTwist_localCharacter (W : CharacterWeight p K G)
    (alpha : MulAut G)
    (x : Subgroup.normalizer ((W.rightTwist alpha).subgroup : Set G)) :
    (W.rightTwist alpha).localCharacter
        (localMk (W.rightTwist alpha).subgroup x) =
      W.localCharacter
        (localMk W.subgroup (rightNormalizerEquiv alpha W.subgroup x)) := by
  change W.localCharacter
      (rightNormalizerQuotientEquiv alpha W.subgroup
        (localMk (W.subgroup.comap alpha.toMonoidHom) x)) = _
  rfl

variable (f : G →* H) (hf : Function.Surjective f)
  (hker : IsPGroup p f.ker)

include hker in
theorem kernel_le_radical (W : CharacterWeight p K G) :
    f.ker ≤ W.subgroup :=
  (normal_pSubgroup_le_pCore p f.ker hker).trans
    (pCore_le_of_isRadicalSubgroup W.prime W.subgroup W.radical)

/-- The actual local quotient equivalence for an upstairs weight. -/
def localEquiv (W : CharacterWeight p K G) :
    NormalizerQuotient W.subgroup ≃*
      NormalizerQuotient (W.subgroup.map f) :=
  normalizerQuotientEquivOfSurjectiveOfKerLE f hf W.subgroup
    (kernel_le_radical f hker W)

theorem localEquiv_mk (W : CharacterWeight p K G)
    (x : Subgroup.normalizer (W.subgroup : Set G)) :
    localEquiv f hf hker W (localMk W.subgroup x) =
      localMk (W.subgroup.map f) (normalizerMap f W.subgroup x) := rfl

/-- Descend the radical and its ordinary defect-zero quotient character. -/
def descend (W : CharacterWeight p K G) : CharacterWeight p K H where
  prime := W.prime
  subgroup := W.subgroup.map f
  radical := (isRadicalSubgroup_iff_map_surjective_of_ker_le
    f hf W.subgroup (kernel_le_radical f hker W) hker).mp W.radical
  localCharacter := OrdinaryIrreducibleCharacter.mapEquiv W.localCharacter
    (localEquiv f hf hker W)
  defectZero := W.defectZero.mapEquiv (localEquiv f hf hker W)

@[simp] theorem descend_subgroup (W : CharacterWeight p K G) :
    (descend f hf hker W).subgroup = W.subgroup.map f := rfl

theorem descend_localCharacter (W : CharacterWeight p K G)
    (x : Subgroup.normalizer (W.subgroup : Set G))
    (y : Subgroup.normalizer ((descend f hf hker W).subgroup : Set H))
    (hxy : f x = y) :
    (descend f hf hker W).localCharacter
        (localMk (descend f hf hker W).subgroup y) =
      W.localCharacter (localMk W.subgroup x) := by
  have hy : normalizerMap f W.subgroup x = y := Subtype.ext hxy
  subst y
  change W.localCharacter
      ((localEquiv f hf hker W).symm
        (localMk (W.subgroup.map f) (normalizerMap f W.subgroup x))) = _
  rw [← localEquiv_mk f hf hker W x]
  rw [MulEquiv.symm_apply_apply]

/-- The preimage local quotient, with the map-comap equality retained. -/
def preimageLocalEquiv (R : Subgroup H) :
    NormalizerQuotient (R.comap f) ≃* NormalizerQuotient R :=
  (normalizerQuotientEquivOfSurjectiveOfKerLE f hf (R.comap f)
    (Subgroup.ker_le_comap f R)).trans
      (MulEquiv.cast (M := fun S : Subgroup H ↦ NormalizerQuotient S)
        (Subgroup.map_comap_eq_self_of_surjective hf R))

theorem localEquiv_cast_mk (Q : Subgroup G) (hQ : f.ker ≤ Q)
    (R : Subgroup H) (hQR : Q.map f = R)
    (x : Subgroup.normalizer (Q : Set G))
    (y : Subgroup.normalizer (R : Set H)) (hxy : f x = y) :
    ((normalizerQuotientEquivOfSurjectiveOfKerLE f hf Q hQ).trans
      (MulEquiv.cast (M := fun S : Subgroup H ↦ NormalizerQuotient S) hQR))
        (localMk Q x) = localMk R y := by
  subst R
  have hy : normalizerMap f Q x = y := Subtype.ext hxy
  subst y
  rfl

theorem preimageLocalEquiv_mk (R : Subgroup H)
    (x : Subgroup.normalizer ((R.comap f : Subgroup G) : Set G))
    (y : Subgroup.normalizer (R : Set H)) (hxy : f x = y) :
    preimageLocalEquiv f hf R (localMk (R.comap f) x) = localMk R y :=
  localEquiv_cast_mk f hf _ _ _ _ x y hxy

/-- Lift the full preimage radical and pull back the same local character. -/
def lift (W : CharacterWeight p K H) : CharacterWeight p K G where
  prime := W.prime
  subgroup := W.subgroup.comap f
  radical := (isRadicalSubgroup_iff_map_surjective_of_ker_le
    f hf (W.subgroup.comap f) (Subgroup.ker_le_comap f W.subgroup) hker).mpr
      (by simpa only [Subgroup.map_comap_eq_self_of_surjective hf]
        using W.radical)
  localCharacter := OrdinaryIrreducibleCharacter.mapEquiv W.localCharacter
    (preimageLocalEquiv f hf W.subgroup).symm
  defectZero := W.defectZero.mapEquiv (preimageLocalEquiv f hf W.subgroup).symm

@[simp] theorem lift_subgroup (W : CharacterWeight p K H) :
    (lift f hf hker W).subgroup = W.subgroup.comap f := rfl

theorem lift_localCharacter (W : CharacterWeight p K H)
    (x : Subgroup.normalizer ((lift f hf hker W).subgroup : Set G))
    (y : Subgroup.normalizer (W.subgroup : Set H)) (hxy : f x = y) :
    (lift f hf hker W).localCharacter
        (localMk (lift f hf hker W).subgroup x) =
      W.localCharacter (localMk W.subgroup y) := by
  change W.localCharacter
    (preimageLocalEquiv f hf W.subgroup (localMk (W.subgroup.comap f) x)) = _
  rw [preimageLocalEquiv_mk f hf W.subgroup x y hxy]

theorem descend_injective : Function.Injective (descend (K := K) f hf hker) := by
  intro W V hWV
  have hmap : W.subgroup.map f = V.subgroup.map f :=
    congrArg CharacterWeight.subgroup hWV
  have hQ : W.subgroup = V.subgroup :=
    Subgroup.map_injective_of_ker_le f
      (kernel_le_radical f hker W) (kernel_le_radical f hker V) hmap
  apply weight_eq_of_values W V hQ
  intro x y hxy
  rw [← descend_localCharacter f hf hker W x (normalizerMap f W.subgroup x) rfl,
    ← descend_localCharacter f hf hker V y (normalizerMap f V.subgroup y) rfl]
  exact localCharacter_eq_of_eq hWV _ _ (congrArg f hxy)

@[simp] theorem descend_lift (W : CharacterWeight p K H) :
    descend f hf hker (lift f hf hker W) = W := by
  apply weight_eq_of_values _ W
    (Subgroup.map_comap_eq_self_of_surjective hf W.subgroup)
  intro x y hxy
  obtain ⟨z, hz⟩ := normalizerMap_surjective f hf
    (W.subgroup.comap f) (Subgroup.ker_le_comap f W.subgroup) x
  have hzx : f z = (x : H) := congrArg Subtype.val hz
  rw [descend_localCharacter f hf hker (lift f hf hker W) z x hzx]
  exact lift_localCharacter f hf hker W z y (hzx.trans hxy)

@[simp] theorem lift_descend (W : CharacterWeight p K G) :
    lift f hf hker (descend f hf hker W) = W := by
  apply descend_injective f hf hker
  exact descend_lift f hf hker (descend f hf hker W)

/-- A proved equivalence on the actual raw ordinary-character weights. -/
def weightEquiv : CharacterWeight p K G ≃ CharacterWeight p K H where
  toFun := descend f hf hker
  invFun := lift f hf hker
  left_inv := lift_descend f hf hker
  right_inv := descend_lift f hf hker

theorem descend_rightTwist (alpha : MulAut G) (beta : MulAut H)
    (square : ∀ g, f (alpha g) = beta (f g))
    (W : CharacterWeight p K G) :
    descend f hf hker (W.rightTwist alpha) =
      (descend f hf hker W).rightTwist beta := by
  have hQ : (W.subgroup.comap alpha.toMonoidHom).map f =
      (W.subgroup.map f).comap beta.toMonoidHom := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨alpha x, hx, square x⟩
    · intro hy
      obtain ⟨x, rfl⟩ := hf y
      refine ⟨x, ?_, rfl⟩
      change alpha x ∈ W.subgroup
      have hx : f (alpha x) ∈ W.subgroup.map f := by
        rw [square]
        exact hy
      have hx' : alpha x ∈ (W.subgroup.map f).comap f := hx
      rwa [Subgroup.comap_map_eq_self (kernel_le_radical f hker W)] at hx'
  apply weight_eq_of_values _ _ hQ
  intro x y hxy
  obtain ⟨z, hz⟩ := normalizerMap_surjective f hf
    (W.rightTwist alpha).subgroup
    (kernel_le_radical f hker (W.rightTwist alpha)) x
  have hzx : f z = (x : H) := congrArg Subtype.val hz
  rw [descend_localCharacter f hf hker (W.rightTwist alpha) z x hzx,
    rightTwist_localCharacter, rightTwist_localCharacter]
  symm
  apply descend_localCharacter f hf hker W
    (rightNormalizerEquiv alpha W.subgroup z)
    (rightNormalizerEquiv beta (W.subgroup.map f) y)
  change f (alpha z) = beta y
  rw [square, hzx, hxy]

theorem lift_rightTwist (alpha : MulAut G) (beta : MulAut H)
    (square : ∀ g, f (alpha g) = beta (f g))
    (W : CharacterWeight p K H) :
    lift f hf hker (W.rightTwist beta) =
      (lift f hf hker W).rightTwist alpha := by
  apply descend_injective f hf hker
  rw [descend_lift, descend_rightTwist f hf hker alpha beta square, descend_lift]

/-- The proved raw weight equivalence descends through local-character
isomorphism, which is literal equality on this set of weights defined by characters. -/
def isoClassEquiv :
    CharacterWeight.IsoClass (p := p) (K := K) (G := G) ≃
      CharacterWeight.IsoClass (p := p) (K := K) (G := H) :=
  Quotient.congr (weightEquiv f hf hker) (by
    intro W V
    change CharacterWeight.Isomorphic W V ↔
      CharacterWeight.Isomorphic (descend f hf hker W) (descend f hf hker V)
    constructor
    · intro h
      have heq := congrArg (descend f hf hker) (CharacterWeight.eq_of_isomorphic h)
      rw [heq]
      exact CharacterWeight.isomorphic_refl _
    · intro h
      have heq := descend_injective f hf hker (CharacterWeight.eq_of_isomorphic h)
      rw [heq]
      exact CharacterWeight.isomorphic_refl _)

@[simp] theorem isoClassEquiv_mk (W : CharacterWeight p K G) :
    isoClassEquiv f hf hker (Quotient.mk'' W) =
      Quotient.mk'' (descend f hf hker W) := rfl

@[simp] theorem isoClassEquiv_symm_mk (W : CharacterWeight p K H) :
    (isoClassEquiv f hf hker).symm (Quotient.mk'' W) =
      Quotient.mk'' (lift f hf hker W) := rfl

theorem isoClassEquiv_rightTwist (alpha : MulAut G) (beta : MulAut H)
    (square : ∀ g, f (alpha g) = beta (f g))
    (x : CharacterWeight.IsoClass (p := p) (K := K) (G := G)) :
    isoClassEquiv f hf hker (CharacterWeight.rightTwistIsoClass alpha x) =
      CharacterWeight.rightTwistIsoClass beta (isoClassEquiv f hf hker x) := by
  refine Quotient.inductionOn x ?_
  intro W
  change Quotient.mk'' (descend f hf hker (W.rightTwist alpha)) =
    Quotient.mk'' ((descend f hf hker W).rightTwist beta)
  rw [descend_rightTwist f hf hker alpha beta square W]

theorem isoClassEquiv_conjugation (g : G)
    (x : CharacterWeight.IsoClass (p := p) (K := K) (G := G)) :
    isoClassEquiv f hf hker (g • x) = f g • isoClassEquiv f hf hker x := by
  change isoClassEquiv f hf hker
    (CharacterWeight.rightTwistIsoClass (MulAut.conj g⁻¹) x) =
      CharacterWeight.rightTwistIsoClass (MulAut.conj (f g)⁻¹)
        (isoClassEquiv f hf hker x)
  apply isoClassEquiv_rightTwist f hf hker
  intro y
  simp

theorem orbitRel_iff (x y : CharacterWeight.IsoClass (p := p) (K := K) (G := G)) :
    MulAction.orbitRel G _ x y ↔
      MulAction.orbitRel H _ (isoClassEquiv f hf hker x)
        (isoClassEquiv f hf hker y) := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨f g, (isoClassEquiv_conjugation f hf hker g y).symm⟩
  · rintro ⟨h, hh⟩
    obtain ⟨g, rfl⟩ := hf h
    refine ⟨g, (isoClassEquiv f hf hker).injective ?_⟩
    rw [isoClassEquiv_conjugation]
    exact hh

/-- The actual ambient-conjugacy classes of character weights are in
bijection across every finite group surjection with an ell-group kernel. -/
def conjugacyClassEquiv :
    CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G) ≃
      CharacterWeight.ConjugacyClass (p := p) (K := K) (G := H) :=
  Quotient.congr (isoClassEquiv f hf hker) (orbitRel_iff f hf hker)

@[simp] theorem conjugacyClassEquiv_mk
    (x : CharacterWeight.IsoClass (p := p) (K := K) (G := G)) :
    conjugacyClassEquiv f hf hker (Quotient.mk'' x) =
      Quotient.mk'' (isoClassEquiv f hf hker x) := rfl

@[simp] theorem conjugacyClassEquiv_symm_mk
    (x : CharacterWeight.IsoClass (p := p) (K := K) (G := H)) :
    (conjugacyClassEquiv f hf hker).symm (Quotient.mk'' x) =
      Quotient.mk'' ((isoClassEquiv f hf hker).symm x) := rfl

theorem conjugacyClassEquiv_rightTwist (alpha : MulAut G) (beta : MulAut H)
    (square : ∀ g, f (alpha g) = beta (f g))
    (x : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G)) :
    conjugacyClassEquiv f hf hker
        (CharacterWeight.rightTwistConjugacyClass alpha x) =
      CharacterWeight.rightTwistConjugacyClass beta
        (conjugacyClassEquiv f hf hker x) := by
  refine Quotient.inductionOn x ?_
  intro x
  change Quotient.mk''
      (isoClassEquiv f hf hker (CharacterWeight.rightTwistIsoClass alpha x)) =
    Quotient.mk''
      (CharacterWeight.rightTwistIsoClass beta (isoClassEquiv f hf hker x))
  rw [isoClassEquiv_rightTwist f hf hker alpha beta square x]

theorem conjugacyClassEquiv_smul (alpha : MulAut G) (beta : MulAut H)
    (square : ∀ g, f (alpha g) = beta (f g))
    (x : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G)) :
    conjugacyClassEquiv f hf hker (MulOpposite.op alpha • x) =
      MulOpposite.op beta • conjugacyClassEquiv f hf hker x :=
  conjugacyClassEquiv_rightTwist f hf hker alpha beta square x

/-- The literal quotient specialization, with no ell-core identification. -/
def quotientWeightEquiv (P : Subgroup G) [P.Normal] (hP : IsPGroup p P) :
    CharacterWeight p K G ≃ CharacterWeight p K (G ⧸ P) :=
  weightEquiv (p := p) (K := K) (QuotientGroup.mk' P) (QuotientGroup.mk'_surjective P)
    (by
      change IsPGroup p (QuotientGroup.mk' P).ker
      rw [QuotientGroup.ker_mk']
      exact hP)

/-- The literal quotient specialization on actual weight classes. -/
def quotientConjugacyClassEquiv (P : Subgroup G) [P.Normal]
    (hP : IsPGroup p P) :
    CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G) ≃
      CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G ⧸ P) :=
  conjugacyClassEquiv (p := p) (K := K)
    (QuotientGroup.mk' P) (QuotientGroup.mk'_surjective P)
    (by
      change IsPGroup p (QuotientGroup.mk' P).ker
      rw [QuotientGroup.ker_mk']
      exact hP)

end ModularRep.PaperProofs.TypeBCentralKernelWeightTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
