import ModularRep.PaperProofs.OddTwoCentralTwoGlobalInflation

/-!
# Actual character weights through the central two-quotient

The forward raw map is the checked `quotientPair`: the subgroup is its
image under the real projection and the character is the selected pair's
own character transported along the actual normalizer-quotient equivalence.
The inverse below uses the subgroup preimage and the inverse of this same
local equivalence. No weight bijection is a source field.

Raw invertibility and the two quotient descents are K. The precise
automorphism naturality equation is the standard transport input already
used for representation weights in `NormalCoreLemma48SourceInstantiation`;
here it is imposed only on these literal character maps. MRR Lemma 6.3,
printed p.359, uses this actual normal-core weight identification. The
previous module proves that the normal two-core of Sp is its actual centre.

The block restriction below must additionally bind block induction to the
same central projection. Navarro 9.10 alone is not an induction theorem.
No local triple relation or final iBAW conclusion is asserted here.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.OddTwoCentralTwoWeightInflation

open ModularRep.CharacterWeight
open ModularRep.PaperProofs.OddTwoCentralTwoRelationInflation
open ModularRep.PaperProofs.OddTwoCentralTwoGlobalInflation
open ModularRep.PaperProofs.OddTwoUniversalPrimeToTwoSelfCover

universe u

section ActualRawPairs

variable {K G H : Type u} [Field K] [CharZero K]
variable [Group G] [Finite G] [Group H] [Finite H]
variable (f : G →* H) (hf : Function.Surjective f)
variable (hkernel : IsPGroup 2 f.ker)

/-- The canonical local quotient equivalence for the actual preimage
subgroup. The final cast is only `map (comap Q) = Q`. -/
def liftLocalQuotientEquiv (Q : Subgroup H) :
    NormalizerQuotient (Q.comap f) ≃* NormalizerQuotient Q :=
  (normalizerQuotientEquivOfSurjectiveOfKerLE f hf (Q.comap f)
    (Subgroup.ker_le_comap f Q)).trans
    (MulEquiv.cast (M := fun R : Subgroup H => NormalizerQuotient R)
      (Subgroup.map_comap_eq_self_of_surjective hf Q))

/-- The inverse raw pair is computed from the subgroup preimage and its
own ordinary character. No character choice or uniqueness is needed. -/
def liftPair (W : CharacterWeight 2 K H) : CharacterWeight 2 K G where
  prime := W.prime
  subgroup := W.subgroup.comap f
  radical := (isRadicalSubgroup_iff_map_surjective_of_ker_le f hf
    (W.subgroup.comap f) (Subgroup.ker_le_comap f W.subgroup) hkernel).mpr
      (by simpa only [Subgroup.map_comap_eq_self_of_surjective hf] using W.radical)
  localCharacter := OrdinaryIrreducibleCharacter.mapEquiv W.localCharacter
    (liftLocalQuotientEquiv f hf W.subgroup).symm
  defectZero := W.defectZero.mapEquiv (liftLocalQuotientEquiv f hf W.subgroup).symm

@[simp] theorem liftPair_subgroup (W : CharacterWeight 2 K H) :
    (liftPair f hf hkernel W).subgroup = W.subgroup.comap f := rfl

theorem liftPair_localCharacter (W : CharacterWeight 2 K H)
    (x : NormalizerQuotient (W.subgroup.comap f)) :
    (liftPair f hf hkernel W).localCharacter x =
      W.localCharacter (liftLocalQuotientEquiv f hf W.subgroup x) := rfl

private theorem castLocalCharacter_mapEquiv
    {Q R : Subgroup H} (h : Q = R) {L : Type u} [Group L] [Finite L]
    (chi : OrdinaryIrreducibleCharacter.Irr K L)
    (e : L ≃* NormalizerQuotient Q) :
    castLocalCharacter h (OrdinaryIrreducibleCharacter.mapEquiv chi e) =
      OrdinaryIrreducibleCharacter.mapEquiv chi
        (e.trans (MulEquiv.cast
          (M := fun S : Subgroup H => NormalizerQuotient S) h)) := by
  subst R
  rfl

/-- Quotienting the computed lift recovers the same raw pair, including
its own ordinary character. -/
theorem quotientPair_liftPair (W : CharacterWeight 2 K H) :
    quotientPair f hf hkernel (liftPair f hf hkernel W) = W := by
  apply eq_of_isomorphic
  refine ⟨Subgroup.map_comap_eq_self_of_surjective hf W.subgroup, ?_⟩
  change castLocalCharacter
      (Subgroup.map_comap_eq_self_of_surjective hf W.subgroup)
      (OrdinaryIrreducibleCharacter.mapEquiv
        (OrdinaryIrreducibleCharacter.mapEquiv W.localCharacter
          (liftLocalQuotientEquiv f hf W.subgroup).symm)
        (normalizerQuotientEquivOfSurjectiveOfKerLE f hf (W.subgroup.comap f)
          (Subgroup.ker_le_comap f W.subgroup))) = W.localCharacter
  rw [castLocalCharacter_mapEquiv]
  apply OrdinaryIrreducibleCharacter.ext
  intro x
  change W.localCharacter
      (liftLocalQuotientEquiv f hf W.subgroup
        ((liftLocalQuotientEquiv f hf W.subgroup).symm x)) = W.localCharacter x
  rw [MulEquiv.apply_symm_apply]

/-- The actual raw quotient map is injective; containment of the kernel
comes from each pair's own radicality. -/
theorem quotientPair_injective : Function.Injective (quotientPair f hf hkernel
    (K := K)) := by
  intro W V h
  have hQ : W.subgroup = V.subgroup :=
    Subgroup.map_injective_of_ker_le f
      (kernel_le_selected f hkernel W) (kernel_le_selected f hkernel V)
      (congrArg CharacterWeight.subgroup h)
  rcases W with ⟨hp, Q, hrad, chi, hdz⟩
  rcases V with ⟨hp', R, hrad', psi, hdz'⟩
  change Q = R at hQ
  subst R
  have hchar : OrdinaryIrreducibleCharacter.mapEquiv chi
      (normalizerQuotientEquivOfSurjectiveOfKerLE f hf Q
        (kernel_le_selected f hkernel
          (⟨hp, Q, hrad, chi, hdz⟩ : CharacterWeight 2 K G))) =
    OrdinaryIrreducibleCharacter.mapEquiv psi
      (normalizerQuotientEquivOfSurjectiveOfKerLE f hf Q
        (kernel_le_selected f hkernel
          (⟨hp, Q, hrad, chi, hdz⟩ : CharacterWeight 2 K G))) := by
    have hsame : Isomorphic
        (quotientPair f hf hkernel (⟨hp, Q, hrad, chi, hdz⟩ : CharacterWeight 2 K G))
        (quotientPair f hf hkernel (⟨hp', Q, hrad', psi, hdz'⟩ : CharacterWeight 2 K G)) := by
      rw [h]
      exact isomorphic_refl _
    rcases hsame with ⟨hsub, hc⟩
    exact hc
  have hc : chi = psi := by
    apply OrdinaryIrreducibleCharacter.ext
    intro x
    let e := normalizerQuotientEquivOfSurjectiveOfKerLE f hf Q
      (kernel_le_selected f hkernel
        (⟨hp, Q, hrad, chi, hdz⟩ : CharacterWeight 2 K G))
    have hx := congrArg (fun theta => theta (e x)) hchar
    change chi (e.symm (e x)) = psi (e.symm (e x)) at hx
    simpa only [MulEquiv.symm_apply_apply] using hx
  subst psi
  rfl

theorem liftPair_quotientPair (W : CharacterWeight 2 K G) :
    liftPair f hf hkernel (quotientPair f hf hkernel W) = W := by
  apply quotientPair_injective f hf hkernel
  exact quotientPair_liftPair f hf hkernel (quotientPair f hf hkernel W)

/-- An equivalence constructed from the fixed quotient and preimage maps.
It is not supplied by a source certificate. -/
def rawPairEquiv : CharacterWeight 2 K G ≃ CharacterWeight 2 K H where
  toFun := quotientPair f hf hkernel
  invFun := liftPair f hf hkernel
  left_inv := liftPair_quotientPair f hf hkernel
  right_inv := quotientPair_liftPair f hf hkernel

/-- The exact naturality boundary for the already fixed raw maps. This is
the character-function version of the existing standard normal-core
transport input. The square uses the real group homomorphism. -/
structure ActualQuotientNaturality : Prop where
  rightTwist : ∀ (alpha : MulAut G) (beta : MulAut H),
    (∀ g, f (alpha g) = beta (f g)) → ∀ W : CharacterWeight 2 K G,
      quotientPair f hf hkernel (W.rightTwist alpha) =
        (quotientPair f hf hkernel W).rightTwist beta

def quotientIsoClass : CharacterWeight.IsoClass (p := 2) (K := K) (G := G) →
    CharacterWeight.IsoClass (p := 2) (K := K) (G := H) :=
  Quotient.map (quotientPair f hf hkernel) (by
    intro W V h
    cases eq_of_isomorphic h
    exact isomorphic_refl _)

def liftIsoClass : CharacterWeight.IsoClass (p := 2) (K := K) (G := H) →
    CharacterWeight.IsoClass (p := 2) (K := K) (G := G) :=
  Quotient.map (liftPair f hf hkernel) (by
    intro W V h
    cases eq_of_isomorphic h
    exact isomorphic_refl _)

@[simp] theorem liftIsoClass_quotientIsoClass
    (x : CharacterWeight.IsoClass (p := 2) (K := K) (G := G)) :
    liftIsoClass f hf hkernel (quotientIsoClass f hf hkernel x) = x := by
  refine Quotient.inductionOn x ?_
  intro W
  exact congrArg Quotient.mk'' (liftPair_quotientPair f hf hkernel W)

@[simp] theorem quotientIsoClass_liftIsoClass
    (x : CharacterWeight.IsoClass (p := 2) (K := K) (G := H)) :
    quotientIsoClass f hf hkernel (liftIsoClass f hf hkernel x) = x := by
  refine Quotient.inductionOn x ?_
  intro W
  exact congrArg Quotient.mk'' (quotientPair_liftPair f hf hkernel W)

def isoClassEquiv : CharacterWeight.IsoClass (p := 2) (K := K) (G := G) ≃
    CharacterWeight.IsoClass (p := 2) (K := K) (G := H) where
  toFun := quotientIsoClass f hf hkernel
  invFun := liftIsoClass f hf hkernel
  left_inv := liftIsoClass_quotientIsoClass f hf hkernel
  right_inv := quotientIsoClass_liftIsoClass f hf hkernel

namespace ActualQuotientNaturality

variable {f hf hkernel} (T : ActualQuotientNaturality (K := K) f hf hkernel)

include T

theorem quotientIsoClass_rightTwist (alpha : MulAut G) (beta : MulAut H)
    (commutes : ∀ g, f (alpha g) = beta (f g))
    (x : CharacterWeight.IsoClass (p := 2) (K := K) (G := G)) :
    quotientIsoClass f hf hkernel (rightTwistIsoClass alpha x) =
      rightTwistIsoClass beta (quotientIsoClass f hf hkernel x) := by
  refine Quotient.inductionOn x ?_
  intro W
  exact congrArg Quotient.mk'' (T.rightTwist alpha beta commutes W)

theorem quotientIsoClass_conjugation (g : G)
    (x : CharacterWeight.IsoClass (p := 2) (K := K) (G := G)) :
    quotientIsoClass f hf hkernel (g • x) =
      f g • quotientIsoClass f hf hkernel x := by
  apply T.quotientIsoClass_rightTwist (MulAut.conj g⁻¹) (MulAut.conj (f g)⁻¹)
  intro a
  simp only [MulAut.conj_apply, MulAut.conj_inv_apply, map_mul, map_inv, inv_inv]

theorem liftIsoClass_conjugation (g : G)
    (x : CharacterWeight.IsoClass (p := 2) (K := K) (G := H)) :
    liftIsoClass f hf hkernel (f g • x) =
      g • liftIsoClass f hf hkernel x := by
  apply (isoClassEquiv f hf hkernel).injective
  change quotientIsoClass f hf hkernel (liftIsoClass f hf hkernel (f g • x)) =
    quotientIsoClass f hf hkernel (g • liftIsoClass f hf hkernel x)
  rw [quotientIsoClass_liftIsoClass, T.quotientIsoClass_conjugation,
    quotientIsoClass_liftIsoClass]

/-- The forward orbit map is the actual quotient pair on every raw
representative. -/
def quotientConjugacyClass :
    CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := G) →
      CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := H) :=
  Quotient.map (quotientIsoClass f hf hkernel) (by
    intro x y h
    rcases h with ⟨g, rfl⟩
    exact ⟨f g, (T.quotientIsoClass_conjugation g y).symm⟩)

def liftConjugacyClass :
    CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := H) →
      CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := G) :=
  Quotient.map (liftIsoClass f hf hkernel) (by
    intro x y h
    rcases h with ⟨h, rfl⟩
    obtain ⟨g, rfl⟩ := hf h
    exact ⟨g, (T.liftIsoClass_conjugation g y).symm⟩)

@[simp] theorem liftConjugacyClass_quotientConjugacyClass
    (x : CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := G)) :
    T.liftConjugacyClass (T.quotientConjugacyClass x) = x := by
  refine Quotient.inductionOn x ?_
  intro w
  exact congrArg Quotient.mk'' (liftIsoClass_quotientIsoClass f hf hkernel w)

@[simp] theorem quotientConjugacyClass_liftConjugacyClass
    (x : CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := H)) :
    T.quotientConjugacyClass (T.liftConjugacyClass x) = x := by
  refine Quotient.inductionOn x ?_
  intro w
  exact congrArg Quotient.mk'' (quotientIsoClass_liftIsoClass f hf hkernel w)

def conjugacyClassEquiv :
    CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := G) ≃
      CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := H) where
  toFun := T.quotientConjugacyClass
  invFun := T.liftConjugacyClass
  left_inv := T.liftConjugacyClass_quotientConjugacyClass
  right_inv := T.quotientConjugacyClass_liftConjugacyClass

@[simp] theorem conjugacyClassEquiv_mk (W : CharacterWeight 2 K G) :
    T.conjugacyClassEquiv (Quotient.mk'' (Quotient.mk'' W)) =
      Quotient.mk'' (Quotient.mk'' (quotientPair f hf hkernel W)) := rfl

theorem conjugacyClassEquiv_rightTwist (alpha : MulAut G) (beta : MulAut H)
    (commutes : ∀ g, f (alpha g) = beta (f g))
    (x : CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := G)) :
    T.conjugacyClassEquiv (rightTwistConjugacyClass alpha x) =
      rightTwistConjugacyClass beta (T.conjugacyClassEquiv x) := by
  refine Quotient.inductionOn x ?_
  intro w
  exact congrArg Quotient.mk'' (T.quotientIsoClass_rightTwist alpha beta commutes w)

end ActualQuotientNaturality

end ActualRawPairs

end ModularRep.PaperProofs.OddTwoCentralTwoWeightInflation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
