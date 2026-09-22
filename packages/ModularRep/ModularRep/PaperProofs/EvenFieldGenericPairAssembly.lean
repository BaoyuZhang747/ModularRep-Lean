import ModularRep.PaperProofs.EvenFieldDependentGenericPair

/-!
# Construction in the finite-subgroup dependent-pair prototype

This file joins separate subgroup and normaliser-character fixedness
statements in the finite-subgroup model.  It contains no orbit fixedness
hypothesis, but it is not a model of the manuscript's algebraic `e`-torus and
therefore receives no proof credit for Lemma 3.6.
-/

namespace ModularRep.PaperProofs.EvenFieldGenericPairAssembly

open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs.EvenFieldDependentGenericPair

universe u

variable {k G : Type u} [Field k] [Group G]

/-- The automorphism induced on `N_G(T)` by an automorphism stabilising `T`.
The equality is oriented as `alpha(T) = T`, matching the output of the torus
calculation. -/
def normalizerAutOfStable (alpha : MulAut G) (T : Subgroup G)
    (stable : T.map alpha.toMonoidHom = T) :
    MulAut (Subgroup.normalizer (T : Set G)) :=
  (normalizerEquiv alpha T).trans (normalizerCongr stable)

@[simp]
theorem normalizerAutOfStable_coe (alpha : MulAut G) (T : Subgroup G)
    (stable : T.map alpha.toMonoidHom = T)
    (x : Subgroup.normalizer (T : Set G)) :
    ((normalizerAutOfStable alpha T stable x :
      Subgroup.normalizer (T : Set G)) : G) = alpha x := by
  rw [normalizerAutOfStable, MulEquiv.trans_apply, normalizerCongr_coe,
    normalizerEquiv_coe]

/-- Separate fixedness of the subgroup and of its actual normaliser character
gives semantic fixedness of the dependent pair. -/
theorem isTransportedBy_self_of_character_fixed
    (alpha : MulAut G) (P : GenericLocalPair k G)
    (subgroup_fixed : P.1.map alpha.toMonoidHom = P.1)
    (character_fixed :
      twist k _ P.2 (normalizerAutOfStable alpha P.1 subgroup_fixed) = P.2) :
    IsTransportedBy alpha P P := by
  let hsub : P.1 = P.1.map alpha.toMonoidHom := subgroup_fixed.symm
  refine ⟨hsub, ?_⟩
  intro x
  have helement :
      transportedNormalizerElement alpha P P hsub x =
        normalizerAutOfStable alpha P.1 subgroup_fixed x := by
    apply Subtype.ext
    rw [transportedNormalizerElement_coe, normalizerAutOfStable_coe]
  rw [helement]
  have hvalue := congrArg
    (fun chi : Irr k (Subgroup.normalizer (P.1 : Set G)) ↦ chi x)
    character_fixed
  exact hvalue

/-- Right-action endpoint obtained from the separately proved torus and
normaliser-character equalities. -/
theorem conjugacyClass_fixed_of_components_right
    (sigma tau : MulAut G) (h : G)
    (htau : tau = MulAut.conj h * sigma)
    (P : GenericLocalPair k G)
    (subgroup_fixed : P.1.map tau.symm.toMonoidHom = P.1)
    (character_fixed :
      twist k _ P.2
        (normalizerAutOfStable tau P.1 (by
          have hmap := congrArg
            (fun T : Subgroup G ↦ T.map tau.toMonoidHom) subgroup_fixed
          simpa [Subgroup.map_map] using hmap.symm)) = P.2) :
    conjugacyClass (rightTransportPair P sigma) = conjugacyClass P := by
  have subgroup_fixed_forward : P.1.map tau.toMonoidHom = P.1 := by
    have hmap := congrArg
      (fun T : Subgroup G ↦ T.map tau.toMonoidHom) subgroup_fixed
    simpa [Subgroup.map_map] using hmap.symm
  let tauN := normalizerAutOfStable tau P.1 subgroup_fixed_forward
  let hsub : P.1 = P.1.map tau.symm.toMonoidHom := subgroup_fixed.symm
  have htransport : IsTransportedBy tau.symm P P := by
    refine ⟨hsub, ?_⟩
    intro x
    have helement :
        transportedNormalizerElement tau.symm P P hsub x = tauN.symm x := by
      apply Subtype.ext
      apply tau.injective
      rw [transportedNormalizerElement_coe]
      rw [tau.apply_symm_apply]
      have hcoe := normalizerAutOfStable_coe tau P.1
        subgroup_fixed_forward (tauN.symm x)
      calc
        (x : G) = ((tauN (tauN.symm x) :
            Subgroup.normalizer (P.1 : Set G)) : G) :=
          congrArg Subtype.val (tauN.apply_symm_apply x).symm
        _ = tau (tauN.symm x :
            Subgroup.normalizer (P.1 : Set G)) := hcoe
    rw [helement]
    have hvalue := congrArg
      (fun chi : Irr k (Subgroup.normalizer (P.1 : Set G)) ↦
        chi (tauN.symm x)) character_fixed
    change P.2 (tauN (tauN.symm x)) = P.2 (tauN.symm x) at hvalue
    rw [tauN.apply_symm_apply] at hvalue
    exact hvalue.symm
  have hpair : rightTransportPair P tau = P := by
    exact (transportPair_isTransported tau.symm P).right_unique htransport
  exact conjugacyClass_fixed_of_innerTwist_right sigma tau h htau P hpair

end ModularRep.PaperProofs.EvenFieldGenericPairAssembly


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
