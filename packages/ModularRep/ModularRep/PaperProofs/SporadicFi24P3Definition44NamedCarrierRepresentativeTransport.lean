import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeMaps
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierABC

/-!
# The actual raw pair at any radical representative

Equality of the two quotient weight classes supplies an inner conjugator
of the entire raw pair. It therefore transports the ordinary character as
well as the subgroup. Composing the ambient embedding with this inner
automorphism keeps its image and the embedded radical unchanged.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeTransport

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierABC
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeMaps

universe u v

variable {p : ℕ} {K X : Type u} [Field K] [CharZero K] [Group X] [Fintype X]

theorem exists_inner_raw (W V : CharacterWeight p K X)
    (h : (Quotient.mk'' (Quotient.mk'' V) : ConjugacyClass (p := p) (K := K) (G := X)) =
      Quotient.mk'' (Quotient.mk'' W)) :
    ∃ g : X, W.rightTwist (MulAut.conj g⁻¹) = V := by
  obtain ⟨g, hg⟩ := Quotient.exact h
  exact ⟨g, CharacterWeight.eq_of_isomorphic (Quotient.exact hg)⟩

def backNormalizerEquiv (W V : CharacterWeight p K X) (alpha : MulAut X)
    (hpair : W.rightTwist alpha = V) :
    Subgroup.normalizer (V.subgroup : Set X) ≃*
      Subgroup.normalizer (W.subgroup : Set X) := by
  subst V
  exact rightNormalizerEquiv alpha W.subgroup

theorem backNormalizerEquiv_coe (W V : CharacterWeight p K X) (alpha : MulAut X)
    (hpair : W.rightTwist alpha = V) (n : Subgroup.normalizer (V.subgroup : Set X)) :
    (backNormalizerEquiv W V alpha hpair n : X) = alpha n := by
  subst V
  rfl

theorem ordinary_normalizer_values (W V : CharacterWeight p K X) (alpha : MulAut X)
    (hpair : W.rightTwist alpha = V) (n : Subgroup.normalizer (V.subgroup : Set X)) :
    V.localCharacter (QuotientGroup.mk n) =
      W.localCharacter (QuotientGroup.mk (backNormalizerEquiv W V alpha hpair n)) := by
  subst V
  change W.localCharacter
    (rightNormalizerQuotientEquiv alpha W.subgroup (QuotientGroup.mk n)) = _
  rfl

theorem subgroup_map_back (W V : CharacterWeight p K X) (alpha : MulAut X)
    (hpair : W.rightTwist alpha = V) : V.subgroup.map alpha.toMonoidHom = W.subgroup := by
  subst V
  exact Subgroup.map_comap_eq_self_of_surjective alpha.surjective W.subgroup

theorem embedded_radical_eq {A : Type v} [Group A]
    (W V : CharacterWeight p K X) (alpha : MulAut X)
    (hpair : W.rightTwist alpha = V) (embed : X →* A) :
    V.subgroup.map (embed.comp alpha.toMonoidHom) = W.subgroup.map embed := by
  rw [← Subgroup.map_map, subgroup_map_back W V alpha hpair]

omit [Fintype X] in
theorem embedded_base_eq {A : Type v} [Group A]
    (alpha : MulAut X) (embed : X →* A) :
    (embed.comp alpha.toMonoidHom).range = embed.range := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr alpha.surjective,
    ← MonoidHom.range_eq_map]

theorem global_inner_values {k : Type u} [Field k] [CharP k p] [IsAlgClosed k]
    (iota : PrimeRegularRootEmbedding p k K X) (phi : IBr iota)
    (g : X) (x : PrimeRegularElement (G := X) p) :
    phi.1 (PrimeRegularElement.map (MulAut.conj g⁻¹).toMonoidHom x) = phi.1 x :=
  phi.1.map_conj g⁻¹ x

theorem exists_selected_inner_raw
    (P : Definition35Problem.{u}) (M : EquivariantMatch P)
    (Q : RadicalSubgroup (p := P.p) (G := P.H))
    (hQ : radicalClass (M.Omega M.theta.1) =
      (Quotient.mk'' Q : RadicalConjugacyClass (p := P.p) (G := P.H))) :
    ∃ g : P.H,
      (selectedCharacterWeight P.blockSource P.block M.weight).rightTwist (MulAut.conj g⁻¹) =
        characterWeightAt P.iota.prime Q (localMap P.iota M.Omega P.iota.prime Q ⟨M.theta.1, hQ⟩) := by
  apply exists_inner_raw
  exact (localMap_class P.iota M.Omega P.iota.prime Q ⟨M.theta.1, hQ⟩).trans
    (M.matched.symm.trans (selectedCharacterWeight_spec P.blockSource P.block M.weight).symm)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
