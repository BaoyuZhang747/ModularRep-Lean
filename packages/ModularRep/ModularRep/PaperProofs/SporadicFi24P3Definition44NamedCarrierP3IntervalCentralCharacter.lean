import ModularRep.Navarro414IntervalCentralCharacterSource
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3IntervalSimple

/-! Derive the central-function equality in Navarro (4.14) on its full
subgroup interval. The two coefficient restrictions agree on the local
centralizer; normal-p kernel action therefore makes every local catalogue
character agree on them. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3IntervalCentralCharacter

open ModularRep
open SporadicFi24P3Definition44NamedCarrierP3IntervalSimple

theorem interval_difference_brauerRestriction_eq_zero
    {p : ℕ} {k G : Type*}
    [CommRing k] [CharP k p] [Fact p.Prime]
    [Group G] [Finite G]
    (Q H : Subgroup G)
    (I : CentralBrauerInterval (p := p) Q H)
    (z : GroupAlgebraCenter k G) :
    centralBrauerRestriction (Q.subgroupOf H)
      (centerCoeffRestrict H z -
        centralBrauerMapTo (k := k) (p := p) Q H
          I.isPGroup I.centralizer_le I.le_normalizer z) = 0 := by
  apply Subtype.ext
  ext c
  let cG : centralizerOf Q := ⟨((c : H) : G), by
    apply Subgroup.mem_centralizer_iff.mpr
    intro q hq
    let qH : H := ⟨q, I.p_le hq⟩
    have hqH : qH ∈ Q.subgroupOf H := hq
    exact congrArg (fun x : H => (x : G))
      (Subgroup.mem_centralizer_iff.mp c.property qH hqH)⟩
  have hinc :
      Subgroup.inclusion I.centralizer_le cG = (c : H) :=
    Subtype.ext rfl
  change
    (z : k[G]).coeff (cG : G) -
      ((centralBrauerMapTo (k := k) (p := p) Q H
          I.isPGroup I.centralizer_le I.le_normalizer z :
            GroupAlgebraCenter k H) : k[H]).coeff (c : H) = 0
  apply sub_eq_zero.mpr
  symm
  rw [centralBrauerMapTo_apply]
  change
    Finsupp.mapDomain (Subgroup.inclusion I.centralizer_le)
      (((centralBrauerMap (k := k) (p := p) Q I.isPGroup z :
          GroupAlgebraCenter k (centralizerOf Q)) :
            k[centralizerOf Q])).coeff (c : H) =
      (z : k[G]).coeff (cG : G)
  rw [← hinc,
    Finsupp.mapDomain_apply
      (Subgroup.inclusion_injective I.centralizer_le)]
  exact centralBrauerRestriction_coeff Q z cG

universe u

theorem interval_central_character_source
    {p : ℕ} {k G : Type u} {B : Type*}
    [Field k] [IsAlgClosed k] [CharP k p] [Fact p.Prime]
    [Group G] [Fintype G] [Fintype B]
    {Q H : Subgroup G} {e : B → k[H]}
    (I : CentralBrauerInterval (p := p) Q H) :
    let _ : Fintype H := Fintype.ofFinite H
    ∀ (blocks : BlockIdempotentDecomposition e)
      (catalogue : BlockCentralCharacterCatalogue blocks),
      Navarro414IntervalCentralCharacterSource I blocks catalogue := by
  let _ : Fintype H := Fintype.ofFinite H
  dsimp only
  intro blocks catalogue
  let : (Q.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer I.p_le).mpr I.le_normalizer
  refine ⟨fun b => ?_⟩
  apply LinearMap.ext
  intro z
  have hz := catalogue_zero_of_normal_p_restriction_zero
    blocks catalogue (Q.subgroupOf H) I.isPGroup.comap_subtype
    (centerCoeffRestrict H z -
      centralBrauerMapTo (k := k) (p := p) Q H
        I.isPGroup I.centralizer_le I.le_normalizer z)
    (interval_difference_brauerRestriction_eq_zero Q H I z) b
  rw [map_sub, sub_eq_zero] at hz
  exact hz

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3IntervalCentralCharacter


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
