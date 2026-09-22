import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Cyclic quotients inherited by subgroups

This file formalises the elementary group theoretic step used in the proof of
Lemma 3.10 of the manuscript.  If `P` is normal in `A` and `A / P` is cyclic,
then every subgroup `K` of `A` has cyclic quotient by `K ∩ P`.  In Lean the
intersection is represented as the pullback `P.comap K.subtype`, a subgroup of
the type `K`.

The final theorem also checks that this intersection is a `p`-group whenever
`P` is.  Thus it supplies the normal `p`-subgroup with cyclic quotient used in
the manuscript's proof that subgroups of a `p`-hypoelementary group are again
`p`-hypoelementary.  Mathlib does not currently package the largest normal
`p`-subgroup `O_p(K)`.  We therefore state the final passage for an arbitrary
normal subgroup `Q` containing `K ∩ P`; taking `Q = O_p(K)` gives the step
used in the manuscript.
-/

namespace Formalisation

variable {A : Type*} [Group A]

/-- Restricting the quotient map `A → A / P` to `K` has kernel `K ∩ P`. -/
theorem ker_quotientMap_restrict (P K : Subgroup A) [P.Normal] :
    ((QuotientGroup.mk' P).comp K.subtype).ker = P.comap K.subtype := by
  rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']

/-- If `A / P` is cyclic, then `K / (K ∩ P)` is cyclic for every subgroup
`K` of `A`. -/
theorem subgroup_quotient_inter_isCyclic (P K : Subgroup A) [P.Normal]
    [IsCyclic (A ⧸ P)] : IsCyclic (K ⧸ P.comap K.subtype) := by
  let f : K →* A ⧸ P := (QuotientGroup.mk' P).comp K.subtype
  have hker : f.ker = P.comap K.subtype := by
    simpa [f] using ker_quotientMap_restrict P K
  have hcyclic : IsCyclic (K ⧸ f.ker) :=
    isCyclic_of_injective (QuotientGroup.kerLift f)
      (QuotientGroup.kerLift_injective f)
  exact (QuotientGroup.quotientMulEquivOfEq hker).isCyclic.mp hcyclic

/-- The intersection of a `p`-subgroup with any subgroup is a `p`-subgroup. -/
theorem subgroup_inter_isPGroup {p : ℕ} (P K : Subgroup A)
    (hP : IsPGroup p P) : IsPGroup p (P.comap K.subtype) :=
  hP.comap_subtype

/-- Enlarging the normal subgroup in the denominator preserves cyclicity of
the quotient. -/
theorem cyclic_quotient_of_normal_supergroup (P Q : Subgroup A)
    [P.Normal] [Q.Normal] (hPQ : P ≤ Q) [IsCyclic (A ⧸ P)] :
    IsCyclic (A ⧸ Q) := by
  let hPQ' : P ≤ Q.comap (MonoidHom.id A) := by
    simpa using hPQ
  let f : A ⧸ P →* A ⧸ Q :=
    QuotientGroup.map P Q (MonoidHom.id A) hPQ'
  apply isCyclic_of_surjective f
  apply QuotientGroup.map_surjective_of_surjective P Q (MonoidHom.id A)
  simpa using QuotientGroup.mk'_surjective Q

/-- If a normal subgroup of `K` contains `K ∩ P`, then quotienting `K` by
that larger subgroup is still cyclic.  In the finite group argument of the
manuscript, the larger subgroup is `O_p(K)`. -/
theorem subgroup_quotient_of_inter_le_isCyclic (P K : Subgroup A) [P.Normal]
    [IsCyclic (A ⧸ P)] (Q : Subgroup K) [Q.Normal]
    (hQ : P.comap K.subtype ≤ Q) : IsCyclic (K ⧸ Q) := by
  let _ : IsCyclic (K ⧸ P.comap K.subtype) :=
    subgroup_quotient_inter_isCyclic P K
  exact cyclic_quotient_of_normal_supergroup (P.comap K.subtype) Q hQ

/-- A normal `p`-subgroup with cyclic quotient restricts to such a subgroup in
every subgroup of the ambient group. -/
theorem subgroup_has_normal_pSubgroup_with_cyclic_quotient {p : ℕ}
    (P K : Subgroup A) [P.Normal] (hP : IsPGroup p P)
    [IsCyclic (A ⧸ P)] :
    (P.comap K.subtype).Normal ∧
      IsPGroup p (P.comap K.subtype) ∧
      IsCyclic (K ⧸ P.comap K.subtype) := by
  exact ⟨inferInstance, subgroup_inter_isPGroup P K hP,
    subgroup_quotient_inter_isCyclic P K⟩

end Formalisation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
