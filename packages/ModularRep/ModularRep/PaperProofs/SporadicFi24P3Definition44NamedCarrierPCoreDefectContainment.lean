import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierNormalPCentralBrauerSupport
import ModularRep.Navarro417LocalDefectSources

/-! The normal p-core lies in every supplied Navarro defect representative.
Nonzero Brauer support is proved internally; the representative's separate
Navarro 4.11 support characterization remains explicit. -/

noncomputable section
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPCoreDefectContainment

open ModularRep
open SporadicFi24P3Definition44NamedCarrierNormalPCentralBrauerSupport

theorem normal_subgroup_le_of_isSubconjugate
    {G : Type*} [Group G] {P D : Subgroup G} [P.Normal]
    (h : P.IsSubconjugate D) : P ≤ D := by
  rcases h with ⟨g, hg⟩
  intro x hx
  apply (Subgroup.mem_map_iff_mem
    (f := (MulAut.conj g).toMonoidHom) (K := D)
    (MulAut.conj g).injective).mp
  exact hg (show MulAut.conj g x ∈ P from
    (inferInstance : P.Normal).conj_mem x hx g)

theorem normal_pSubgroup_hasNonzeroCentralBrauerRestriction
    {p : ℕ} {k G Block : Type*}
    [Field k] [CharP k p] [Fact p.Prime] [Group G] [Finite G] [Fintype Block]
    {e : Block → k[G]} (blocks : BlockIdempotentDecomposition e)
    (b : Block) (P : Subgroup G) [P.Normal] (hP : IsPGroup p P) :
    HasNonzeroCentralBrauerRestriction blocks b P :=
  normal_p_central_idempotent_restriction_ne_zero P hP
    (blocks.blockIdempotentInCenter b) (blocks.primitive b).idempotent
    (blocks.primitive b).ne_zero

theorem navarro408PCoreDefectSource
    {p : ℕ} {k G LocalBlock : Type*}
    [Field k] [CharP k p] [IsAlgClosed k] [Group G] [Fintype G]
    [Fintype LocalBlock] [Fact p.Prime]
    (P : Subgroup G)
    {e : LocalBlock → k[defectNormalizer P]}
    (blocks : BlockIdempotentDecomposition e) :
    Navarro408PCoreDefectSource (p := p) P blocks := by
  refine ⟨?_⟩
  intro b D hD
  let _ : Fintype (defectNormalizer P) := Fintype.ofFinite _
  apply normal_subgroup_le_of_isSubconjugate
  exact (hD.support411.nonzero_iff_isSubconjugate
    (pCore p (defectNormalizer P)) (pCore_isPGroup p _)).mp
      (normal_pSubgroup_hasNonzeroCentralBrauerRestriction blocks b
        (pCore p (defectNormalizer P)) (pCore_isPGroup p _))

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPCoreDefectContainment


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
