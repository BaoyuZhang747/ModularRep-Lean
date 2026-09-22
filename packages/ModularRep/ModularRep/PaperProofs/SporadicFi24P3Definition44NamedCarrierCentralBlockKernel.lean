import ModularRep.CentralCharacterBlockInductionRestriction

/-! A central kernel passes from an ambient irreducible representation to a
local one through their actual block induction relation. The only central
sector used is the trivial sector on the given kernel subgroup. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralBlockKernel

open ModularRep

theorem centralCharacter_eq_one_of_le_ker
    {k G V : Type*} [Field k] [IsAlgClosed k] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (Z : Subgroup G) (hZ : Z ≤ Subgroup.center G)
    (rho : Representation k G V) [rho.IsIrreducible]
    (hkernel : Z ≤ rho.ker) :
    rho.centralCharacter Z hZ = 1 := by
  have hone : ∀ z : Z,
      rho (z : G) = (((1 : Z →* kˣ) z : k)) • LinearMap.id := by
    intro z
    have hz : rho (z : G) = 1 := hkernel z.property
    rw [hz]
    simp [Module.End.one_eq_id]
  exact ((Representation.existsUnique_centralCharacter rho Z hZ).unique
    hone (Representation.centralCharacter_spec rho Z hZ)).symm

theorem le_ker_of_centralCharacter_eq_one
    {k G V : Type*} [Field k] [IsAlgClosed k] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (Z : Subgroup G) (hZ : Z ≤ Subgroup.center G)
    (rho : Representation k G V) [rho.IsIrreducible]
    (hcentral : rho.centralCharacter Z hZ = 1) :
    Z ≤ rho.ker := by
  intro z hz
  change rho z = LinearMap.id
  have hspec := Representation.centralCharacter_spec rho Z hZ ⟨z, hz⟩
  rw [hcentral] at hspec
  simpa [Module.End.one_eq_id] using hspec

section BlockInduction

variable {k G LocalBlock AmbientBlock VN VG : Type*}
variable [Field k] [IsAlgClosed k] [Group G] [Fintype G]
variable [Fintype LocalBlock] [Fintype AmbientBlock]
variable [AddCommGroup VN] [Module k VN] [FiniteDimensional k VN]
variable [AddCommGroup VG] [Module k VG] [FiniteDimensional k VG]
variable (H Z : Subgroup G)

local instance subgroupFintype : Fintype H := Fintype.ofFinite H

variable {localIdempotent : LocalBlock → k[H]}
variable {ambientIdempotent : AmbientBlock → k[G]}
variable {localBlocks : BlockIdempotentDecomposition localIdempotent}
variable {ambientBlocks : BlockIdempotentDecomposition ambientIdempotent}

theorem local_central_kernel_of_blockInducesTo
    [Fintype Z] [Invertible (Fintype.card Z : k)]
    (hZH : Z ≤ H) (hZ : Z ≤ Subgroup.center G)
    (localCatalogue : BlockCentralCharacterCatalogue localBlocks)
    (ambientCatalogue : BlockCentralCharacterCatalogue ambientBlocks)
    {b : LocalBlock} {B : AmbientBlock}
    (hinduces : BlockInducesTo H localCatalogue ambientCatalogue b B)
    (rhoN : Representation k H VN) [rhoN.IsIrreducible]
    (rhoG : Representation k G VG) [rhoG.IsIrreducible]
    (hbV : ∀ v : rhoN.asModule, localIdempotent b • v = v)
    (hBV : ∀ v : rhoG.asModule, ambientIdempotent B • v = v)
    (hkernel : Z ≤ rhoG.ker) :
    Z.subgroupOf H ≤ rhoN.ker := by
  apply le_ker_of_centralCharacter_eq_one (Z.subgroupOf H)
    (subgroupOf_le_center H Z hZ) rhoN
  rw [Representation.centralCharacter_eq_comp_of_blockInducesTo
    H Z hZH hZ localCatalogue ambientCatalogue hinduces rhoN rhoG hbV hBV,
    centralCharacter_eq_one_of_le_ker Z hZ rhoG hkernel]
  ext z
  rfl

end BlockInduction

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralBlockKernel



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
