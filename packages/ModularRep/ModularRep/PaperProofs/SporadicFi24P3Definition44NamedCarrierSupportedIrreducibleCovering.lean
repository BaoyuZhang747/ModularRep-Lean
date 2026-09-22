import ModularRep.CentralCharacterCovering
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralAlgebraScalar
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage

/-! Supported central elements have the same action on a representation
and its literal restriction. For irreducible representations, the retained
catalogues and their actual affording equations therefore give covering.
No normality, cyclicity or character-theoretic covering source is required. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSupportedIrreducibleCovering

open ModularRep ModularRep.FDRepSimpleClassKZero
open SporadicFi24P3Definition44NamedCarrierCentralAlgebraScalar
open SporadicFi24P3Definition44NamedCarrierQuotientBlockAlgebra
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage

universe u

theorem algebraMapOf_coeffRestrict_of_supported
    {k G : Type u} [Field k] [Group G]
    (N : Subgroup G) (z : GroupAlgebraCenter k G)
    (hz : CentralElementSupportedOn N z) :
    algebraMapOf N.subtype (coeffRestrict N (z : k[G])) = (z : k[G]) := by
  classical
  have hr : coeffRestrict N (z : k[G]) =
      MonoidAlgebra.comapDomain N.subtype Subtype.val_injective (z : k[G]) := by
    ext n
    rfl
  have hs : ↑(z : k[G]).coeff.support ⊆ Set.range N.subtype := by
    intro g hg
    have hgN : g ∈ N := by
      by_contra hn
      exact (Finsupp.mem_support_iff.mp hg) (hz g hn)
    exact ⟨⟨g, hgN⟩, rfl⟩
  change MonoidAlgebra.mapDomain N.subtype (coeffRestrict N (z : k[G])) = (z : k[G])
  rw [hr]
  exact MonoidAlgebra.mapDomain_comapDomain hs Subtype.val_injective

theorem supported_pullback_action
    {k G V : Type u} [Field k] [Group G]
    [AddCommGroup V] [Module k V]
    (N : Subgroup G) (sigma : Representation k G V)
    (z : GroupAlgebraCenter k G) (hz : CentralElementSupportedOn N z) :
    (sigma.pullback N.subtype).asAlgebraHom (centerCoeffRestrict N z).val =
      sigma.asAlgebraHom z.val := by
  change (sigma.pullback N.subtype).asAlgebraHom
    (coeffRestrict N (z : k[G])) = sigma.asAlgebraHom (z : k[G])
  rw [algebra_action_map, algebraMapOf_coeffRestrict_of_supported N z hz]

local instance subgroupFintype {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) : Fintype N := Fintype.ofFinite _

theorem centralCharacterCovers_of_literal_restriction
    {p : ℕ} {k K G V I J : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group G] [Fintype G] [Fintype I] [Fintype J]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (N : Subgroup G)
    (iotaG : PrimeRegularRootEmbedding p k K G)
    (iotaN : PrimeRegularRootEmbedding p k K N)
    {eG : I → k[G]} {eN : J → k[N]}
    (blocksG : BlockIdempotentDecomposition eG)
    (blocksN : BlockIdempotentDecomposition eN)
    (injG : IrreducibleBrauerCharacterInjectivity iotaG)
    (injN : IrreducibleBrauerCharacterInjectivity iotaN)
    (catalogueG : BlockCentralCharacterCatalogue blocksG)
    (catalogueN : BlockCentralCharacterCatalogue blocksN)
    (Phi : IBr iotaG) (phi : IBr iotaN)
    (sigma : Representation k G V) (rho : Representation k N V)
    [sigma.IsIrreducible] [rho.IsIrreducible]
    (hres : sigma.pullback N.subtype = rho)
    (hPhi : Phi.val = sigma.brauerCharacterOfRootEmbedding iotaG)
    (hphi : phi.val = rho.brauerCharacterOfRootEmbedding iotaN) :
    CentralCharacterCovers N
      (catalogueG.centralCharacter
        (irreducibleBrauerCharacterBlock iotaG injG blocksG Phi))
      (catalogueN.centralCharacter
        (irreducibleBrauerCharacterBlock iotaN injN blocksN phi)) := by
  intro z hz
  apply scalar_id_injective sigma
  have hact : rho.asAlgebraHom (centerCoeffRestrict N z).val =
      sigma.asAlgebraHom z.val := by
    rw [← hres]
    exact supported_pullback_action N sigma z hz
  exact (catalogue_action_of_affording iotaG injG blocksG catalogueG Phi sigma hPhi z).symm.trans
    (hact.symm.trans (catalogue_action_of_affording
      iotaN injN blocksN catalogueN phi rho hphi (centerCoeffRestrict N z)))

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSupportedIrreducibleCovering


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
