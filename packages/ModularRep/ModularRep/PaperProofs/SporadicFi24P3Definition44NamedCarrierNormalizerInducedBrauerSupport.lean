import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPKernelCentralAction
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralAlgebraScalar
import ModularRep.BlockInduction
import ModularRep.BlockCentralBrauerImage

/-! Nonzero Brauer support of an induced normalizer block. The restricted
central element is used through its scalar action on an actual simple
representation; no idempotence of coefficient restriction is required. -/

noncomputable section
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierNormalizerInducedBrauerSupport
open ModularRep ModularRep.FDRepSimpleClassKZero
open SporadicFi24P3Definition44NamedCarrierPKernelCentralAction
open SporadicFi24P3Definition44NamedCarrierCentralAlgebraScalar
attribute [local instance] Fintype.ofFinite

theorem centralBrauerRestriction_centerCoeffRestrict_eq_zero
    {k G : Type*} [CommSemiring k] [Group G]
    (Q H : Subgroup G) (hQH : Q ≤ H)
    (z : GroupAlgebraCenter k G)
    (hz : centralBrauerRestriction Q z = 0) :
    centralBrauerRestriction (Q.subgroupOf H) (centerCoeffRestrict H z) = 0 := by
  apply Subtype.ext
  ext c
  let cG : centralizerOf Q := ⟨((c : H) : G), by
    apply Subgroup.mem_centralizer_iff.mpr
    intro q hq
    let qH : H := ⟨q, hQH hq⟩
    have hqH : qH ∈ Q.subgroupOf H := hq
    exact congrArg (fun x : H => (x : G))
      (Subgroup.mem_centralizer_iff.mp c.property qH hqH)⟩
  change (z : k[G]).coeff (cG : G) = 0
  change ((centralBrauerRestriction Q z :
    GroupAlgebraCenter k (centralizerOf Q)) : k[centralizerOf Q]).coeff cG = 0
  rw [hz]
  rfl

universe u v
theorem normalizer_induced_block_has_nonzero_brauer_support
    {p : ℕ} {k G : Type u} {K : Type v} {I J : Type*}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group G] [Fintype G] [Fact p.Prime] [Fintype I] [Fintype J]
    (Q : Subgroup G) (hQ : IsPGroup p Q)
    (iota : PrimeRegularRootEmbedding p k K (defectNormalizer Q))
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    {localIdempotent : I → k[defectNormalizer Q]}
    {ambientIdempotent : J → k[G]}
    (localBlocks : BlockIdempotentDecomposition localIdempotent)
    (ambientBlocks : BlockIdempotentDecomposition ambientIdempotent)
    (localCatalogue : BlockCentralCharacterCatalogue localBlocks)
    (ambientCatalogue : BlockCentralCharacterCatalogue ambientBlocks)
    (phi : IBr iota) (B : J)
    (hInd : BlockInducesTo (defectNormalizer Q) localCatalogue ambientCatalogue
      (irreducibleBrauerCharacterBlock iota hinj localBlocks phi) B) :
    HasNonzeroCentralBrauerRestriction ambientBlocks B Q := by
  let N := defectNormalizer Q
  let P : Subgroup N := Q.subgroupOf N
  let e := ambientBlocks.blockIdempotentInCenter B
  let z := centerCoeffRestrict N e
  have hscalar : localCatalogue.centralCharacter
      (irreducibleBrauerCharacterBlock iota hinj localBlocks phi) z = 1 := by
    obtain ⟨hdefined, heq⟩ := hInd
    have h := congrArg (fun f : GroupAlgebraCenter k G →ₐ[k] k => f e) heq
    exact h.trans (ambientCatalogue.centralCharacter_own B)
  obtain ⟨V, hV, hchar⟩ := phi.property
  let _ : Representation.IsIrreducible V.ρ := hV
  let _ : Nontrivial V :=
    IsSimpleModule.nontrivial k[N] (Representation.asModule V.ρ)
  have haction : Representation.asAlgebraHom V.ρ z.val = (LinearMap.id : V →ₗ[k] V) := by
    rw [catalogue_action_of_affording iota hinj localBlocks localCatalogue phi V.ρ hchar z,
      hscalar, one_smul]
  intro hz
  have hzlocal : centralBrauerRestriction P z = 0 :=
    centralBrauerRestriction_centerCoeffRestrict_eq_zero Q N Q.le_normalizer e hz
  have hzero := central_action_eq_zero_of_normal_p P hQ.comap_subtype V.ρ hV z hzlocal
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have h := congrArg (fun f : V →ₗ[k] V => f v) (haction.symm.trans hzero)
  exact hv h

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierNormalizerInducedBrauerSupport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
