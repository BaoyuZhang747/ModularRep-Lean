import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSupportedIrreducibleCovering
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSignedBrauerExtension
import ModularRep.Navarro414IntervalCentralCharacterAdapter

/-! Select the global top block at index two using the actual global model
and its sign twist. The local model supplies covering through its literal
restriction; the supported idempotent trace proves the required selection. -/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSignedBrauerTopBlockChoice

open ModularRep.FDRepSimpleClassKZero
open SporadicFi24P3Definition44NamedCarrierSignedBrauerExtension
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSupportedIrreducibleCovering
open Representation.Extension

universe u

noncomputable local instance subgroupFintypeForTopBlock
    {A : Type u} [Group A] [Finite A] (N : Subgroup A) : Fintype N :=
  Fintype.ofFinite N

/-- Construct a block-compatible global extension from the initial/base
induction relation and the quotient sign, while retaining the local
extension literally. The intersection catalogue is transported along the
actual subgroup-intersection equivalence; no catalogue-equality premise is
accepted. -/
theorem exists_global_twisted_extension_with_induced_block_of_index_two
    {p : Nat} {k K A : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group A] [Fintype A] [Fact p.Prime]
    (h2 : (2 : k) ≠ 0)
    (N : Subgroup A) [N.Normal] (H : Subgroup A)
    (iotaA : PrimeRegularRootEmbedding p k K A)
    (iotaN : PrimeRegularRootEmbedding p k K N)
    (iotaH : PrimeRegularRootEmbedding p k K H)
    (iotaM : PrimeRegularRootEmbedding p k K (N.comap H.subtype))
    (globalRootAgreement :
      ∀ zeta : rootsOfUnity (primeRegularExponent p N) k,
        iotaN.lift (((zeta : kˣ) : k)) =
          iotaA.lift (((zeta : kˣ) : k)))
    (hindex : N.index = 2)
    {AmbientBlock BaseBlock LocalBlock IntersectionBlock : Type u}
    [Fintype AmbientBlock] [Fintype BaseBlock]
    [Fintype LocalBlock] [Fintype IntersectionBlock]
    {ambientIdempotent : AmbientBlock → k[A]}
    {baseIdempotent : BaseBlock → k[N]}
    {localIdempotent : LocalBlock → k[H]}
    {intersectionIdempotent : IntersectionBlock → k[N.comap H.subtype]}
    (ambientBlocks : BlockIdempotentDecomposition ambientIdempotent)
    (baseBlocks : BlockIdempotentDecomposition baseIdempotent)
    (localBlocks : BlockIdempotentDecomposition localIdempotent)
    (intersectionBlocks : BlockIdempotentDecomposition intersectionIdempotent)
    (hinjA : IrreducibleBrauerCharacterInjectivity iotaA)
    (hinjN : IrreducibleBrauerCharacterInjectivity iotaN)
    (hinjH : IrreducibleBrauerCharacterInjectivity iotaH)
    (hinjM : IrreducibleBrauerCharacterInjectivity iotaM)
    (ambientCatalogue : BlockCentralCharacterCatalogue ambientBlocks)
    (baseCatalogue : BlockCentralCharacterCatalogue baseBlocks)
    (localCatalogue : BlockCentralCharacterCatalogue localBlocks)
    (intersectionCatalogue : BlockCentralCharacterCatalogue intersectionBlocks)
    (phi : IBr iotaN) (theta : IBr iotaM)
    (initialGlobal : BrauerCharacterExtensionWitness iotaA iotaN phi)
    (fixedLocal : BrauerCharacterExtensionWitness iotaH iotaM theta)
    {UG : Type u} [AddCommGroup UG] [Module k UG] [FiniteDimensional k UG]
    (sigmaG : Representation k A UG) (rhoG : Representation k N UG)
    [sigmaG.IsIrreducible] [rhoG.IsIrreducible]
    (hresG : sigmaG.pullback N.subtype = rhoG)
    (hInitial : initialGlobal.val.val = sigmaG.brauerCharacterOfRootEmbedding iotaA)
    (hBaseG : phi.val = rhoG.brauerCharacterOfRootEmbedding iotaN)
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (sigma : Representation k H V)
    (rho : Representation k (N.comap H.subtype) V)
    [sigma.IsIrreducible] [rho.IsIrreducible]
    (hres : sigma.pullback (N.comap H.subtype).subtype = rho)
    (hLocal : fixedLocal.val.val = sigma.brauerCharacterOfRootEmbedding iotaH)
    (hBase : theta.val = rho.brauerCharacterOfRootEmbedding iotaM)
    (Q : Subgroup A)
    (interval : CentralBrauerInterval (p := p) Q H)
    (S414 : Navarro414IntervalCentralCharacterSource
      interval localBlocks localCatalogue)
    (hbase : BlockInducesTo (H.comap N.subtype)
      (intersectionCatalogue.alongMulEquiv (subgroupIntersectionEquiv H N))
      baseCatalogue
      (irreducibleBrauerCharacterBlock iotaM hinjM intersectionBlocks theta)
      (irreducibleBrauerCharacterBlock iotaN hinjN baseBlocks phi)) :
    ∃ (global : BrauerCharacterExtensionWitness iotaA iotaN phi)
      (lambda : (A ⧸ N) →* Kˣ),
      (∀ x : PrimeRegularElement (G := A) p,
        global.val.val x = (lambda (QuotientGroup.mk' N x.val) : K) * initialGlobal.val.val x) ∧
      BlockInducesTo H localCatalogue ambientCatalogue
        (irreducibleBrauerCharacterBlock iotaH hinjH localBlocks fixedLocal.1)
        (irreducibleBrauerCharacterBlock iotaA hinjA ambientBlocks global.1) := by
  let bH := irreducibleBrauerCharacterBlock iotaH hinjH localBlocks fixedLocal.1
  let bM := irreducibleBrauerCharacterBlock iotaM hinjM intersectionBlocks theta
  let B := navarro414InducedBlock S414 ambientCatalogue bH
  have htop : BlockInducesTo H localCatalogue ambientCatalogue bH B :=
    navarro414InducedBlock_inducesTo S414 ambientCatalogue bH
  have hlocalCover : CentralCharacterCovers (N.comap H.subtype)
      (localCatalogue.centralCharacter bH)
      (intersectionCatalogue.centralCharacter bM) :=
    centralCharacterCovers_of_literal_restriction
      (N.comap H.subtype) iotaH iotaM
      localBlocks intersectionBlocks hinjH hinjM
      localCatalogue intersectionCatalogue fixedLocal.val theta
      sigma rho hres hLocal hBase
  obtain ⟨hdefinedTop, htopCharacter⟩ := htop
  obtain ⟨hdefinedBase, hbaseCharacter⟩ := hbase
  have hcover := inducedCentralCharacter_covers_of_local_cover
    H N (localCatalogue.centralCharacter bH)
    (intersectionCatalogue.centralCharacter bM)
    hlocalCover hdefinedTop hdefinedBase
  rw [htopCharacter] at hcover
  change CentralCharacterCovers N (ambientCatalogue.centralCharacter B)
    (inducedCentralCharacter (H.comap N.subtype)
      ((intersectionCatalogue.alongMulEquiv
        (subgroupIntersectionEquiv H N)).centralCharacter bM)
      hdefinedBase) at hcover
  rw [hbaseCharacter] at hcover
  obtain ⟨global, lambda, hglobalBlock, htwist⟩ := exists_twisted_extension_in_covering_block_of_index_two
    h2 N hindex iotaA iotaN globalRootAgreement
    ambientBlocks baseBlocks hinjA hinjN ambientCatalogue baseCatalogue
    B phi initialGlobal sigmaG rhoG hresG hInitial hBaseG hcover
  refine ⟨global, lambda, htwist, ?_⟩
  rw [hglobalBlock]
  exact ⟨hdefinedTop, htopCharacter⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSignedBrauerTopBlockChoice



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
