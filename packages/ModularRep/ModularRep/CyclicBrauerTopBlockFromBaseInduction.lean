import ModularRep.NavarroBrauerRestrictionCovering
import ModularRep.Navarro414IntervalCentralCharacterAdapter

/-!
# The cyclic top-block choice from actual base induction

This is the covering-and-choice step in the cyclic proof of Späth (2013),
Lemma 6.1. The only block-induction premise is the initial relation in the
normal base group. Navarro (4.14) selects the top block internally; the
(9.2)/(9.5) covering interface and coefficient-restriction pasting show that
it covers the same base block. The cyclic twist interface is the composite
Navarro (8.20)+(8.7) route with the required modular cyclic, root-lift, and
tensor compatibility, and then selects a global extension in that top block.

No top-block label, selected covering equality, target induction relation, or
PositiveQTopChoice is an input. The local extension, base characters, and
all catalogues remain fixed; the returned global extension may be a quotient
linear twist of the initial one but restricts to the same base character.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.CyclicBrauerTopBlockFromBaseInduction

open ModularRep.FDRepSimpleClassKZero
open ModularRep.NavarroCoveringBrauerExtension
open ModularRep.NavarroBrauerRestrictionCovering
open Representation.Extension

universe u

noncomputable local instance subgroupFintypeForTopBlock
    {A : Type u} [Group A] [Finite A] (N : Subgroup A) : Fintype N :=
  Fintype.ofFinite N

/-- Construct a block-compatible global extension from the initial/base
induction relation and uniform standard sources, while retaining the local
extension literally. The intersection catalogue is transported along the
actual subgroup-intersection equivalence; no catalogue-equality premise is
accepted. -/
theorem exists_global_extension_with_induced_block
    {p : Nat} {k K A : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group A] [Fintype A] [Fact p.Prime]
    (S9295 : Navarro9295BrauerRestrictionCoveringPrinciple p k K)
    (S9495 : Navarro9495BrauerCoveringPrinciple p k K)
    (S820 : Navarro820CyclicBrauerTwistPrinciple p k K)
    (N : Subgroup A) [N.Normal] (H : Subgroup A)
    (iotaA : PrimeRegularRootEmbedding p k K A)
    (iotaN : PrimeRegularRootEmbedding p k K N)
    (iotaH : PrimeRegularRootEmbedding p k K H)
    (iotaM : PrimeRegularRootEmbedding p k K (N.comap H.subtype))
    (globalRootAgreement :
      ∀ zeta : rootsOfUnity (primeRegularExponent p N) k,
        iotaN.lift (((zeta : kˣ) : k)) =
          iotaA.lift (((zeta : kˣ) : k)))
    (localRootAgreement :
      ∀ zeta : rootsOfUnity
          (primeRegularExponent p (N.comap H.subtype)) k,
        iotaM.lift (((zeta : kˣ) : k)) =
          iotaH.lift (((zeta : kˣ) : k)))
    (fieldSource : SpathCoefficientField p k iotaA.prime)
    (hcyclic : IsCyclic (A ⧸ N))
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
    (Q : Subgroup A)
    (interval : CentralBrauerInterval (p := p) Q H)
    (S414 : Navarro414IntervalCentralCharacterSource
      interval localBlocks localCatalogue)
    (hbase : BlockInducesTo (H.comap N.subtype)
      (intersectionCatalogue.alongMulEquiv (subgroupIntersectionEquiv H N))
      baseCatalogue
      (irreducibleBrauerCharacterBlock iotaM hinjM intersectionBlocks theta)
      (irreducibleBrauerCharacterBlock iotaN hinjN baseBlocks phi)) :
    ∃ global : BrauerCharacterExtensionWitness iotaA iotaN phi,
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
    centralCharacterCovers_of_extension
      S9295 (N.comap H.subtype) iotaH iotaM localRootAgreement fieldSource
      localBlocks intersectionBlocks hinjH hinjM
      localCatalogue intersectionCatalogue theta fixedLocal
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
  obtain ⟨global, hglobalBlock⟩ := exists_extension_in_covering_block
    S9495 S820 N iotaA iotaN globalRootAgreement fieldSource hcyclic
    ambientBlocks baseBlocks hinjA hinjN ambientCatalogue baseCatalogue
    B phi initialGlobal hcover
  refine ⟨global, ?_⟩
  rw [hglobalBlock]
  exact ⟨hdefinedTop, htopCharacter⟩

end ModularRep.CyclicBrauerTopBlockFromBaseInduction



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
