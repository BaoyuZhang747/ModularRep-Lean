import ModularRep.IBrBlockEquivTransport
import ModularRep.CentralCharacterCovering
import ModularRep.NavarroBrauerRestrictionCovering
import ModularRep.Navarro414IntervalCentralCharacterAdapter
import ModularRep.SubgroupIntervalTwo

/-! Block compatibility for two fixed extensions over a p-group quotient.
The only induction input is the relation between their base characters. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBQ3PrincipalPairBlockChoice

open ModularRep ModularRep.FDRepSimpleClassKZero
open ModularRep.NavarroBrauerRestrictionCovering
open ModularRep.NavarroCoveringBrauerExtension
open Representation.Extension

universe u

local instance subgroupFintype {A : Type u} [Group A] [Finite A] (H : Subgroup A) :
    Fintype H := Fintype.ofFinite H

/-- The uniqueness direction of Navarro (9.6), expressed through (9.5).
Both labels and central characters belong to the displayed block decompositions. -/
def Navarro96PGroupCoveringUniquenessPrinciple
    (p : Nat) (k : Type u) [Field k] [CharP k p] [IsAlgClosed k] : Prop :=
  ∀ {A : Type u} [Group A] [Fintype A] [Fact p.Prime]
    (N : Subgroup A) [N.Normal],
    IsPGroup p (A ⧸ N) →
    ∀ {AmbientBlock BaseBlock : Type u}
      [Fintype AmbientBlock] [Fintype BaseBlock]
      {ambientIdempotent : AmbientBlock → k[A]}
      {baseIdempotent : BaseBlock → k[N]}
      (ambientBlocks : BlockIdempotentDecomposition ambientIdempotent)
      (baseBlocks : BlockIdempotentDecomposition baseIdempotent)
      (ambientCatalogue : BlockCentralCharacterCatalogue ambientBlocks)
      (baseCatalogue : BlockCentralCharacterCatalogue baseBlocks)
      (B₁ B₂ : AmbientBlock) (b : BaseBlock),
      CentralCharacterCovers N
        (ambientCatalogue.centralCharacter B₁) (baseCatalogue.centralCharacter b) →
      CentralCharacterCovers N
        (ambientCatalogue.centralCharacter B₂) (baseCatalogue.centralCharacter b) →
      B₁ = B₂

def localIntersection {A : Type u} [Group A] (D J : Subgroup A) : Subgroup J :=
  D.comap J.subtype

def localInclusion {A : Type u} [Group A] (D J : Subgroup A) :
    localIntersection D J →* D where
  toFun x := ⟨x.1.1, x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

structure IntermediateBlockData (p : Nat) (k K : Type u)
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K] [Fact p.Prime]
    {A : Type u} [Group A] [Fintype A]
    (D : Subgroup A)
    (globalCharacter : PrimeRegularClassFunction K A p)
    (localCharacter : PrimeRegularClassFunction K D p)
    (J : Subgroup A) where
  globalRoot : PrimeRegularRootEmbedding p k K J
  globalBrauer : IBr globalRoot
  globalRestriction : PrimeRegularClassFunction.pullback J.subtype globalCharacter = globalBrauer.1
  localRoot : PrimeRegularRootEmbedding p k K (localIntersection D J)
  localBrauer : IBr localRoot
  localRestriction : PrimeRegularClassFunction.pullback (localInclusion D J) localCharacter = localBrauer.1
  GlobalBlock : Type u
  LocalBlock : Type u
  [fintypeGlobalBlock : Fintype GlobalBlock]
  [fintypeLocalBlock : Fintype LocalBlock]
  globalBlockIdempotent : GlobalBlock → k[J]
  localBlockIdempotent : LocalBlock → k[localIntersection D J]
  globalBlocks : BlockIdempotentDecomposition globalBlockIdempotent
  localBlocks : BlockIdempotentDecomposition localBlockIdempotent
  globalBrauerInjective : IrreducibleBrauerCharacterInjectivity globalRoot
  localBrauerInjective : IrreducibleBrauerCharacterInjectivity localRoot
  globalCentralCharacters : BlockCentralCharacterCatalogue globalBlocks
  localCentralCharacters : BlockCentralCharacterCatalogue localBlocks
  globalCentralCharactersNavarro311 : Navarro311CatalogueProvenance p (Fact.out : p.Prime)
    globalBlocks globalCentralCharacters
  localCentralCharactersNavarro311 : Navarro311CatalogueProvenance p (Fact.out : p.Prime)
    localBlocks localCentralCharacters
  inductionEquality : BlockInducesTo (localIntersection D J)
    localCentralCharacters globalCentralCharacters
    (irreducibleBrauerCharacterBlock localRoot localBrauerInjective localBlocks localBrauer)
    (irreducibleBrauerCharacterBlock globalRoot globalBrauerInjective globalBlocks globalBrauer)

attribute [instance] IntermediateBlockData.fintypeGlobalBlock
  IntermediateBlockData.fintypeLocalBlock

variable {p : Nat} {k K : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K] [Fact p.Prime]

theorem baseSquare_of_localEmbedding
    {G A : Type u} [Group G] [Group A]
    (N : Subgroup G) (base D : Subgroup A)
    (eG : G ≃* base) (eM : N ≃* base.comap D.subtype)
    (hM : ∀ n : N, (eM n).1.1 = (eG n.1 : A)) :
    eG.toMonoidHom.comp N.subtype =
      (localIntersection D base).subtype.comp
        (eM.trans (subgroupIntersectionEquiv D base)).toMonoidHom := by
  apply MonoidHom.ext
  intro n
  apply Subtype.ext
  exact (hM n).symm

def baseBlockDataOfExtensions
    {G A : Type u} [Group G] [Fintype G] [Group A] [Fintype A]
    (N : Subgroup G) (base D : Subgroup A)
    (eG : G ≃* base) (eM : N ≃* base.comap D.subtype)
    (square : eG.toMonoidHom.comp N.subtype =
      (localIntersection D base).subtype.comp
        (eM.trans (subgroupIntersectionEquiv D base)).toMonoidHom)
    (rG : PrimeRegularRootEmbedding p k K G)
    (rN : PrimeRegularRootEmbedding p k K N)
    (rA : PrimeRegularRootEmbedding p k K A)
    (rD : PrimeRegularRootEmbedding p k K D)
    (injG : IrreducibleBrauerCharacterInjectivity rG)
    (injN : IrreducibleBrauerCharacterInjectivity rN)
    {BG BN : Type u} [Fintype BG] [Fintype BN]
    {bG : BG → k[G]} {bN : BN → k[N]}
    (DG : BlockIdempotentDecomposition bG) (DN : BlockIdempotentDecomposition bN)
    (CG : BlockCentralCharacterCatalogue DG) (CN : BlockCentralCharacterCatalogue DN)
    (phiG : IBr rG) (phiN : IBr rN)
    (globalExt : BrauerCharacterExtensionWitness rA (rG.alongMulEquiv eG)
      (IrreducibleBrauerCharacter.alongMulEquiv rG eG phiG))
    (localExt : BrauerCharacterExtensionWitness rD (rN.alongMulEquiv eM)
      (IrreducibleBrauerCharacter.alongMulEquiv rN eM phiN))
    (fieldSource : SpathCoefficientField p k (Fact.out : p.Prime))
    (hInd : BlockInducesTo N CN CG
      (irreducibleBrauerCharacterBlock rN injN DN phiN)
      (irreducibleBrauerCharacterBlock rG injG DG phiG)) :
    IntermediateBlockData p k K D globalExt.1.1 localExt.1.1 base := by
  let d := subgroupIntersectionEquiv D base
  let eN : N ≃* localIntersection D base := eM.trans d
  refine {
    globalRoot := rG.alongMulEquiv eG
    globalBrauer := IrreducibleBrauerCharacter.alongMulEquiv rG eG phiG
    globalRestriction := globalExt.2
    localRoot := rN.alongMulEquiv eN
    localBrauer := IrreducibleBrauerCharacter.alongMulEquiv rN eN phiN
    localRestriction := ?_
    GlobalBlock := BG
    LocalBlock := BN
    globalBlockIdempotent := fun b => MonoidAlgebra.domCongr k k eG (bG b)
    localBlockIdempotent := fun b => MonoidAlgebra.domCongr k k eN (bN b)
    globalBlocks := DG.alongMulEquiv eG
    localBlocks := DN.alongMulEquiv eN
    globalBrauerInjective := irreducibleBrauerCharacterInjectivity_of_rootEmbedding _
    localBrauerInjective := irreducibleBrauerCharacterInjectivity_of_rootEmbedding _
    globalCentralCharacters := CG.alongMulEquiv eG
    localCentralCharacters := CN.alongMulEquiv eN
    globalCentralCharactersNavarro311 := ⟨fieldSource⟩
    localCentralCharactersNavarro311 := ⟨fieldSource⟩
    inductionEquality := ?_ }
  · apply PrimeRegularClassFunction.ext
    intro x
    exact congrArg
      (fun chi : PrimeRegularClassFunction K (base.comap D.subtype) p =>
        chi (PrimeRegularElement.map d.symm.toMonoidHom x)) localExt.2
  · rw [irreducibleBrauerCharacterBlock_alongMulEquiv rN injN eN
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) DN phiN,
      irreducibleBrauerCharacterBlock_alongMulEquiv rG injG eG
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) DG phiG]
    exact blockInducesTo_alongMulEquiv N (localIntersection D base) eG eN square
      CN CG (CN.alongMulEquiv eN) (CG.alongMulEquiv eG) rfl rfl hInd


def localTopEquiv {G : Type u} [Group G] (N : Subgroup G) :
    N ≃* localIntersection N (⊤ : Subgroup G) where
  toFun n := ⟨⟨n.1, Subgroup.mem_top _⟩, n.2⟩
  invFun n := ⟨n.1.1, n.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

def topBlockData
    {A : Type u} [Group A] [Fintype A] (N : Subgroup A)
    (rG : PrimeRegularRootEmbedding p k K A)
    (rN : PrimeRegularRootEmbedding p k K N)
    (injG : IrreducibleBrauerCharacterInjectivity rG)
    (injN : IrreducibleBrauerCharacterInjectivity rN)
    {BG BN : Type u} [Fintype BG] [Fintype BN]
    {bG : BG → k[A]} {bN : BN → k[N]}
    (DG : BlockIdempotentDecomposition bG) (DN : BlockIdempotentDecomposition bN)
    (CG : BlockCentralCharacterCatalogue DG) (CN : BlockCentralCharacterCatalogue DN)
    (phiG : IBr rG) (phiN : IBr rN)
    (fieldSource : SpathCoefficientField p k (Fact.out : p.Prime))
    (hInd : BlockInducesTo N CN CG
      (irreducibleBrauerCharacterBlock rN injN DN phiN)
      (irreducibleBrauerCharacterBlock rG injG DG phiG)) :
    IntermediateBlockData p k K N phiG.1 phiN.1 (⊤ : Subgroup A) := by
  let eG : A ≃* (⊤ : Subgroup A) := Subgroup.topEquiv.symm
  let eN := localTopEquiv N
  have hsquare : eG.toMonoidHom.comp N.subtype =
      (localIntersection N (⊤ : Subgroup A)).subtype.comp eN.toMonoidHom := by
    ext n
    rfl
  refine {
    globalRoot := rG.alongMulEquiv eG
    globalBrauer := IrreducibleBrauerCharacter.alongMulEquiv rG eG phiG
    globalRestriction := ?_
    localRoot := rN.alongMulEquiv eN
    localBrauer := IrreducibleBrauerCharacter.alongMulEquiv rN eN phiN
    localRestriction := ?_
    GlobalBlock := BG
    LocalBlock := BN
    globalBlockIdempotent := fun b => MonoidAlgebra.domCongr k k eG (bG b)
    localBlockIdempotent := fun b => MonoidAlgebra.domCongr k k eN (bN b)
    globalBlocks := DG.alongMulEquiv eG
    localBlocks := DN.alongMulEquiv eN
    globalBrauerInjective := irreducibleBrauerCharacterInjectivity_of_rootEmbedding _
    localBrauerInjective := irreducibleBrauerCharacterInjectivity_of_rootEmbedding _
    globalCentralCharacters := CG.alongMulEquiv eG
    localCentralCharacters := CN.alongMulEquiv eN
    globalCentralCharactersNavarro311 := ⟨fieldSource⟩
    localCentralCharactersNavarro311 := ⟨fieldSource⟩
    inductionEquality := ?_ }
  · apply PrimeRegularClassFunction.ext
    intro x
    rfl
  · apply PrimeRegularClassFunction.ext
    intro x
    rfl
  · rw [irreducibleBrauerCharacterBlock_alongMulEquiv rN injN eN
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) DN phiN,
      irreducibleBrauerCharacterBlock_alongMulEquiv rG injG eG
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) DG phiG]
    exact blockInducesTo_alongMulEquiv N (localIntersection N (⊤ : Subgroup A))
      eG eN hsquare CN CG (CN.alongMulEquiv eN) (CG.alongMulEquiv eG) rfl rfl hInd


theorem blockInducesTo_of_pGroupQuotient
    {p : Nat} {k K A : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group A] [Fintype A] [Fact p.Prime]
    (S9295 : Navarro9295BrauerRestrictionCoveringPrinciple p k K)
    (S96 : Navarro96PGroupCoveringUniquenessPrinciple p k)
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
    (hPGroup : IsPGroup p (A ⧸ N))
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
    BlockInducesTo H localCatalogue ambientCatalogue
      (irreducibleBrauerCharacterBlock iotaH hinjH localBlocks fixedLocal.1)
      (irreducibleBrauerCharacterBlock iotaA hinjA ambientBlocks initialGlobal.1) := by
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
  have hglobalCover := centralCharacterCovers_of_extension
    S9295 N iotaA iotaN globalRootAgreement fieldSource
    ambientBlocks baseBlocks hinjA hinjN ambientCatalogue baseCatalogue phi initialGlobal
  have hglobalBlock := S96 N hPGroup ambientBlocks baseBlocks
    ambientCatalogue baseCatalogue B
    (irreducibleBrauerCharacterBlock iotaA hinjA ambientBlocks initialGlobal.1)
    (irreducibleBrauerCharacterBlock iotaN hinjN baseBlocks phi) hcover hglobalCover
  rw [← hglobalBlock]
  exact ⟨hdefinedTop, htopCharacter⟩


private theorem domCongr_roundtrip
    {k G H : Type u} [Field k] [Group G] [Group H]
    (e : G ≃* H) (f : k[H]) :
    MonoidAlgebra.domCongr k k e (MonoidAlgebra.domCongr k k e.symm f) = f := by
  ext x
  simp only [MonoidAlgebra.coeff_domCongr, MulEquiv.symm_symm, MulEquiv.apply_symm_apply]

def allIntermediateBlockData
    {G A : Type u}
    [Group G] [Fintype G] [Group A] [Fintype A]
    (N : Subgroup G) (B D : Subgroup A) [B.Normal]
    (eG : G ≃* B) (eM : N ≃* B.comap D.subtype)
    (square : eG.toMonoidHom.comp N.subtype =
      (localIntersection D B).subtype.comp
        (eM.trans (subgroupIntersectionEquiv D B)).toMonoidHom)
    (rG : PrimeRegularRootEmbedding p k K G)
    (rN : PrimeRegularRootEmbedding p k K N)
    (rA : PrimeRegularRootEmbedding p k K A)
    (rD : PrimeRegularRootEmbedding p k K D)
    (injG : IrreducibleBrauerCharacterInjectivity rG)
    (injN : IrreducibleBrauerCharacterInjectivity rN)
    {BG BN BA BD : Type u}
    [Fintype BG] [Fintype BN] [Fintype BA] [Fintype BD]
    {bG : BG → k[G]} {bN : BN → k[N]}
    {bA : BA → k[A]} {bD : BD → k[D]}
    (DG : BlockIdempotentDecomposition bG) (DN : BlockIdempotentDecomposition bN)
    (DA : BlockIdempotentDecomposition bA) (DD : BlockIdempotentDecomposition bD)
    (CG : BlockCentralCharacterCatalogue DG) (CN : BlockCentralCharacterCatalogue DN)
    (CA : BlockCentralCharacterCatalogue DA) (CD : BlockCentralCharacterCatalogue DD)
    (phiG : IBr rG) (phiN : IBr rN)
    (initialGlobal : BrauerCharacterExtensionWitness rA (rG.alongMulEquiv eG)
      (IrreducibleBrauerCharacter.alongMulEquiv rG eG phiG))
    (fixedLocal : BrauerCharacterExtensionWitness rD (rN.alongMulEquiv eM)
      (IrreducibleBrauerCharacter.alongMulEquiv rN eM phiN))
    (globalAgreement : ∀ zeta : rootsOfUnity (primeRegularExponent p B) k,
      (rG.alongMulEquiv eG).lift (((zeta : kˣ) : k)) = rA.lift (((zeta : kˣ) : k)))
    (localAgreement : ∀ zeta : rootsOfUnity (primeRegularExponent p (B.comap D.subtype)) k,
      (rN.alongMulEquiv eM).lift (((zeta : kˣ) : k)) = rD.lift (((zeta : kˣ) : k)))
    (fieldSource : SpathCoefficientField p k (Fact.out : p.Prime))
    (hPGroup : IsPGroup p (A ⧸ B))
    (hcard : Nat.card (A ⧸ B) ≤ 2)
    (Q : Subgroup A) (interval : CentralBrauerInterval (p := p) Q D)
    (S414 : Navarro414IntervalCentralCharacterSource interval DD CD)
    (S9295 : Navarro9295BrauerRestrictionCoveringPrinciple p k K)
    (S96 : Navarro96PGroupCoveringUniquenessPrinciple p k)
    (hInd : BlockInducesTo N CN CG
      (irreducibleBrauerCharacterBlock rN injN DN phiN)
      (irreducibleBrauerCharacterBlock rG injG DG phiG)) :
    ∀ J : Subgroup A, B ≤ J →
      IntermediateBlockData p k K D initialGlobal.1.1 fixedLocal.1.1 J := by
  let rB := rG.alongMulEquiv eG
  let phiB := IrreducibleBrauerCharacter.alongMulEquiv rG eG phiG
  let rM := rN.alongMulEquiv eM
  let phiM := IrreducibleBrauerCharacter.alongMulEquiv rN eM phiN
  let initialBase := baseBlockDataOfExtensions
    N B D eG eM square rG rN rA rD injG injN
    DG DN CG CN phiG phiN initialGlobal fixedLocal fieldSource hInd
  let d := subgroupIntersectionEquiv D B
  let intersectionBlocks := initialBase.localBlocks.alongMulEquiv d.symm
  let intersectionCatalogue := initialBase.localCentralCharacters.alongMulEquiv d.symm
  let injM := irreducibleBrauerCharacterInjectivity_of_rootEmbedding rM
  have hblock : irreducibleBrauerCharacterBlock rM injM intersectionBlocks phiM =
      irreducibleBrauerCharacterBlock initialBase.localRoot initialBase.localBrauerInjective
        initialBase.localBlocks initialBase.localBrauer := by
    apply irreducibleBrauerCharacterBlock_alongMulEquiv_of_lift_eq
      initialBase.localRoot initialBase.localBrauerInjective rM injM d.symm
      initialBase.localBlocks initialBase.localBrauer phiM
    · funext z
      change (rN.alongMulEquiv eM).lift z = (rN.alongMulEquiv (eM.trans d)).lift z
      simp only [PrimeRegularRootEmbedding.alongMulEquiv_lift]
    · apply PrimeRegularClassFunction.ext
      intro x
      rfl
  have hcatalogue (b : initialBase.LocalBlock) :
      (intersectionCatalogue.alongMulEquiv d).centralCharacter b =
        initialBase.localCentralCharacters.centralCharacter b := by
    apply centralCharacterAlongMulEquiv_eq_of_blockIdempotent
      d intersectionCatalogue initialBase.localCentralCharacters
    apply Subtype.ext
    exact domCongr_roundtrip d (show k[D.comap B.subtype] from initialBase.localBlockIdempotent b)
  have hbase : BlockInducesTo (D.comap B.subtype)
      (intersectionCatalogue.alongMulEquiv d) initialBase.globalCentralCharacters
      (irreducibleBrauerCharacterBlock rM injM intersectionBlocks phiM)
      (irreducibleBrauerCharacterBlock rB initialBase.globalBrauerInjective
        initialBase.globalBlocks phiB) := by
    unfold BlockInducesTo
    rw [hblock, hcatalogue]
    exact initialBase.inductionEquality
  have htop := blockInducesTo_of_pGroupQuotient
    S9295 S96 B D rA rB rD rM globalAgreement localAgreement fieldSource hPGroup
    DA initialBase.globalBlocks DD intersectionBlocks
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) initialBase.globalBrauerInjective
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) injM
    CA initialBase.globalCentralCharacters CD intersectionCatalogue
    phiB phiM initialGlobal fixedLocal Q interval S414 hbase
  let atTop := topBlockData D rA rD
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _)
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _)
    DA DD CA CD initialGlobal.1 fixedLocal.1 fieldSource htop
  classical
  intro J hJ
  by_cases hbaseJ : J = B
  · subst J
    exact initialBase
  · have htopJ :=
      (subgroup_eq_base_or_top_of_quotient_card_le_two B hcard J hJ).resolve_left hbaseJ
    subst J
    exact atTop


end ModularRep.PaperProofs.TypeBQ3PrincipalPairBlockChoice


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
