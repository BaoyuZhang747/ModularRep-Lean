import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPacketValues
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierInnerRebase
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierNormalizedPairs

/-!
# A literal extension packet at an arbitrary raw weight representative

The local group is identified with the normalizer of the actual input
radical. The ordinary character in its restriction equation belongs to
that same input raw weight. Intermediate blocks retain the actual global
and local extension characters. All fields are concrete mathematical data.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualRadicalPacket

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeTransport
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPacketValues
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierInnerRebase
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQOneWitness

universe u

local instance subgroupFintype {A : Type u} [Group A] [Finite A] (H : Subgroup A) :
    Fintype H := Fintype.ofFinite H

def localIntersection {A : Type u} [Group A] (D J : Subgroup A) : Subgroup J :=
  D.comap J.subtype

def localInclusion {A : Type u} [Group A] (D J : Subgroup A) :
    localIntersection D J →* D where
  toFun x := ⟨x.1.1, x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

structure ActualIntermediateBlockData (P : Definition35Problem.{u})
    {A : Type u} [Group A] [Fintype A]
    (D : Subgroup A)
    (globalCharacter : PrimeRegularClassFunction P.K A P.p)
    (localCharacter : PrimeRegularClassFunction P.K D P.p)
    (J : Subgroup A) where
  globalRoot : PrimeRegularRootEmbedding P.p P.k P.K J
  globalBrauer : IBr globalRoot
  globalRestriction : PrimeRegularClassFunction.pullback J.subtype globalCharacter = globalBrauer.1
  localRoot : PrimeRegularRootEmbedding P.p P.k P.K (localIntersection D J)
  localBrauer : IBr localRoot
  localRestriction : PrimeRegularClassFunction.pullback (localInclusion D J) localCharacter = localBrauer.1
  GlobalBlock : Type u
  LocalBlock : Type u
  [fintypeGlobalBlock : Fintype GlobalBlock]
  [fintypeLocalBlock : Fintype LocalBlock]
  globalBlockIdempotent : GlobalBlock → P.k[J]
  localBlockIdempotent : LocalBlock → P.k[localIntersection D J]
  globalBlocks : BlockIdempotentDecomposition globalBlockIdempotent
  localBlocks : BlockIdempotentDecomposition localBlockIdempotent
  globalBrauerInjective : IrreducibleBrauerCharacterInjectivity globalRoot
  localBrauerInjective : IrreducibleBrauerCharacterInjectivity localRoot
  globalCentralCharacters : BlockCentralCharacterCatalogue globalBlocks
  localCentralCharacters : BlockCentralCharacterCatalogue localBlocks
  globalCentralCharactersNavarro311 : Navarro311CatalogueProvenance P.p P.iota.prime
    globalBlocks globalCentralCharacters
  localCentralCharactersNavarro311 : Navarro311CatalogueProvenance P.p P.iota.prime
    localBlocks localCentralCharacters
  inductionEquality : BlockInducesTo (localIntersection D J)
    localCentralCharacters globalCentralCharacters
    (irreducibleBrauerCharacterBlock localRoot localBrauerInjective localBlocks localBrauer)
    (irreducibleBrauerCharacterBlock globalRoot globalBrauerInjective globalBlocks globalBrauer)

attribute [instance] ActualIntermediateBlockData.fintypeGlobalBlock
  ActualIntermediateBlockData.fintypeLocalBlock

structure ActualWeightPacket (P : Definition35Problem.{u})
    (psi : Definition35Brauer P) (V : CharacterWeight P.p P.K P.H) where
  quotient : CentralQuotientBrauerSource P psi psi
  ambient : SpathAmbientGroup P psi psi quotient
  embeddingInjective : Function.Injective
    ((quotientToAmbient P psi psi quotient ambient).comp (centralCharacterQuotientMap P psi))
  localGroup : Subgroup ambient.A
  localGroup_eq : localGroup = Subgroup.normalizer
    (V.subgroup.map ((quotientToAmbient P psi psi quotient ambient).comp
      (centralCharacterQuotientMap P psi)) : Set ambient.A)
  localMap : Subgroup.normalizer (V.subgroup : Set P.H) →* localGroup
  localMap_natural : localGroup.subtype.comp localMap =
    ((quotientToAmbient P psi psi quotient ambient).comp
      (centralCharacterQuotientMap P psi)).comp (Subgroup.normalizer (V.subgroup : Set P.H)).subtype
  localMap_range : localMap.range = ambient.base.comap localGroup.subtype
  globalRoot : PrimeRegularRootEmbedding P.p P.k P.K ambient.A
  globalCharacter : IBr globalRoot
  globalRestriction : ∀ x : PrimeRegularElement (G := P.H) P.p,
    globalCharacter.1 (PrimeRegularElement.map
      ((quotientToAmbient P psi psi quotient ambient).comp (centralCharacterQuotientMap P psi)) x) =
      psi.1.1 x
  localRoot : PrimeRegularRootEmbedding P.p P.k P.K localGroup
  localCharacter : IBr localRoot
  localRestriction : ∀ n : PrimeRegularElement
      (G := Subgroup.normalizer (V.subgroup : Set P.H)) P.p,
    localCharacter.1 (PrimeRegularElement.map localMap n) = V.localCharacter (QuotientGroup.mk n.1)
  intermediateBlocks : ∀ (J : Subgroup ambient.A), ambient.base ≤ J →
    ActualIntermediateBlockData P localGroup globalCharacter.1 localCharacter.1 J
  qOne : V.subgroup = ⊥ →
    PrimeRegularClassFunction.pullback localGroup.subtype globalCharacter.1 = localCharacter.1

variable {P : Definition35Problem.{u}} {psi : Definition35Brauer P}
variable {w : Definition35Weight P}

def actualIntermediateOfPacket
    (packet : SpathMatchedBlockCondition P psi psi w)
    (J : Subgroup packet.ambient.A) (hJ : packet.ambient.base ≤ J) :
    ActualIntermediateBlockData P
      (AmbientLocalGroup P psi psi w packet.quotient packet.ambient)
      packet.extensions.globalExtension.1.1 packet.extensions.localExtension.1.1 J := by
  let B := packet.intermediateBlocks.equalityAt J hJ
  exact {
    globalRoot := B.globalRoot
    globalBrauer := B.globalBrauer
    globalRestriction := B.globalRestriction
    localRoot := B.localRoot
    localBrauer := B.localBrauer
    localRestriction := B.localRestriction
    GlobalBlock := B.GlobalBlock
    LocalBlock := B.LocalBlock
    globalBlockIdempotent := B.globalBlockIdempotent
    localBlockIdempotent := B.localBlockIdempotent
    globalBlocks := B.globalBlocks
    localBlocks := B.localBlocks
    globalBrauerInjective := B.globalBrauerInjective
    localBrauerInjective := B.localBrauerInjective
    globalCentralCharacters := B.globalCentralCharacters
    localCentralCharacters := B.localCentralCharacters
    globalCentralCharactersNavarro311 := B.globalCentralCharactersNavarro311
    localCentralCharactersNavarro311 := B.localCentralCharactersNavarro311
    inductionEquality := B.inductionEquality }

def rebasePacket (packet : SpathMatchedBlockCondition P psi psi w)
    (hcenter : Subgroup.center P.H = ⊥)
    (hOne : selectedRadical P w = ⊥ → GlobalLocalExtensionsAgree packet)
    (V : CharacterWeight P.p P.K P.H) (g : P.H)
    (hpair : (selectedCharacterWeight P.blockSource P.block w).rightTwist (MulAut.conj g⁻¹) = V) :
    ActualWeightPacket P psi V := by
  let W := selectedCharacterWeight P.blockSource P.block w
  let alpha := MulAut.conj g⁻¹
  let f := centralCharacterQuotientMap P psi
  let A := innerRebase packet.ambient (f g⁻¹)
  let embed : P.H →* packet.ambient.A := (quotientToAmbient P psi psi packet.quotient A).comp f
  have hemb : embed = (rawEmbedding packet).comp alpha.toMonoidHom := by
    ext x
    change (packet.ambient.baseEquiv (f g⁻¹ * f x * (f g⁻¹)⁻¹) : packet.ambient.A) =
      (packet.ambient.baseEquiv (f (g⁻¹ * x * (g⁻¹)⁻¹)) : packet.ambient.A)
    simp only [map_mul, map_inv, inv_inv]
  have hrad : V.subgroup.map embed = ambientRadical P psi psi w packet.quotient packet.ambient := by
    rw [hemb, embedded_radical_eq W V alpha hpair]
    change W.subgroup.map ((quotientToAmbient P psi psi packet.quotient packet.ambient).comp f) =
      (W.subgroup.map f).map (quotientToAmbient P psi psi packet.quotient packet.ambient)
    rw [Subgroup.map_map]
  let eN := backNormalizerEquiv W V alpha hpair
  let localMap := (rawNormalizerIntoLocal packet).comp eN.toMonoidHom
  refine {
    quotient := packet.quotient
    ambient := A
    embeddingInjective := ?_
    localGroup := AmbientLocalGroup P psi psi w packet.quotient packet.ambient
    localGroup_eq := ?_
    localMap := localMap
    localMap_natural := ?_
    localMap_range := ?_
    globalRoot := packet.extensions.ambientRoot
    globalCharacter := packet.extensions.globalExtension.1
    globalRestriction := ?_
    localRoot := packet.extensions.localAmbientRoot
    localCharacter := packet.extensions.localExtension.1
    localRestriction := ?_
    intermediateBlocks := fun J hJ => actualIntermediateOfPacket packet J hJ
    qOne := ?_ }
  · change Function.Injective embed
    rw [hemb]
    exact (rawEmbedding_injective packet hcenter).comp alpha.injective
  · change Subgroup.normalizer _ = Subgroup.normalizer (V.subgroup.map embed : Set packet.ambient.A)
    rw [hrad]
  · ext n
    have hn := DFunLike.congr_fun (rawNormalizerIntoLocal_natural packet) (eN n)
    change ((rawNormalizerIntoLocal packet) (eN n)).1 = embed n.1
    rw [hemb]
    exact hn.trans (congrArg (rawEmbedding packet) (backNormalizerEquiv_coe W V alpha hpair n))
  · change localMap.range = _
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eN.surjective,
      ← MonoidHom.range_eq_map, rawNormalizerIntoLocal_range packet hcenter]
    rfl
  · intro x
    change packet.extensions.globalExtension.1.1 (PrimeRegularElement.map embed x) = psi.1.1 x
    rw [hemb]
    exact packet_globalExtension_inner_value packet g x
  · exact packet_localExtension_representative_value packet V alpha hpair
  · intro hV
    apply hOne
    change W.subgroup = ⊥
    rw [← subgroup_map_back W V alpha hpair, hV, Subgroup.map_bot]

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualRadicalPacket


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
