import ModularRep.CentralCharacterCovering
import ModularRep.IBrBlockEquivTransport
import ModularRep.NavarroLocalReductionInflationBlockCompatibility
import ModularRep.PaperProofs.EvenFieldFLZCentrelessLocalPackets
import ModularRep.PaperProofs.SpathPositiveQBaseBlock

/-!
# Transporting the positive radical block relation to the base subgroup

This file constructs the global and local group equivalences used to carry
the block relation of a selected weight to the base intermediate subgroup.
The equivalences and their commuting square are proved from the literal group
maps.  Given the kernel-derived selected-weight relation and two raw
primitive-idempotent matches, the final theorem transports that relation.  No
base-stage block-induction relation, BAW
conclusion, or iBAW conclusion is assumed.
-/

noncomputable section

namespace ModularRep.PaperProofs.SpathPositiveQBaseBlockTransport

open ModularRep
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZCentrelessCentralKernel
open ModularRep.PaperProofs.EvenFieldFLZCentrelessLocalPackets
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SpathPositiveQBaseBlock

universe u

noncomputable local instance subgroupFintype
    {G : Type u} [Group G] [Finite G] (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

/-- The centreless quotient equivalence followed by the fixed equivalence
from the quotient to the base subgroup. -/
def positiveQBaseGlobalEquiv
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    {reference psi : Definition35Brauer P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    (ambient : SpathAmbientGroup P reference psi quotient) :
    P.H ≃* ambient.base :=
  (centerlessCentralCharacterQuotientMapEquiv
    P hcenter reference).trans ambient.baseEquiv

/-- The corresponding equivalence between the selected normaliser and the
local subgroup of the base intermediate subgroup. -/
def positiveQQuotientNormalizerEquiv
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference : Definition35Brauer P)
    (w : Definition35Weight P) :
    Subgroup.normalizer (selectedRadical P w : Set P.H) ≃*
      Subgroup.normalizer
        (quotientRadical P reference w :
          Set (CentralCharacterQuotient P reference)) := by
  let eQ :=
    centerlessCentralCharacterQuotientMapEquiv P hcenter reference
  have hQ :
      (selectedRadical P w).map eQ.toMonoidHom =
        quotientRadical P reference w := by
    unfold eQ quotientRadical
    rw [centerlessCentralCharacterQuotientMapEquiv_toMonoidHom]
  have hN :
      Subgroup.normalizer
          (((selectedRadical P w).map eQ.toMonoidHom :
            Subgroup (CentralCharacterQuotient P reference)) : Set _) =
        Subgroup.normalizer
          ((quotientRadical P reference w :
            Subgroup (CentralCharacterQuotient P reference)) :
            Set (CentralCharacterQuotient P reference)) := by
    rw [hQ]
  exact (normalizerEquiv eQ (selectedRadical P w)).trans
    (MulEquiv.subgroupCongr hN)

@[simp]
theorem positiveQQuotientNormalizerEquiv_coe
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference : Definition35Brauer P)
    (w : Definition35Weight P)
    (n : Subgroup.normalizer (selectedRadical P w : Set P.H)) :
    ((positiveQQuotientNormalizerEquiv P hcenter reference w n :
        Subgroup.normalizer
          (quotientRadical P reference w :
            Set (CentralCharacterQuotient P reference))) :
      CentralCharacterQuotient P reference) =
      centerlessCentralCharacterQuotientMapEquiv
        P hcenter reference n := by
  simpa only [positiveQQuotientNormalizerEquiv,
    MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply] using
      normalizerEquiv_coe
        (centerlessCentralCharacterQuotientMapEquiv
          P hcenter reference)
        (selectedRadical P w) n

/-- The canonical map between the two normaliser quotients agrees with the
quotient maps after transporting the source normaliser across the centreless
equivalence. -/
@[simp]
theorem quotientNormalizerMap_mk_positiveQQuotientNormalizerEquiv
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference : Definition35Brauer P)
    (w : Definition35Weight P)
    (n : Subgroup.normalizer (selectedRadical P w : Set P.H)) :
    quotientNormalizerMap P reference w
        (QuotientGroup.mk'
          ((selectedRadical P w).subgroupOf
            (Subgroup.normalizer (selectedRadical P w : Set P.H))) n) =
      quotientLocalInflationMap P reference w
        (positiveQQuotientNormalizerEquiv
          P hcenter reference w n) := by
  let Q := selectedRadical P w
  let f := centralCharacterQuotientMap P reference
  let NG := Subgroup.normalizer (Q : Set P.H)
  let NH := Subgroup.normalizer
    ((Q.map f : Subgroup (CentralCharacterQuotient P reference)) :
      Set (CentralCharacterQuotient P reference))
  let R : Subgroup NG := Q.subgroupOf NG
  let T : Subgroup NH := (Q.map f).subgroupOf NH
  let fN : NG →* NH := normalizerMap f Q
  have hmap : R ≤ T.comap fN := by
    intro q hq
    change f q.1 ∈ Q.map f
    exact ⟨q.1, hq, rfl⟩
  change
    (QuotientGroup.map R T fN hmap)
        (QuotientGroup.mk' R n) =
      QuotientGroup.mk' T
        (positiveQQuotientNormalizerEquiv
          P hcenter reference w n)
  rw [QuotientGroup.map_mk']
  apply congrArg
  apply Subtype.ext
  rw [normalizerMap_coe,
    positiveQQuotientNormalizerEquiv_coe]
  rfl

/-- Homomorphism form of the normaliser-quotient commuting square. -/
theorem quotientNormalizerMap_positiveQ_square
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference : Definition35Brauer P)
    (w : Definition35Weight P) :
    (quotientNormalizerMap P reference w).comp
        (QuotientGroup.mk'
          ((selectedRadical P w).subgroupOf
            (Subgroup.normalizer (selectedRadical P w : Set P.H)))) =
      (quotientLocalInflationMap P reference w).comp
        (positiveQQuotientNormalizerEquiv
          P hcenter reference w).toMonoidHom := by
  ext n
  exact quotientNormalizerMap_mk_positiveQQuotientNormalizerEquiv
    P hcenter reference w n

/-- The corresponding equivalence between the selected normaliser and the
local subgroup of the base intermediate subgroup. -/
def positiveQBaseLocalEquiv
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation :
      QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    (extensions : SpathCharacterExtensions P reference psi w quotient weight
      localInflation ambient) :
    Subgroup.normalizer (selectedRadical P w : Set P.H) ≃*
      IntermediateLocalNormalizer (w := w) ambient ambient.base :=
  (((positiveQQuotientNormalizerEquiv
      P hcenter reference w).trans
    extensions.localBaseEquiv).trans
      (ambientLocalBaseEquivIntermediateLocalBase ambient))

/-- The local equivalence and the global equivalence agree after inclusion
in the base group. -/
@[simp]
theorem positiveQBaseLocalEquiv_coe
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation :
      QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    (extensions : SpathCharacterExtensions P reference psi w quotient weight
      localInflation ambient)
    (n : Subgroup.normalizer (selectedRadical P w : Set P.H)) :
    ((positiveQBaseLocalEquiv P hcenter extensions n :
        IntermediateLocalNormalizer (w := w) ambient ambient.base) :
      ambient.base) =
      positiveQBaseGlobalEquiv P hcenter ambient n := by
  apply Subtype.ext
  change
    (extensions.localBaseEquiv
        (positiveQQuotientNormalizerEquiv
          P hcenter reference w n)).1.1 =
      ambient.base.subtype
        (ambient.baseEquiv
          (centerlessCentralCharacterQuotientMapEquiv
            P hcenter reference n))
  rw [extensions.localBaseEquiv_natural]
  rw [positiveQQuotientNormalizerEquiv_coe]
  rfl

/-- The group equivalences form the commuting square required for transport
of induced central characters. -/
theorem positiveQBaseEquiv_square
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation :
      QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    (extensions : SpathCharacterExtensions P reference psi w quotient weight
      localInflation ambient) :
    (positiveQBaseGlobalEquiv P hcenter ambient).toMonoidHom.comp
        (Subgroup.normalizer
          (selectedRadical P w : Set P.H)).subtype =
      (IntermediateLocalNormalizer
        (w := w) ambient ambient.base).subtype.comp
        (positiveQBaseLocalEquiv P hcenter extensions).toMonoidHom := by
  ext n
  exact congrArg Subtype.val
    (positiveQBaseLocalEquiv_coe
      P hcenter extensions n).symm

/-- Transport the quotient-normaliser root back to the source normaliser. -/
def positiveQSourceNormalizerRoot
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference : Definition35Brauer P)
    (w : Definition35Weight P)
    {weight : QuotientWeightBrauerSource P reference w}
    (localInflation :
      QuotientLocalInflationSource P reference w weight) :
    PrimeRegularRootEmbedding P.p P.k P.K
      (Subgroup.normalizer (selectedRadical P w : Set P.H)) :=
  localInflation.iota.alongMulEquiv
    (positiveQQuotientNormalizerEquiv
      P hcenter reference w).symm

/-- Transport the inflated quotient character back to the source
normaliser. -/
def positiveQSourceNormalizerBrauer
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference : Definition35Brauer P)
    (w : Definition35Weight P)
    {weight : QuotientWeightBrauerSource P reference w}
    (localInflation :
      QuotientLocalInflationSource P reference w weight) :
    IBr
      (positiveQSourceNormalizerRoot
        P hcenter reference w localInflation) :=
  IrreducibleBrauerCharacter.alongMulEquiv
    localInflation.iota
    (positiveQQuotientNormalizerEquiv
      P hcenter reference w).symm
    localInflation.brauer

/-- The transported source-normaliser Brauer character is the literal
reduction of the ordinary inflation of the selected defect-zero quotient
character.  This follows only from the quotient reduction and inflation
equalities and the normaliser-quotient commuting square above. -/
theorem positiveQSourceNormalizerBrauer_isReductionOf_inflatedSelectedLocal
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference : Definition35Brauer P)
    (w : Definition35Weight P)
    (weight : QuotientWeightBrauerSource P reference w)
    (localInflation :
      QuotientLocalInflationSource P reference w weight) :
    NormalizerInflatedReduction
      (selectedCharacterWeight P.blockSource P.block w).subgroup
      (selectedCharacterWeight P.blockSource P.block w).localCharacter
      (positiveQSourceNormalizerRoot
        P hcenter reference w localInflation)
      (positiveQSourceNormalizerBrauer
        P hcenter reference w localInflation) := by
  intro g
  let Q := selectedRadical P w
  let R : Subgroup (Subgroup.normalizer (Q : Set P.H)) :=
    Q.subgroupOf (Subgroup.normalizer (Q : Set P.H))
  let e := positiveQQuotientNormalizerEquiv P hcenter reference w
  let gQ : PrimeRegularElement (G := NormalizerQuotient Q) P.p :=
    PrimeRegularElement.map (QuotientGroup.mk' R) g
  let ge : PrimeRegularElement
      (G := Subgroup.normalizer
        (quotientRadical P reference w :
          Set (CentralCharacterQuotient P reference))) P.p :=
    PrimeRegularElement.map e.toMonoidHom g
  have hinflation := congrArg
    (fun chi : PrimeRegularClassFunction P.K
        (Subgroup.normalizer
          (quotientRadical P reference w :
            Set (CentralCharacterQuotient P reference))) P.p => chi ge)
    localInflation.inflation
  have hsquare :
      PrimeRegularElement.map (quotientNormalizerMap P reference w) gQ =
        PrimeRegularElement.map
          (quotientLocalInflationMap P reference w) ge := by
    apply Subtype.ext
    exact quotientNormalizerMap_mk_positiveQQuotientNormalizerEquiv
      P hcenter reference w g.1
  calc
    (selectedCharacterWeight P.blockSource P.block w).localCharacter
        (QuotientGroup.mk' R g.1) =
        weight.ordinary
          (quotientNormalizerMap P reference w
            (QuotientGroup.mk' R g.1)) :=
      (weight.ordinaryDescends (QuotientGroup.mk' R g.1)).symm
    _ = weight.brauer.1
          (PrimeRegularElement.map
            (quotientNormalizerMap P reference w) gQ) :=
      weight.reduction
        (PrimeRegularElement.map
          (quotientNormalizerMap P reference w) gQ)
    _ = weight.brauer.1
          (PrimeRegularElement.map
            (quotientLocalInflationMap P reference w) ge) := by
      rw [hsquare]
    _ = localInflation.brauer.1 ge := by
      simpa only [PrimeRegularClassFunction.pullback_apply] using hinflation
    _ = (positiveQSourceNormalizerBrauer
          P hcenter reference w localInflation).1 g := by
      simp only [positiveQSourceNormalizerBrauer,
        IrreducibleBrauerCharacter.alongMulEquiv_val,
        PrimeRegularClassFunction.pullback_apply]
      rfl

/-- The source assertion needed to identify the block of the transported
local Brauer character.  It contains no target-stage or block-induction
conclusion. -/
private structure PositiveQSourceNormalizerBlockSupport
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference : Definition35Brauer P)
    (w : Definition35Weight P)
    {weight : QuotientWeightBrauerSource P reference w}
    (localInflation :
      QuotientLocalInflationSource P reference w weight) : Prop where
  block_eq :
    let W := selectedCharacterWeight P.blockSource P.block w
    let O := P.blockSource.operations
    let localData := O.inflatedNormalizerBlockData W.subgroup
    letI : Fintype
        (InflatedNormalizerBlock (k := P.k) W.subgroup) :=
      localData.fintypeBlock
    irreducibleBrauerCharacterBlock
        (positiveQSourceNormalizerRoot
          P hcenter reference w localInflation)
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding
          (positiveQSourceNormalizerRoot
            P hcenter reference w localInflation))
        localData.blocks
        (positiveQSourceNormalizerBrauer
          P hcenter reference w localInflation) =
      O.inflateToNormalizer W.subgroup
        (O.localCharacterBlock
          W.subgroup W.localCharacter W.defectZero)

/-- The generic local reduction-inflation compatibility law, applied to the
kernel-proved reduction identity above, supplies the existing positive-radical
private support record. -/
private theorem positiveQSourceNormalizerBlockSupport_of_compatibility
    (P : Definition35Problem.{u})
    (hcenter : Subgroup.center P.H = ⊥)
    (reference : Definition35Brauer P)
    (w : Definition35Weight P)
    (weight : QuotientWeightBrauerSource P reference w)
    (localInflation :
      QuotientLocalInflationSource P reference w weight)
    (compatibility :
      ModularRep.NavarroLocalReductionInflationBlockCompatibility.Source
        P.blockSource.operations) :
    PositiveQSourceNormalizerBlockSupport
      P hcenter reference w localInflation := by
  refine ⟨?_⟩
  let W := selectedCharacterWeight P.blockSource P.block w
  let O := P.blockSource.operations
  let iotaN := positiveQSourceNormalizerRoot
    P hcenter reference w localInflation
  let phiN := positiveQSourceNormalizerBrauer
    P hcenter reference w localInflation
  have hReduction : NormalizerInflatedReduction
      W.subgroup W.localCharacter iotaN phiN :=
    positiveQSourceNormalizerBrauer_isReductionOf_inflatedSelectedLocal
      P hcenter reference w weight localInflation
  simpa only [W, O, iotaN, phiN,
    ModularRep.NavarroLocalReductionInflationBlockCompatibility.normalizerBrauerBlock,
    ModularRep.CharacterWeight.LocalNormalizerBlockOperations.normalizerBrauerBlock,
    ModularRep.CharacterWeight.LocalBlockInductionOperations.toLocalNormalizerBlockOperations,
    ModularRep.CharacterWeight.InflatedNormalizerBlockCatalogueData.toDecompositionData]
    using compatibility.normalizer_block_of_reduction
      W iotaN phiN hReduction

/-- The serially transported base root and the source-normaliser root have
the same coefficient field lift. -/
theorem baseLocalRoot_lift_eq_positiveQSourceNormalizerRoot
    {P : Definition35Problem.{u}}
    (hcenter : Subgroup.center P.H = ⊥)
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation :
      QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    (extensions : SpathCharacterExtensions P reference psi w quotient weight
      localInflation ambient) :
    (baseLocalRoot extensions).lift =
      (positiveQSourceNormalizerRoot
        P hcenter reference w localInflation).lift := by
  funext z
  calc
    (baseLocalRoot extensions).lift z =
        (localInflation.iota.alongMulEquiv
          extensions.localBaseEquiv).lift z :=
      (localInflation.iota.alongMulEquiv
        extensions.localBaseEquiv).alongMulEquiv_lift
          (ambientLocalBaseEquivIntermediateLocalBase ambient) z
    _ = localInflation.iota.lift z :=
      localInflation.iota.alongMulEquiv_lift
        extensions.localBaseEquiv z
    _ =
        (positiveQSourceNormalizerRoot
          P hcenter reference w localInflation).lift z :=
      (localInflation.iota.alongMulEquiv_lift
        (positiveQQuotientNormalizerEquiv
          P hcenter reference w).symm z).symm

/-- The base local Brauer character is the transport of the source-normaliser
character along the composite local equivalence. -/
theorem baseLocalBrauer_eq_pullback_positiveQBaseLocalEquiv
    {P : Definition35Problem.{u}}
    (hcenter : Subgroup.center P.H = ⊥)
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation :
      QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    (extensions : SpathCharacterExtensions P reference psi w quotient weight
      localInflation ambient) :
    (baseLocalBrauer extensions).1 =
      PrimeRegularClassFunction.pullback
        (positiveQBaseLocalEquiv
          P hcenter extensions).symm.toMonoidHom
        (positiveQSourceNormalizerBrauer
          P hcenter reference w localInflation).1 := by
  apply PrimeRegularClassFunction.ext
  intro x
  simp only [baseLocalBrauer, positiveQSourceNormalizerBrauer,
    IrreducibleBrauerCharacter.alongMulEquiv_val,
    PrimeRegularClassFunction.pullback_apply]
  apply congrArg (fun y ↦ localInflation.brauer.1 y)
  apply Subtype.ext
  change
    extensions.localBaseEquiv.symm
        ((ambientLocalBaseEquivIntermediateLocalBase ambient).symm x.1) =
      (positiveQQuotientNormalizerEquiv
        P hcenter reference w)
        ((positiveQBaseLocalEquiv
          P hcenter extensions).symm x.1)
  have happly :=
    congrArg
      (extensions.localBaseEquiv.trans
        (ambientLocalBaseEquivIntermediateLocalBase ambient)).symm
      ((positiveQBaseLocalEquiv
        P hcenter extensions).apply_symm_apply x.1)
  simpa only [positiveQBaseLocalEquiv, MulEquiv.trans_apply,
    MulEquiv.symm_trans_apply, MulEquiv.apply_symm_apply,
    MulEquiv.symm_apply_apply] using happly.symm

/-- Transporting the quotient root to the base group preserves its lift.
Consequently a quotient root with the source lift gives the source lift at
the base group. -/
theorem baseGlobalRoot_lift_eq_of_quotient
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation :
      QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    (extensions : SpathCharacterExtensions P reference psi w quotient weight
      localInflation ambient)
    (hquotient : quotient.iota.lift = P.iota.lift) :
    (baseGlobalRoot extensions).lift = P.iota.lift := by
  funext z
  exact (quotient.iota.alongMulEquiv_lift ambient.baseEquiv z).trans
    (congrFun hquotient z)

/-- In the centreless case, the Brauer character transported to the base
group is the pullback of the original character along the inverse of the
global equivalence. -/
theorem baseGlobalBrauer_eq_pullback_positiveQBaseGlobalEquiv
    {P : Definition35Problem.{u}}
    (hcenter : Subgroup.center P.H = ⊥)
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation :
      QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    (extensions : SpathCharacterExtensions P reference psi w quotient weight
      localInflation ambient) :
    (baseGlobalBrauer extensions).1 =
      PrimeRegularClassFunction.pullback
        (positiveQBaseGlobalEquiv P hcenter ambient).symm.toMonoidHom
        psi.1.1 := by
  change PrimeRegularClassFunction.pullback
      ambient.baseEquiv.symm.toMonoidHom quotient.brauer.1 =
    PrimeRegularClassFunction.pullback
      (positiveQBaseGlobalEquiv P hcenter ambient).symm.toMonoidHom
      psi.1.1
  apply PrimeRegularClassFunction.ext
  intro x
  simp only [PrimeRegularClassFunction.pullback_apply]
  let eQ := centerlessCentralCharacterQuotientMapEquiv
    P hcenter reference
  let y := PrimeRegularElement.map
    ambient.baseEquiv.symm.toMonoidHom x
  let z := PrimeRegularElement.map eQ.symm.toMonoidHom y
  have hinflation := congrArg
    (fun chi : PrimeRegularClassFunction P.K P.H P.p ↦ chi z)
    quotient.inflation
  change quotient.brauer.1
      (PrimeRegularElement.map
        (centralCharacterQuotientMap P reference) z) =
    psi.1.1 z at hinflation
  calc
    quotient.brauer.1 y =
        quotient.brauer.1
          (PrimeRegularElement.map
            (centralCharacterQuotientMap P reference) z) := by
      congr 1
      apply Subtype.ext
      change y.1 = (centralCharacterQuotientMap P reference) (eQ.symm y.1)
      rw [← centerlessCentralCharacterQuotientMapEquiv_toMonoidHom]
      exact (eQ.apply_symm_apply y.1).symm
    _ = psi.1.1 z := hinflation
    _ = psi.1.1
        (PrimeRegularElement.map
          (positiveQBaseGlobalEquiv P hcenter ambient).symm.toMonoidHom x) := by
      congr 1

/-! ## Block catalogues and the two selected idempotent matches -/

/-- Complete block catalogue data at the base subgroup, without any block
induction relation. -/
structure BaseBlockCatalogueData
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation :
      QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    (extensions : SpathCharacterExtensions P reference psi w quotient weight
      localInflation ambient) where
  GlobalBlock : Type u
  LocalBlock : Type u
  [fintypeGlobalBlock : Fintype GlobalBlock]
  [fintypeLocalBlock : Fintype LocalBlock]
  globalBlockIdempotent : GlobalBlock → MonoidAlgebra P.k ambient.base
  localBlockIdempotent : LocalBlock →
    MonoidAlgebra P.k
      (IntermediateLocalNormalizer (w := w) ambient ambient.base)
  globalBlocks : BlockIdempotentDecomposition globalBlockIdempotent
  localBlocks : BlockIdempotentDecomposition localBlockIdempotent
  globalBrauerInjective :
    IrreducibleBrauerCharacterInjectivity (baseGlobalRoot extensions)
  localBrauerInjective :
    IrreducibleBrauerCharacterInjectivity (baseLocalRoot extensions)
  globalCentralCharacters : BlockCentralCharacterCatalogue globalBlocks
  localCentralCharacters : BlockCentralCharacterCatalogue localBlocks

attribute [instance]
  BaseBlockCatalogueData.fintypeGlobalBlock
  BaseBlockCatalogueData.fintypeLocalBlock

/-- Transport the source global and normaliser block catalogues to the two
base groups.  This is a kernel construction from the catalogues already
present in the local block-induction operations. -/
def baseBlockCatalogueDataOfOperations
    {P : Definition35Problem.{u}}
    (hcenter : Subgroup.center P.H = ⊥)
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation :
      QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    (extensions : SpathCharacterExtensions P reference psi w quotient weight
      localInflation ambient) :
    BaseBlockCatalogueData extensions := by
  let W := selectedCharacterWeight P.blockSource P.block w
  let O := P.blockSource.operations
  let localData := O.inflatedNormalizerBlockData W.subgroup
  letI : Fintype P.Block := O.ambientBlockData.fintypeBlock
  letI : Fintype
      (InflatedNormalizerBlock (k := P.k) W.subgroup) :=
    localData.fintypeBlock
  let eG := positiveQBaseGlobalEquiv P hcenter ambient
  let eL := positiveQBaseLocalEquiv P hcenter extensions
  exact {
    GlobalBlock := P.Block
    LocalBlock := InflatedNormalizerBlock (k := P.k) W.subgroup
    fintypeGlobalBlock := O.ambientBlockData.fintypeBlock
    fintypeLocalBlock := localData.fintypeBlock
    globalBlockIdempotent := fun B =>
      MonoidAlgebra.domCongr P.k P.k eG
        (O.ambientBlockData.blockIdempotent B)
    localBlockIdempotent := fun b =>
      MonoidAlgebra.domCongr P.k P.k eL
        (inflatedNormalizerBlockIdempotent
          (k := P.k) W.subgroup b)
    globalBlocks := O.ambientBlockData.blocks.alongMulEquiv eG
    localBlocks := localData.blocks.alongMulEquiv eL
    globalBrauerInjective :=
      irreducibleBrauerCharacterInjectivity_of_rootEmbedding
        (baseGlobalRoot extensions)
    localBrauerInjective :=
      irreducibleBrauerCharacterInjectivity_of_rootEmbedding
        (baseLocalRoot extensions)
    globalCentralCharacters :=
      O.ambientBlockData.catalogue.alongMulEquiv eG
    localCentralCharacters :=
      localData.catalogue.alongMulEquiv eL }

/-- Coefficient field provenance needed only when the target catalogues are
packaged for the existing base-stage interface. -/
structure BaseBlockCatalogueNavarro311Provenance
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation :
      QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    {extensions : SpathCharacterExtensions P reference psi w quotient weight
      localInflation ambient}
    (_base : BaseBlockCatalogueData extensions) : Prop where
  fieldSource : SpathCoefficientField P.p P.k P.iota.prime

/-- The target global block selected by the transported Brauer character. -/
def selectedBaseGlobalBlock
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation :
      QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    {extensions : SpathCharacterExtensions P reference psi w quotient weight
      localInflation ambient}
    (base : BaseBlockCatalogueData extensions) : base.GlobalBlock :=
  irreducibleBrauerCharacterBlock
    (baseGlobalRoot extensions) base.globalBrauerInjective
    base.globalBlocks (baseGlobalBrauer extensions)

/-- The target local block selected by the transported local Brauer
character. -/
def selectedBaseLocalBlock
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation :
      QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    {extensions : SpathCharacterExtensions P reference psi w quotient weight
      localInflation ambient}
    (base : BaseBlockCatalogueData extensions) : base.LocalBlock :=
  irreducibleBrauerCharacterBlock
    (baseLocalRoot extensions) base.localBrauerInjective
    base.localBlocks (baseLocalBrauer extensions)

/-- The operations-wide Navarro compatibility law identifies the local block
selected at the base intermediate subgroup.  The normaliser reduction used
here is the kernel-derived theorem above, not a source field. -/
theorem selectedBaseLocalBlock_eq_source_of_compatibility
    {P : Definition35Problem.{u}}
    (hcenter : Subgroup.center P.H = ⊥)
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation :
      QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    (extensions : SpathCharacterExtensions P reference psi w quotient weight
      localInflation ambient)
    (compatibility :
      ModularRep.NavarroLocalReductionInflationBlockCompatibility.Source
        P.blockSource.operations) :
    let W := selectedCharacterWeight P.blockSource P.block w
    let O := P.blockSource.operations
    selectedBaseLocalBlock
        (baseBlockCatalogueDataOfOperations
          (P := P) hcenter extensions) =
      O.inflateToNormalizer W.subgroup
        (O.localCharacterBlock
          W.subgroup W.localCharacter W.defectZero) := by
  let W := selectedCharacterWeight P.blockSource P.block w
  let O := P.blockSource.operations
  let localData := O.inflatedNormalizerBlockData W.subgroup
  letI : Fintype
      (InflatedNormalizerBlock (k := P.k) W.subgroup) :=
    localData.fintypeBlock
  let iotaN :=
    positiveQSourceNormalizerRoot
      P hcenter reference w localInflation
  let phiN :=
    positiveQSourceNormalizerBrauer
      P hcenter reference w localInflation
  let support :=
    positiveQSourceNormalizerBlockSupport_of_compatibility
      P hcenter reference w weight localInflation compatibility
  change
    irreducibleBrauerCharacterBlock
        (baseLocalRoot extensions)
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding
          (baseLocalRoot extensions))
        (localData.blocks.alongMulEquiv
          (positiveQBaseLocalEquiv P hcenter extensions))
        (baseLocalBrauer extensions) =
      O.inflateToNormalizer W.subgroup
        (O.localCharacterBlock
          W.subgroup W.localCharacter W.defectZero)
  have hsource := support.block_eq
  change
    irreducibleBrauerCharacterBlock
        iotaN
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iotaN)
        localData.blocks phiN =
      O.inflateToNormalizer W.subgroup
        (O.localCharacterBlock
          W.subgroup W.localCharacter W.defectZero) at hsource
  exact
    (irreducibleBrauerCharacterBlock_alongMulEquiv_of_lift_eq
      (iotaG := iotaN)
      (hinjG :=
        irreducibleBrauerCharacterInjectivity_of_rootEmbedding iotaN)
      (iotaH := baseLocalRoot extensions)
      (hinjH :=
        irreducibleBrauerCharacterInjectivity_of_rootEmbedding
          (baseLocalRoot extensions))
      (e := positiveQBaseLocalEquiv P hcenter extensions)
      (D := localData.blocks)
      (phiG := phiN)
      (phiH := baseLocalBrauer extensions)
      (hlift :=
        baseLocalRoot_lift_eq_positiveQSourceNormalizerRoot
          (P := P) hcenter extensions)
      (hphi :=
        baseLocalBrauer_eq_pullback_positiveQBaseLocalEquiv
          (P := P) hcenter extensions)).trans hsource

section OperationsGlobalSelector

variable {p : ℕ} {k K H Gamma Block : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group H] [Fintype H]
variable [Group Gamma] [Finite Gamma]
variable [MulAction (MulAut H)ᵐᵒᵖ Block]
variable (iota : PrimeRegularRootEmbedding p k K H)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blockSource : LocalBlockInductionSource
  (p := p) (k := k) (K := K) (G := H) (Block := Block))
variable (block : Block)
variable (gamma : Gamma →* MulAut H)
variable (gammaBlock_fixed : ∀ a : Gamma,
  inverseOpHom gamma a • block = block)
variable (brauerSupport :
  OperationsBrauerSupport iota hinj blockSource.operations)
variable (localReduction : ∀ w : LiteralWeightFibre blockSource block,
  SelectedLocalReductionSource blockSource block w)

/-- For an operations-aligned Definition 3.5 problem, transport preserves
the ambient block selected by the source Brauer character. -/
theorem selectedBaseGlobalBlock_eq_block_ofOperations
    (hcenter : Subgroup.center H = ⊥)
    {reference psi : Definition35Brauer
      (Definition35Problem.ofOperations iota hinj blockSource block gamma
        gammaBlock_fixed brauerSupport localReduction)}
    {w : Definition35Weight
      (Definition35Problem.ofOperations iota hinj blockSource block gamma
        gammaBlock_fixed brauerSupport localReduction)}
    {quotient : CentralQuotientBrauerSource
      (Definition35Problem.ofOperations iota hinj blockSource block gamma
        gammaBlock_fixed brauerSupport localReduction) reference psi}
    {weight : QuotientWeightBrauerSource
      (Definition35Problem.ofOperations iota hinj blockSource block gamma
        gammaBlock_fixed brauerSupport localReduction) reference w}
    {localInflation :
      QuotientLocalInflationSource
        (Definition35Problem.ofOperations iota hinj blockSource block gamma
          gammaBlock_fixed brauerSupport localReduction)
        reference w weight}
    {ambient : SpathAmbientGroup
      (Definition35Problem.ofOperations iota hinj blockSource block gamma
        gammaBlock_fixed brauerSupport localReduction)
      reference psi quotient}
    (extensions : SpathCharacterExtensions
      (Definition35Problem.ofOperations iota hinj blockSource block gamma
        gammaBlock_fixed brauerSupport localReduction)
      reference psi w quotient weight localInflation ambient)
    (hquotient : quotient.iota.lift = iota.lift) :
    selectedBaseGlobalBlock
        (baseBlockCatalogueDataOfOperations
          (P := Definition35Problem.ofOperations iota hinj blockSource block
            gamma gammaBlock_fixed brauerSupport localReduction)
          hcenter extensions) =
      block := by
  letI : Fintype Block :=
    blockSource.operations.ambientBlockData.fintypeBlock
  change irreducibleBrauerCharacterBlock
      (baseGlobalRoot extensions)
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding
        (baseGlobalRoot extensions))
      (blockSource.operations.ambientBlockData.blocks.alongMulEquiv
        (positiveQBaseGlobalEquiv
          (Definition35Problem.ofOperations iota hinj blockSource block gamma
            gammaBlock_fixed brauerSupport localReduction)
          hcenter ambient))
      (baseGlobalBrauer extensions) = block
  exact
    (irreducibleBrauerCharacterBlock_alongMulEquiv_of_lift_eq
      (iotaG := iota)
      (hinjG := hinj)
      (iotaH := baseGlobalRoot extensions)
      (hinjH := irreducibleBrauerCharacterInjectivity_of_rootEmbedding
        (baseGlobalRoot extensions))
      (e := positiveQBaseGlobalEquiv
        (Definition35Problem.ofOperations iota hinj blockSource block gamma
          gammaBlock_fixed brauerSupport localReduction)
        hcenter ambient)
      (D := blockSource.operations.ambientBlockData.blocks)
      (phiG := psi.1)
      (phiH := baseGlobalBrauer extensions)
      (hlift := baseGlobalRoot_lift_eq_of_quotient extensions hquotient)
      (hphi := baseGlobalBrauer_eq_pullback_positiveQBaseGlobalEquiv
        hcenter extensions)).trans psi.2

/-- Canonical centreless quotient specialization of the operations-aligned
global selector. -/
theorem selectedBaseGlobalBlock_eq_block_ofOperations_centerless
    (hcenter : Subgroup.center H = ⊥)
    {reference psi : Definition35Brauer
      (Definition35Problem.ofOperations iota hinj blockSource block gamma
        gammaBlock_fixed brauerSupport localReduction)}
    {w : Definition35Weight
      (Definition35Problem.ofOperations iota hinj blockSource block gamma
        gammaBlock_fixed brauerSupport localReduction)}
    {weight : QuotientWeightBrauerSource
      (Definition35Problem.ofOperations iota hinj blockSource block gamma
        gammaBlock_fixed brauerSupport localReduction) reference w}
    {localInflation :
      QuotientLocalInflationSource
        (Definition35Problem.ofOperations iota hinj blockSource block gamma
          gammaBlock_fixed brauerSupport localReduction)
        reference w weight}
    {ambient : SpathAmbientGroup
      (Definition35Problem.ofOperations iota hinj blockSource block gamma
        gammaBlock_fixed brauerSupport localReduction) reference psi
      (centerlessCentralQuotientBrauerSourceFromReference
        (Definition35Problem.ofOperations iota hinj blockSource block gamma
          gammaBlock_fixed brauerSupport localReduction)
        hcenter reference psi)}
    (extensions : SpathCharacterExtensions
      (Definition35Problem.ofOperations iota hinj blockSource block gamma
        gammaBlock_fixed brauerSupport localReduction) reference psi w
      (centerlessCentralQuotientBrauerSourceFromReference
        (Definition35Problem.ofOperations iota hinj blockSource block gamma
          gammaBlock_fixed brauerSupport localReduction)
        hcenter reference psi)
      weight localInflation ambient) :
    selectedBaseGlobalBlock
        (baseBlockCatalogueDataOfOperations
          (P := Definition35Problem.ofOperations iota hinj blockSource block
            gamma gammaBlock_fixed brauerSupport localReduction)
          hcenter extensions) =
      block := by
  exact selectedBaseGlobalBlock_eq_block_ofOperations
    (iota := iota)
    (hinj := hinj)
    (blockSource := blockSource)
    (block := block)
    (gamma := gamma)
    (gammaBlock_fixed := gammaBlock_fixed)
    (brauerSupport := brauerSupport)
    (localReduction := localReduction)
    hcenter extensions
    (centerlessCentralQuotientBrauerSourceFromReference_iota_lift
      (Definition35Problem.ofOperations iota hinj blockSource block gamma
        gammaBlock_fixed brauerSupport localReduction)
      hcenter reference psi)

end OperationsGlobalSelector

/-- The two concrete carrier identifications needed to transport the selected
weight's block relation.  They concern primitive idempotents only and contain
no induced-block equality. -/
structure BaseBlockIdempotentMatches
    {P : Definition35Problem.{u}}
    (hcenter : Subgroup.center P.H = ⊥)
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation :
      QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    {extensions : SpathCharacterExtensions P reference psi w quotient weight
      localInflation ambient}
    (base : BaseBlockCatalogueData extensions) : Prop where
  globalIdempotentMatch :
    let O := P.blockSource.operations
    MonoidAlgebra.domCongr P.k P.k
        (positiveQBaseGlobalEquiv P hcenter ambient)
        (O.ambientBlockData.blockIdempotent P.block) =
      base.globalBlockIdempotent (selectedBaseGlobalBlock base)
  localIdempotentMatch :
    let W := selectedCharacterWeight P.blockSource P.block w
    let O := P.blockSource.operations
    let sourceLocalBlock :=
      O.inflateToNormalizer W.subgroup
        (O.localCharacterBlock
          W.subgroup W.localCharacter W.defectZero)
    MonoidAlgebra.domCongr P.k P.k
        (positiveQBaseLocalEquiv P hcenter extensions)
        (inflatedNormalizerBlockIdempotent
          (k := P.k) W.subgroup sourceLocalBlock) =
      base.localBlockIdempotent (selectedBaseLocalBlock base)

/-- For the catalogues transported from the source operations, the two
idempotent matches are equivalent to the corresponding block index
identifications.  This theorem exposes the exact remaining carrier
obligations but does not prove either identification. -/
theorem baseBlockIdempotentMatches_ofOperations_iff
    {P : Definition35Problem.{u}}
    (hcenter : Subgroup.center P.H = ⊥)
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation :
      QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    (extensions : SpathCharacterExtensions P reference psi w quotient weight
      localInflation ambient) :
    let base := baseBlockCatalogueDataOfOperations hcenter extensions
    let W := selectedCharacterWeight P.blockSource P.block w
    let O := P.blockSource.operations
    let sourceLocalBlock :=
      O.inflateToNormalizer W.subgroup
        (O.localCharacterBlock
          W.subgroup W.localCharacter W.defectZero)
    BaseBlockIdempotentMatches hcenter base ↔
      selectedBaseGlobalBlock base = P.block ∧
      selectedBaseLocalBlock base = sourceLocalBlock := by
  let base := baseBlockCatalogueDataOfOperations hcenter extensions
  let W := selectedCharacterWeight P.blockSource P.block w
  let O := P.blockSource.operations
  let sourceLocalBlock :=
    O.inflateToNormalizer W.subgroup
      (O.localCharacterBlock
        W.subgroup W.localCharacter W.defectZero)
  change BaseBlockIdempotentMatches hcenter base ↔
    selectedBaseGlobalBlock base = P.block ∧
      selectedBaseLocalBlock base = sourceLocalBlock
  constructor
  · intro h
    have hG := h.globalIdempotentMatch
    change base.globalBlockIdempotent P.block =
      base.globalBlockIdempotent (selectedBaseGlobalBlock base) at hG
    have hL := h.localIdempotentMatch
    change base.localBlockIdempotent sourceLocalBlock =
      base.localBlockIdempotent (selectedBaseLocalBlock base) at hL
    have hGi : P.block = selectedBaseGlobalBlock base := by
      apply BlockIdempotentDecomposition.primitiveBlockOfIndex_injective
        base.globalBlocks
      apply Subtype.ext
      exact hG
    have hLi : sourceLocalBlock = selectedBaseLocalBlock base := by
      apply BlockIdempotentDecomposition.primitiveBlockOfIndex_injective
        base.localBlocks
      apply Subtype.ext
      exact hL
    exact ⟨hGi.symm, hLi.symm⟩
  · rintro ⟨hG, hL⟩
    constructor
    · change base.globalBlockIdempotent P.block =
        base.globalBlockIdempotent (selectedBaseGlobalBlock base)
      exact (congrArg base.globalBlockIdempotent hG).symm
    · change base.localBlockIdempotent sourceLocalBlock =
        base.localBlockIdempotent (selectedBaseLocalBlock base)
      exact (congrArg base.localBlockIdempotent hL).symm

/-- The global idempotent match determines the transported global central
character. -/
theorem globalCentralCharacter_match
    {P : Definition35Problem.{u}}
    (hcenter : Subgroup.center P.H = ⊥)
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation :
      QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    {extensions : SpathCharacterExtensions P reference psi w quotient weight
      localInflation ambient}
    (base : BaseBlockCatalogueData extensions)
    (hmatch :
      let O := P.blockSource.operations
      MonoidAlgebra.domCongr P.k P.k
          (positiveQBaseGlobalEquiv P hcenter ambient)
          (O.ambientBlockData.blockIdempotent P.block) =
        base.globalBlockIdempotent (selectedBaseGlobalBlock base)) :
    let O := P.blockSource.operations
    letI : Fintype P.Block := O.ambientBlockData.fintypeBlock
    centralCharacterAlongMulEquiv
        (positiveQBaseGlobalEquiv P hcenter ambient)
        (O.ambientBlockData.catalogue.centralCharacter P.block) =
      base.globalCentralCharacters.centralCharacter
        (selectedBaseGlobalBlock base) := by
  let O := P.blockSource.operations
  letI : Fintype P.Block := O.ambientBlockData.fintypeBlock
  apply centralCharacterAlongMulEquiv_eq_of_blockIdempotent
    (positiveQBaseGlobalEquiv P hcenter ambient)
    O.ambientBlockData.catalogue base.globalCentralCharacters
  apply Subtype.ext
  simpa only [centerDomCongr_coe,
    BlockIdempotentDecomposition.blockIdempotentInCenter_coe] using
      hmatch

/-- The local idempotent match determines the transported local central
character. -/
theorem localCentralCharacter_match
    {P : Definition35Problem.{u}}
    (hcenter : Subgroup.center P.H = ⊥)
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation :
      QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    {extensions : SpathCharacterExtensions P reference psi w quotient weight
      localInflation ambient}
    (base : BaseBlockCatalogueData extensions)
    (hmatch :
      let W := selectedCharacterWeight P.blockSource P.block w
      let O := P.blockSource.operations
      let sourceLocalBlock :=
        O.inflateToNormalizer W.subgroup
          (O.localCharacterBlock
            W.subgroup W.localCharacter W.defectZero)
      MonoidAlgebra.domCongr P.k P.k
          (positiveQBaseLocalEquiv P hcenter extensions)
          (inflatedNormalizerBlockIdempotent
            (k := P.k) W.subgroup sourceLocalBlock) =
        base.localBlockIdempotent (selectedBaseLocalBlock base)) :
    let W := selectedCharacterWeight P.blockSource P.block w
    let O := P.blockSource.operations
    let localData := O.inflatedNormalizerBlockData W.subgroup
    letI : Fintype (InflatedNormalizerBlock (k := P.k) W.subgroup) :=
      localData.fintypeBlock
    let sourceLocalBlock :=
      O.inflateToNormalizer W.subgroup
        (O.localCharacterBlock
          W.subgroup W.localCharacter W.defectZero)
    centralCharacterAlongMulEquiv
        (positiveQBaseLocalEquiv P hcenter extensions)
        (localData.catalogue.centralCharacter sourceLocalBlock) =
      base.localCentralCharacters.centralCharacter
        (selectedBaseLocalBlock base) := by
  let W := selectedCharacterWeight P.blockSource P.block w
  let O := P.blockSource.operations
  let localData := O.inflatedNormalizerBlockData W.subgroup
  let sourceLocalBlock :=
    O.inflateToNormalizer W.subgroup
      (O.localCharacterBlock
        W.subgroup W.localCharacter W.defectZero)
  letI : Fintype (InflatedNormalizerBlock (k := P.k) W.subgroup) :=
    localData.fintypeBlock
  apply centralCharacterAlongMulEquiv_eq_of_blockIdempotent
    (positiveQBaseLocalEquiv P hcenter extensions)
    localData.catalogue base.localCentralCharacters
  apply Subtype.ext
  simpa only [centerDomCongr_coe,
    BlockIdempotentDecomposition.blockIdempotentInCenter_coe] using
      hmatch

/-- The selected weight's original block relation transports to the base
subgroup from the two primitive-idempotent matches. -/
theorem baseBlockInducesTo_of_idempotentMatches
    {P : Definition35Problem.{u}}
    (hcenter : Subgroup.center P.H = ⊥)
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation :
      QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    {extensions : SpathCharacterExtensions P reference psi w quotient weight
      localInflation ambient}
    (base : BaseBlockCatalogueData extensions)
    (idempotents : BaseBlockIdempotentMatches hcenter base) :
    BlockInducesTo
      (IntermediateLocalNormalizer (w := w) ambient ambient.base)
      base.localCentralCharacters base.globalCentralCharacters
      (selectedBaseLocalBlock base) (selectedBaseGlobalBlock base) := by
  let W := selectedCharacterWeight P.blockSource P.block w
  let O := P.blockSource.operations
  let localData := O.inflatedNormalizerBlockData W.subgroup
  letI : Fintype P.Block := O.ambientBlockData.fintypeBlock
  letI : Fintype (InflatedNormalizerBlock (k := P.k) W.subgroup) :=
    localData.fintypeBlock
  exact blockInducesTo_alongMulEquiv
    (Subgroup.normalizer (W.subgroup : Set P.H))
    (IntermediateLocalNormalizer (w := w) ambient ambient.base)
    (positiveQBaseGlobalEquiv P hcenter ambient)
    (positiveQBaseLocalEquiv P hcenter extensions)
    (positiveQBaseEquiv_square P hcenter extensions)
    localData.catalogue O.ambientBlockData.catalogue
    base.localCentralCharacters base.globalCentralCharacters
    (localCentralCharacter_match hcenter base
      idempotents.localIdempotentMatch)
    (globalCentralCharacter_match hcenter base
      idempotents.globalIdempotentMatch)
    (selectedCharacterWeight_blockInducesTo
      P.blockSource P.block w)

/-- The two selected block equalities supply the idempotent matches needed
for the transported block-induction relation. -/
theorem baseBlockInducesTo_of_selectedBlockEqualities
    {P : Definition35Problem.{u}}
    (hcenter : Subgroup.center P.H = ⊥)
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation :
      QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    (extensions : SpathCharacterExtensions P reference psi w quotient weight
      localInflation ambient)
    (hblocks :
      let base := baseBlockCatalogueDataOfOperations hcenter extensions
      let W := selectedCharacterWeight P.blockSource P.block w
      let O := P.blockSource.operations
      let sourceLocalBlock := O.inflateToNormalizer W.subgroup
        (O.localCharacterBlock
          W.subgroup W.localCharacter W.defectZero)
      selectedBaseGlobalBlock base = P.block ∧
        selectedBaseLocalBlock base = sourceLocalBlock) :
    let base := baseBlockCatalogueDataOfOperations hcenter extensions
    BlockInducesTo
      (IntermediateLocalNormalizer (w := w) ambient ambient.base)
      base.localCentralCharacters base.globalCentralCharacters
      (selectedBaseLocalBlock base) (selectedBaseGlobalBlock base) := by
  let base := baseBlockCatalogueDataOfOperations hcenter extensions
  change BlockInducesTo
    (IntermediateLocalNormalizer (w := w) ambient ambient.base)
    base.localCentralCharacters base.globalCentralCharacters
    (selectedBaseLocalBlock base) (selectedBaseGlobalBlock base)
  apply baseBlockInducesTo_of_idempotentMatches hcenter base
  exact (baseBlockIdempotentMatches_ofOperations_iff
    hcenter extensions).2 hblocks

section OperationsCentrelessBlockInduction

variable {p : ℕ} {k K H Gamma Block : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group H] [Fintype H]
variable [Group Gamma] [Finite Gamma]
variable [MulAction (MulAut H)ᵐᵒᵖ Block]
variable (iota : PrimeRegularRootEmbedding p k K H)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blockSource : LocalBlockInductionSource
  (p := p) (k := k) (K := K) (G := H) (Block := Block))
variable (block : Block)
variable (gamma : Gamma →* MulAut H)
variable (gammaBlock_fixed : ∀ a : Gamma,
  inverseOpHom gamma a • block = block)
variable (brauerSupport :
  OperationsBrauerSupport iota hinj blockSource.operations)
variable (localReduction : ∀ w : LiteralWeightFibre blockSource block,
  SelectedLocalReductionSource blockSource block w)

/-- For the operations-aligned centreless problem, the operations-wide
Navarro local compatibility law supplies the local block identification
needed for the transported block-induction relation. -/
theorem baseBlockInducesTo_ofOperations_centerless_of_compatibility
    (hcenter : Subgroup.center H = ⊥)
    {reference psi : Definition35Brauer
      (Definition35Problem.ofOperations iota hinj blockSource block gamma
        gammaBlock_fixed brauerSupport localReduction)}
    {w : Definition35Weight
      (Definition35Problem.ofOperations iota hinj blockSource block gamma
        gammaBlock_fixed brauerSupport localReduction)}
    {weight : QuotientWeightBrauerSource
      (Definition35Problem.ofOperations iota hinj blockSource block gamma
        gammaBlock_fixed brauerSupport localReduction) reference w}
    {localInflation :
      QuotientLocalInflationSource
        (Definition35Problem.ofOperations iota hinj blockSource block gamma
          gammaBlock_fixed brauerSupport localReduction)
        reference w weight}
    {ambient : SpathAmbientGroup
      (Definition35Problem.ofOperations iota hinj blockSource block gamma
        gammaBlock_fixed brauerSupport localReduction) reference psi
      (centerlessCentralQuotientBrauerSourceFromReference
        (Definition35Problem.ofOperations iota hinj blockSource block gamma
          gammaBlock_fixed brauerSupport localReduction)
        hcenter reference psi)}
    (extensions : SpathCharacterExtensions
      (Definition35Problem.ofOperations iota hinj blockSource block gamma
        gammaBlock_fixed brauerSupport localReduction) reference psi w
      (centerlessCentralQuotientBrauerSourceFromReference
        (Definition35Problem.ofOperations iota hinj blockSource block gamma
          gammaBlock_fixed brauerSupport localReduction)
        hcenter reference psi)
      weight localInflation ambient)
    (compatibility :
      ModularRep.NavarroLocalReductionInflationBlockCompatibility.Source
        blockSource.operations) :
    let base := baseBlockCatalogueDataOfOperations
      (P := Definition35Problem.ofOperations iota hinj blockSource block
        gamma gammaBlock_fixed brauerSupport localReduction)
      hcenter extensions
    BlockInducesTo
      (IntermediateLocalNormalizer (w := w) ambient ambient.base)
      base.localCentralCharacters base.globalCentralCharacters
      (selectedBaseLocalBlock base) (selectedBaseGlobalBlock base) := by
  apply baseBlockInducesTo_of_selectedBlockEqualities hcenter extensions
  constructor
  · exact selectedBaseGlobalBlock_eq_block_ofOperations_centerless
      (iota := iota)
      (hinj := hinj)
      (blockSource := blockSource)
      (block := block)
      (gamma := gamma)
      (gammaBlock_fixed := gammaBlock_fixed)
      (brauerSupport := brauerSupport)
      (localReduction := localReduction)
      hcenter extensions
  · exact selectedBaseLocalBlock_eq_source_of_compatibility
      (P := Definition35Problem.ofOperations iota hinj blockSource block
        gamma gammaBlock_fixed brauerSupport localReduction)
      hcenter extensions compatibility

end OperationsCentrelessBlockInduction

/-- Package the derived relation for the existing base-stage interface. -/
def baseBlockInducesFromSelectedWeightOfIdempotentMatches
    {P : Definition35Problem.{u}}
    (hcenter : Subgroup.center P.H = ⊥)
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation :
      QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    {extensions : SpathCharacterExtensions P reference psi w quotient weight
      localInflation ambient}
    (base : BaseBlockCatalogueData extensions)
    (idempotents : BaseBlockIdempotentMatches hcenter base)
    (provenance : BaseBlockCatalogueNavarro311Provenance base) :
    BaseBlockInducesFromSelectedWeight extensions where
  GlobalBlock := base.GlobalBlock
  LocalBlock := base.LocalBlock
  fintypeGlobalBlock := base.fintypeGlobalBlock
  fintypeLocalBlock := base.fintypeLocalBlock
  globalBlockIdempotent := base.globalBlockIdempotent
  localBlockIdempotent := base.localBlockIdempotent
  globalBlocks := base.globalBlocks
  localBlocks := base.localBlocks
  globalBrauerInjective := base.globalBrauerInjective
  localBrauerInjective := base.localBrauerInjective
  globalCentralCharacters := base.globalCentralCharacters
  localCentralCharacters := base.localCentralCharacters
  globalCentralCharactersNavarro311 :=
    { fieldSource := provenance.fieldSource }
  localCentralCharactersNavarro311 :=
    { fieldSource := provenance.fieldSource }
  inductionEquality :=
    baseBlockInducesTo_of_idempotentMatches hcenter base idempotents

end ModularRep.PaperProofs.SpathPositiveQBaseBlockTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
