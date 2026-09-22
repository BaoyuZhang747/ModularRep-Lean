import ModularRep.CentralCharacterCovering
import ModularRep.IBrBlockEquivTransport
import ModularRep.PaperProofs.SpathQOneCharacterExtensions

/-!
# Intermediate block transport in the trivial-radical branch

This experimental module isolates the formal block calculation that becomes
available when a local normaliser is the whole intermediate group.  First, it
proves a source-neutral statement: if the inclusion of a subgroup is a group
equivalence, coefficient restriction followed by transport back along that
equivalence is the identity.  Consequently every block in a transported
central character catalogue induces to the block with the same index.

For the `Q = 1` Spath carrier, the canonical equivalence
`qOneIntermediateLocalEquiv` is literally the subgroup inclusion.  A single
global block decomposition and catalogue at each intermediate group can
therefore be transported to the local carrier.  The local root, Brauer
character, restriction equality, block decomposition, catalogue, selected
block, and `BlockInducesTo` proof are all constructed here.  The local
`Navarro311CatalogueProvenance` contains only coefficient field metadata, so
it is rebuilt by reusing the global packet's `fieldSource`; no local Navarro
block-theory theorem is inferred by transport.

The remaining stored projections contain only the first, global half of each
intermediate packet: a root and restricted irreducible Brauer character, one
complete block catalogue, and its coefficient field provenance.  The record
is nevertheless indexed by the full `SpathCharacterExtensions` packet, which
contains the global and local extension data being related.  In particular
the stored projections contain no local catalogue, block-induction equality,
`SpathLemma61Input`, abstract compatible-extension predicate, abstract
intermediate-block-equality predicate, BAW conclusion, or iBAW conclusion.

The constructors are K deductions relative to `common`, `ambientRoot`,
`hlift`, `localData`, and the global packet.  Their resulting data remains
L over all U/E boundaries inherited through those arguments; kernel checking
does not upgrade the extension, root-binding, local-compatibility, or
catalogue sources.

This is an isolated, non-circular experimental K-relative construction.  It
does not lower the live `SpathLemma61Input` boundary and, in particular, does
not construct its compatible-extension clause.  Compatible extensions remain
E2/U source data; only the `Q = 1` intermediate-block transport described
above is kernel-derived relative to the stated inputs.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep

universe u

section EquivalentSubgroupInduction

variable {k G Block : Type*}
variable [Field k] [Group G]
variable (H : Subgroup G)

/-- If an equivalence from a subgroup to its ambient group is literally the
subgroup inclusion, transporting coefficient restriction back to the ambient
group recovers the original central element. -/
theorem centerDomCongr_symm_centerCoeffRestrict_eq_of_equiv_subtype
    (e : H ≃* G) (he : e.toMonoidHom = H.subtype)
    (z : GroupAlgebraCenter k G) :
    (centerDomCongr (k := k) e.symm).symm
        (centerCoeffRestrict H z) = z := by
  apply Subtype.ext
  ext g
  change
    (MonoidAlgebra.domCongr k k e
        (coeffRestrict H (z : k[G]))).coeff g =
      (z : k[G]).coeff g
  rw [MonoidAlgebra.coeff_domCongr, coeffRestrict_apply]
  have hpoint : ((e.symm g : H) : G) = g := by
    have h := congrArg (fun f : H →* G => f (e.symm g)) he
    simpa using h.symm
  rw [hpoint]

/-- Pointwise form of the preceding identity after evaluation by a central
character. -/
theorem inducedCentralFunction_transport_eq_of_equiv_subtype
    (e : H ≃* G) (he : e.toMonoidHom = H.subtype)
    (lambda : GroupAlgebraCenter k G →ₐ[k] k)
    (z : GroupAlgebraCenter k G) :
    inducedCentralFunction H
        (centralCharacterAlongMulEquiv e.symm lambda) z = lambda z := by
  rw [inducedCentralFunction_apply,
    centralCharacterAlongMulEquiv_apply,
    centerDomCongr_symm_centerCoeffRestrict_eq_of_equiv_subtype
      H e he z]

variable [IsAlgClosed k] [Fintype G] [Fintype Block]

local instance equivalentSubgroupFintype : Fintype H :=
  Fintype.ofFinite H

/-- A block induces to itself when its local decomposition and central
character catalogue are transported along an equivalence whose inverse
carrier map is the literal subgroup inclusion.

This is the missing generic self-induction catalogue theorem.  Definedness
is not assumed: it follows because the induced function is the original
ambient algebra homomorphism. -/
theorem blockInducesTo_self_of_equiv_subtype
    {blockIdempotent : Block → k[G]}
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (catalogue : BlockCentralCharacterCatalogue blocks)
    (e : H ≃* G) (he : e.toMonoidHom = H.subtype)
    (b : Block) :
    BlockInducesTo H (catalogue.alongMulEquiv e.symm) catalogue b b := by
  have hvalue : ∀ z : GroupAlgebraCenter k G,
      inducedCentralFunction H
          ((catalogue.alongMulEquiv e.symm).centralCharacter b) z =
        catalogue.centralCharacter b z := by
    intro z
    exact inducedCentralFunction_transport_eq_of_equiv_subtype
      H e he (catalogue.centralCharacter b) z
  have hdefined : IsBlockInductionDefined H
      ((catalogue.alongMulEquiv e.symm).centralCharacter b) := by
    intro x y
    calc
      inducedCentralFunction H
          ((catalogue.alongMulEquiv e.symm).centralCharacter b) (x * y) =
        catalogue.centralCharacter b (x * y) := hvalue (x * y)
      _ = catalogue.centralCharacter b x *
          catalogue.centralCharacter b y := map_mul _ x y
      _ = inducedCentralFunction H
            ((catalogue.alongMulEquiv e.symm).centralCharacter b) x *
          inducedCentralFunction H
            ((catalogue.alongMulEquiv e.symm).centralCharacter b) y := by
        rw [hvalue x, hvalue y]
  refine ⟨hdefined, ?_⟩
  ext z
  simpa only [inducedCentralCharacter_apply] using hvalue z

end EquivalentSubgroupInduction

end ModularRep

namespace ModularRep.PaperProofs.SpathQOneIntermediateBlockTransport

open ModularRep
open ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SpathQOneCharacterExtensions

universe u

noncomputable local instance subgroupFintype
    {G : Type u} [Group G] [Finite G] (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

/-- The irreducible character and the single global catalogue that remain to
be supplied at one intermediate group.  All local fields of
`IntermediateBlockEqualityAt` will be transported from these data.

The restriction equality is a literal root/character binding, not a block
induction assertion.  Injectivity of the Brauer-character labelling is
kernel-derived from the root embedding and is therefore not a field. -/
structure QOneIntermediateGlobalBlockData
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
    (J : Subgroup ambient.A) where
  globalRoot : PrimeRegularRootEmbedding P.p P.k P.K J
  globalBrauer : IBr globalRoot
  globalRestriction :
    PrimeRegularClassFunction.pullback J.subtype
        extensions.globalExtension.1.1 = globalBrauer.1
  Block : Type u
  [fintypeBlock : Fintype Block]
  blockIdempotent : Block → P.k[J]
  blocks : BlockIdempotentDecomposition blockIdempotent
  centralCharacters : BlockCentralCharacterCatalogue blocks
  centralCharactersNavarro311 :
    Navarro311CatalogueProvenance P.p P.iota.prime
      blocks centralCharacters

attribute [instance] QOneIntermediateGlobalBlockData.fintypeBlock

/-- One global intermediate catalogue for every group in the Spath interval.
Its stored projections are strictly the global half of
`IntermediateBlockSource`: it contains no stored local group data and no
block-induction relation.  Its index is still the full extension packet. -/
structure QOneIntermediateGlobalBlockSource
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
  globalAt : ∀ (J : Subgroup ambient.A), ambient.base ≤ J →
    QOneIntermediateGlobalBlockData extensions J

/-- Transport the global intermediate root to the canonically equal local
normaliser. -/
def qOneIntermediateLocalRoot
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {ambient : SpathAmbientGroup P reference psi quotient}
    (hQ : quotientRadical P reference w = ⊥)
    (J : Subgroup ambient.A)
    (globalRoot : PrimeRegularRootEmbedding P.p P.k P.K J) :
    PrimeRegularRootEmbedding P.p P.k P.K
      (IntermediateLocalNormalizer (w := w) ambient J) :=
  globalRoot.alongMulEquiv
    (qOneIntermediateLocalEquiv ambient hQ J).symm

/-- Transport the global restricted Brauer character to the local
intermediate normaliser. -/
def qOneIntermediateLocalBrauer
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {ambient : SpathAmbientGroup P reference psi quotient}
    (hQ : quotientRadical P reference w = ⊥)
    (J : Subgroup ambient.A)
    (globalRoot : PrimeRegularRootEmbedding P.p P.k P.K J)
    (globalBrauer : IBr globalRoot) :
    IBr (qOneIntermediateLocalRoot hQ J globalRoot) :=
  IrreducibleBrauerCharacter.alongMulEquiv globalRoot
    (qOneIntermediateLocalEquiv ambient hQ J).symm globalBrauer

/-- The ambient and intermediate `Q = 1` equivalences form the literal
restriction square. -/
@[simp]
theorem qOneIntermediateRestriction_square
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    (ambient : SpathAmbientGroup P reference psi quotient)
    (hQ : quotientRadical P reference w = ⊥)
    (J : Subgroup ambient.A) :
    (qOneAmbientLocalEquiv ambient hQ).toMonoidHom.comp
        (intermediateLocalToAmbientLocal (w := w) ambient J) =
      J.subtype.comp
        (qOneIntermediateLocalEquiv ambient hQ J).toMonoidHom := by
  ext x
  rfl

/-- The local restriction of the common `Q = 1` extension is exactly the
transport of the supplied global restricted character. -/
@[simp]
theorem qOneIntermediateLocalRestriction
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation :
      QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    (common : LiveQOneCommonExtensionData ambient)
    (ambientRoot : PrimeRegularRootEmbedding P.p P.k P.K ambient.A)
    (hlift : (quotient.iota.alongMulEquiv ambient.baseEquiv).lift =
      ambientRoot.lift)
    (localData : QOneLocalTransportData localInflation ambient)
    (J : Subgroup ambient.A)
    (global : QOneIntermediateGlobalBlockData
      (spathCharacterExtensionsOfQOneCommon common ambientRoot hlift
        localData) J) :
    PrimeRegularClassFunction.pullback
        (intermediateLocalToAmbientLocal (w := w) ambient J)
        (spathCharacterExtensionsOfQOneCommon common ambientRoot hlift
          localData).localExtension.1.1 =
      (qOneIntermediateLocalBrauer
        localData.quotientRadical_eq_bot J global.globalRoot
          global.globalBrauer).1 := by
  apply PrimeRegularClassFunction.ext
  intro x
  let extensions := spathCharacterExtensionsOfQOneCommon common ambientRoot
    hlift localData
  let eA := qOneAmbientLocalEquiv ambient
    localData.quotientRadical_eq_bot
  let eJ := qOneIntermediateLocalEquiv ambient
    localData.quotientRadical_eq_bot J
  let f := intermediateLocalToAmbientLocal (w := w) ambient J
  have hglobal := congrArg
    (fun chi => chi (PrimeRegularElement.map eJ.toMonoidHom x))
    global.globalRestriction
  have hmap :
      PrimeRegularElement.map eA.toMonoidHom
          (PrimeRegularElement.map f x) =
        PrimeRegularElement.map J.subtype
          (PrimeRegularElement.map eJ.toMonoidHom x) := by
    apply Subtype.ext
    rfl
  have hlocalCharacter :
      extensions.localExtension.1.1 =
        PrimeRegularClassFunction.pullback eA.toMonoidHom
          extensions.globalExtension.1.1 := by
    calc
      extensions.localExtension.1.1 =
          (IrreducibleBrauerCharacter.alongMulEquiv ambientRoot eA.symm
            extensions.globalExtension.1).1 := by
        exact congrArg Subtype.val
          (spathCharacterExtensionsOfQOneCommon_localExtension
            common ambientRoot hlift localData)
      _ = PrimeRegularClassFunction.pullback eA.toMonoidHom
          extensions.globalExtension.1.1 := by
        apply PrimeRegularClassFunction.ext
        intro y
        rfl
  have hlocalPoint := congrArg
    (fun chi => chi (PrimeRegularElement.map f x)) hlocalCharacter
  simp only [PrimeRegularClassFunction.pullback_apply] at hlocalPoint
  have hlocalBrauerCharacter :
      (qOneIntermediateLocalBrauer
          localData.quotientRadical_eq_bot J global.globalRoot
            global.globalBrauer).1 =
        PrimeRegularClassFunction.pullback eJ.toMonoidHom
          global.globalBrauer.1 := by
    unfold qOneIntermediateLocalBrauer
    apply PrimeRegularClassFunction.ext
    intro y
    rfl
  calc
    (PrimeRegularClassFunction.pullback f
        extensions.localExtension.1.1) x =
      extensions.localExtension.1.1
        (PrimeRegularElement.map f x) := rfl
    _ = extensions.globalExtension.1.1
        (PrimeRegularElement.map eA.toMonoidHom
          (PrimeRegularElement.map f x)) := hlocalPoint
    _ = extensions.globalExtension.1.1
        (PrimeRegularElement.map J.subtype
          (PrimeRegularElement.map eJ.toMonoidHom x)) := congrArg _ hmap
    _ = global.globalBrauer.1
        (PrimeRegularElement.map eJ.toMonoidHom x) := hglobal
    _ = (PrimeRegularClassFunction.pullback eJ.toMonoidHom
        global.globalBrauer.1) x := rfl
    _ = (qOneIntermediateLocalBrauer
          localData.quotientRadical_eq_bot J global.globalRoot
            global.globalBrauer).1 x :=
      congrArg (fun chi => chi x) hlocalBrauerCharacter.symm

/-- Construct the complete literal intermediate block equality from its
single global catalogue.  The local catalogue and the induction equality are
not source fields.  The local Navarro provenance reuses only the global
coefficient field metadata, which is the sole field of that provenance
record. -/
noncomputable def intermediateBlockEqualityAtOfQOneGlobal
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation :
      QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    (common : LiveQOneCommonExtensionData ambient)
    (ambientRoot : PrimeRegularRootEmbedding P.p P.k P.K ambient.A)
    (hlift : (quotient.iota.alongMulEquiv ambient.baseEquiv).lift =
      ambientRoot.lift)
    (localData : QOneLocalTransportData localInflation ambient)
    (J : Subgroup ambient.A)
    (global : QOneIntermediateGlobalBlockData
      (spathCharacterExtensionsOfQOneCommon common ambientRoot hlift
        localData) J) :
    IntermediateBlockEqualityAt P reference psi w quotient weight
      localInflation ambient
        (spathCharacterExtensionsOfQOneCommon common ambientRoot hlift
          localData) J := by
  let e := qOneIntermediateLocalEquiv ambient
    localData.quotientRadical_eq_bot J
  have he : e.toMonoidHom =
      (IntermediateLocalNormalizer (w := w) ambient J).subtype := by
    ext x
    rfl
  let globalInjective :
      IrreducibleBrauerCharacterInjectivity global.globalRoot :=
    irreducibleBrauerCharacterInjectivity_of_rootEmbedding global.globalRoot
  let localRoot := qOneIntermediateLocalRoot
    localData.quotientRadical_eq_bot J global.globalRoot
  let localBrauer := qOneIntermediateLocalBrauer
    localData.quotientRadical_eq_bot J global.globalRoot global.globalBrauer
  let localInjective : IrreducibleBrauerCharacterInjectivity localRoot :=
    irreducibleBrauerCharacterInjectivity_of_rootEmbedding localRoot
  have hselected :
      irreducibleBrauerCharacterBlock localRoot localInjective
          (global.blocks.alongMulEquiv e.symm) localBrauer =
        irreducibleBrauerCharacterBlock global.globalRoot globalInjective
          global.blocks global.globalBrauer := by
    exact irreducibleBrauerCharacterBlock_alongMulEquiv
      global.globalRoot globalInjective e.symm localInjective
        global.blocks global.globalBrauer
  have hinduction := blockInducesTo_self_of_equiv_subtype
    (k := P.k)
    (H := IntermediateLocalNormalizer (w := w) ambient J)
    global.blocks global.centralCharacters e he
    (irreducibleBrauerCharacterBlock global.globalRoot globalInjective
      global.blocks global.globalBrauer)
  exact {
    globalRoot := global.globalRoot
    globalBrauer := global.globalBrauer
    globalRestriction := global.globalRestriction
    localRoot := localRoot
    localBrauer := localBrauer
    localRestriction := qOneIntermediateLocalRestriction
      common ambientRoot hlift localData J global
    GlobalBlock := global.Block
    LocalBlock := global.Block
    globalBlockIdempotent := global.blockIdempotent
    localBlockIdempotent := fun b =>
      MonoidAlgebra.domCongr P.k P.k e.symm (global.blockIdempotent b)
    globalBlocks := global.blocks
    localBlocks := global.blocks.alongMulEquiv e.symm
    globalBrauerInjective := globalInjective
    localBrauerInjective := localInjective
    globalCentralCharacters := global.centralCharacters
    localCentralCharacters := global.centralCharacters.alongMulEquiv e.symm
    globalCentralCharactersNavarro311 :=
      global.centralCharactersNavarro311
    localCentralCharactersNavarro311 :=
      ⟨global.centralCharactersNavarro311.fieldSource⟩
    inductionEquality := by
      simpa only [hselected] using hinduction }

/-- Fill all intermediate block equalities in the trivial-radical branch
from one global catalogue per intermediate group. -/
noncomputable def intermediateBlockSourceOfQOneGlobal
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation :
      QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    (common : LiveQOneCommonExtensionData ambient)
    (ambientRoot : PrimeRegularRootEmbedding P.p P.k P.K ambient.A)
    (hlift : (quotient.iota.alongMulEquiv ambient.baseEquiv).lift =
      ambientRoot.lift)
    (localData : QOneLocalTransportData localInflation ambient)
    (global : QOneIntermediateGlobalBlockSource
      (spathCharacterExtensionsOfQOneCommon common ambientRoot hlift
        localData)) :
    IntermediateBlockSource P reference psi w quotient weight localInflation
      ambient
        (spathCharacterExtensionsOfQOneCommon common ambientRoot hlift
          localData) where
  equalityAt J hbase :=
    intermediateBlockEqualityAtOfQOneGlobal common ambientRoot hlift
      localData J (global.globalAt J hbase)

end ModularRep.PaperProofs.SpathQOneIntermediateBlockTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
