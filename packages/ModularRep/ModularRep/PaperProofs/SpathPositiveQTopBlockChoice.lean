import ModularRep.PaperProofs.CanonicalLocalBaseTransport

/-!
# The positive-radical top block choice

Späth's cyclic-outer argument first constructs the local character extension
and then chooses a global extension in the block induced from that local
extension.  This module separates that one dependent top choice from the
kernel-derived carrier transports.

No extension, block-induction relation, BAW conclusion, or iBAW conclusion is
asserted without an explicit source field.
-/

noncomputable section

namespace ModularRep.PaperProofs.SpathPositiveQTopBlockChoice

open ModularRep
open ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions

universe u

noncomputable local instance subgroupFintype
    {G : Type u} [Group G] [Finite G] (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

/-- At the top intermediate subgroup, the global carrier is canonically the
ambient group. -/
def topToAmbientEquiv
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    (ambient : SpathAmbientGroup P reference psi quotient) :
    (⊤ : Subgroup ambient.A) ≃* ambient.A :=
  Subgroup.topEquiv

/-- At the top intermediate subgroup, its local normaliser is canonically the
ambient local group. -/
def topLocalToAmbientLocalEquiv
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    (ambient : SpathAmbientGroup P reference psi quotient) :
    IntermediateLocalNormalizer (w := w) ambient (⊤ : Subgroup ambient.A) ≃*
      AmbientLocalGroup P reference psi w quotient ambient where
  toFun x := ⟨x.1.1, x.2⟩
  invFun x := ⟨⟨x.1, Subgroup.mem_top x.1⟩, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The ambient extension character transported to the literal top
intermediate subgroup. -/
def topGlobalRoot
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation :
      QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    (extensions : SpathCharacterExtensions P reference psi w quotient weight
      localInflation ambient) :
    PrimeRegularRootEmbedding P.p P.k P.K (⊤ : Subgroup ambient.A) :=
  extensions.ambientRoot.alongMulEquiv (topToAmbientEquiv ambient).symm

def topGlobalBrauer
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation :
      QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    (extensions : SpathCharacterExtensions P reference psi w quotient weight
      localInflation ambient) :
    IBr (topGlobalRoot extensions) :=
  IrreducibleBrauerCharacter.alongMulEquiv extensions.ambientRoot
    (topToAmbientEquiv ambient).symm extensions.globalExtension.1

@[simp]
theorem topGlobalRestriction
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation :
      QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    (extensions : SpathCharacterExtensions P reference psi w quotient weight
      localInflation ambient) :
    PrimeRegularClassFunction.pullback
        (⊤ : Subgroup ambient.A).subtype extensions.globalExtension.1.1 =
      (topGlobalBrauer extensions).1 := by
  rfl

/-- The fixed local extension character transported to the literal local
normaliser at the top intermediate subgroup. -/
def topLocalRoot
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation :
      QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    (extensions : SpathCharacterExtensions P reference psi w quotient weight
      localInflation ambient) :
    PrimeRegularRootEmbedding P.p P.k P.K
      (IntermediateLocalNormalizer (w := w) ambient
        (⊤ : Subgroup ambient.A)) :=
  extensions.localAmbientRoot.alongMulEquiv
    (topLocalToAmbientLocalEquiv ambient).symm

def topLocalBrauer
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation :
      QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    (extensions : SpathCharacterExtensions P reference psi w quotient weight
      localInflation ambient) :
    IBr (topLocalRoot extensions) :=
  IrreducibleBrauerCharacter.alongMulEquiv extensions.localAmbientRoot
    (topLocalToAmbientLocalEquiv ambient).symm extensions.localExtension.1

@[simp]
theorem topLocalRestriction
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation :
      QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    (extensions : SpathCharacterExtensions P reference psi w quotient weight
      localInflation ambient) :
    PrimeRegularClassFunction.pullback
        (intermediateLocalToAmbientLocal (w := w) ambient
          (⊤ : Subgroup ambient.A))
        extensions.localExtension.1.1 =
      (topLocalBrauer extensions).1 := by
  rfl

/-- The already constructed local half of the Späth extension data. -/
structure FixedLocalExtensionData
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    (localInflation : QuotientLocalInflationSource P reference w weight)
    (ambient : SpathAmbientGroup P reference psi quotient) where
  localAmbientRoot : PrimeRegularRootEmbedding P.p P.k P.K
    (AmbientLocalGroup P reference psi w quotient ambient)
  localExtension :
    Representation.Extension.BrauerCharacterExtensionWitness
      localAmbientRoot
      (localInflation.iota.alongMulEquiv
        (canonicalLocalBaseEquiv ambient))
      (IrreducibleBrauerCharacter.alongMulEquiv
        localInflation.iota (canonicalLocalBaseEquiv ambient)
        localInflation.brauer)

/-- A global extension chosen after the local extension has been fixed. -/
structure ChosenGlobalExtensionData
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    (ambient : SpathAmbientGroup P reference psi quotient) where
  ambientRoot : PrimeRegularRootEmbedding P.p P.k P.K ambient.A
  globalExtension :
    Representation.Extension.BrauerCharacterExtensionWitness
      ambientRoot
      (quotient.iota.alongMulEquiv ambient.baseEquiv)
      (IrreducibleBrauerCharacter.alongMulEquiv
        quotient.iota ambient.baseEquiv quotient.brauer)

/-- Combine the literal Späth extension record from its fixed local half and
one subsequently chosen global extension. -/
def characterExtensionsOfLocalAndGlobal
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation :
      QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    (fixedLocal : FixedLocalExtensionData localInflation ambient)
    (global : ChosenGlobalExtensionData ambient) :
    SpathCharacterExtensions P reference psi w quotient weight
      localInflation ambient where
  ambientRoot := global.ambientRoot
  globalExtension := global.globalExtension
  localBaseEquiv := canonicalLocalBaseEquiv ambient
  localBaseEquiv_natural := canonicalLocalBaseEquiv_natural ambient
  localAmbientRoot := fixedLocal.localAmbientRoot
  localExtension := fixedLocal.localExtension

/-- Complete literal block data for the one top-level induction relation.
The global and local characters are not source fields: they are the canonical
transports of the chosen global extension and the fixed local extension. -/
structure TopBlockInducesFromFixedLocal
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
  globalBlockIdempotent : GlobalBlock →
    MonoidAlgebra P.k (⊤ : Subgroup ambient.A)
  localBlockIdempotent : LocalBlock →
    MonoidAlgebra P.k (IntermediateLocalNormalizer (w := w) ambient
      (⊤ : Subgroup ambient.A))
  globalBlocks : BlockIdempotentDecomposition globalBlockIdempotent
  localBlocks : BlockIdempotentDecomposition localBlockIdempotent
  globalBrauerInjective :
    IrreducibleBrauerCharacterInjectivity (topGlobalRoot extensions)
  localBrauerInjective :
    IrreducibleBrauerCharacterInjectivity (topLocalRoot extensions)
  globalCentralCharacters : BlockCentralCharacterCatalogue globalBlocks
  localCentralCharacters : BlockCentralCharacterCatalogue localBlocks
  globalCentralCharactersNavarro311 :
    Navarro311CatalogueProvenance P.p P.iota.prime
      globalBlocks globalCentralCharacters
  localCentralCharactersNavarro311 :
    Navarro311CatalogueProvenance P.p P.iota.prime
      localBlocks localCentralCharacters
  inductionEquality :
    BlockInducesTo
      (IntermediateLocalNormalizer (w := w) ambient
        (⊤ : Subgroup ambient.A))
      localCentralCharacters globalCentralCharacters
      (irreducibleBrauerCharacterBlock
        (topLocalRoot extensions) localBrauerInjective
        localBlocks (topLocalBrauer extensions))
      (irreducibleBrauerCharacterBlock
        (topGlobalRoot extensions) globalBrauerInjective
        globalBlocks (topGlobalBrauer extensions))

attribute [instance]
  TopBlockInducesFromFixedLocal.fintypeGlobalBlock
  TopBlockInducesFromFixedLocal.fintypeLocalBlock

/-- The top induction packet supplies the full literal block equality at the
top intermediate subgroup; all character restrictions are kernel derived. -/
def intermediateBlockEqualityAtTop
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
    (top : TopBlockInducesFromFixedLocal extensions) :
    IntermediateBlockEqualityAt P reference psi w quotient weight
      localInflation ambient extensions (⊤ : Subgroup ambient.A) where
  globalRoot := topGlobalRoot extensions
  globalBrauer := topGlobalBrauer extensions
  globalRestriction := topGlobalRestriction extensions
  localRoot := topLocalRoot extensions
  localBrauer := topLocalBrauer extensions
  localRestriction := topLocalRestriction extensions
  GlobalBlock := top.GlobalBlock
  LocalBlock := top.LocalBlock
  globalBlockIdempotent := top.globalBlockIdempotent
  localBlockIdempotent := top.localBlockIdempotent
  globalBlocks := top.globalBlocks
  localBlocks := top.localBlocks
  globalBrauerInjective := top.globalBrauerInjective
  localBrauerInjective := top.localBrauerInjective
  globalCentralCharacters := top.globalCentralCharacters
  localCentralCharacters := top.localCentralCharacters
  globalCentralCharactersNavarro311 :=
    top.globalCentralCharactersNavarro311
  localCentralCharactersNavarro311 :=
    top.localCentralCharactersNavarro311
  inductionEquality := top.inductionEquality

/-- The single dependent source choice remaining after the local extension
has been constructed: choose a global extension together with the one top
block-induction relation linking it to that fixed local extension. -/
structure PositiveQTopChoice
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation :
      QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    (fixedLocal : FixedLocalExtensionData localInflation ambient) where
  global : ChosenGlobalExtensionData ambient
  topBlock : TopBlockInducesFromFixedLocal
    (characterExtensionsOfLocalAndGlobal fixedLocal global)

namespace PositiveQTopChoice

def extensions
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation :
      QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    {fixedLocal : FixedLocalExtensionData localInflation ambient}
    (choice : PositiveQTopChoice fixedLocal) :
    SpathCharacterExtensions P reference psi w quotient weight
      localInflation ambient :=
  characterExtensionsOfLocalAndGlobal fixedLocal choice.global

def atTop
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation :
      QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    {fixedLocal : FixedLocalExtensionData localInflation ambient}
    (choice : PositiveQTopChoice fixedLocal) :
    IntermediateBlockEqualityAt P reference psi w quotient weight
      localInflation ambient choice.extensions (⊤ : Subgroup ambient.A) :=
  intermediateBlockEqualityAtTop choice.topBlock

end PositiveQTopChoice

end ModularRep.PaperProofs.SpathPositiveQTopBlockChoice


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
