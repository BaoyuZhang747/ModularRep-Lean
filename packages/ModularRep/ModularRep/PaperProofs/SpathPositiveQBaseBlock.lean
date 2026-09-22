import ModularRep.PaperProofs.CanonicalLocalBaseTransport

/-!
# The positive radical base block relation

At the base intermediate subgroup, the global and local characters are
canonical transports of the characters already contained in the Späth
extension data.  This module derives those transports and their restriction
identities in the kernel.  It leaves only the literal block induction relation
at the base subgroup as an explicit source packet.

No assertion for arbitrary intermediate subgroups, BAW conclusion, or iBAW
conclusion is a field of that packet.
-/

noncomputable section

namespace ModularRep.PaperProofs.SpathPositiveQBaseBlock

open ModularRep
open ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions

universe u

noncomputable local instance subgroupFintype
    {G : Type u} [Group G] [Finite G] (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

/-- The quotient Brauer root transported to the base subgroup. -/
def baseGlobalRoot
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation :
      QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    (_extensions : SpathCharacterExtensions P reference psi w quotient weight
      localInflation ambient) :
    PrimeRegularRootEmbedding P.p P.k P.K ambient.base :=
  quotient.iota.alongMulEquiv ambient.baseEquiv

/-- The quotient Brauer character transported to the base subgroup. -/
def baseGlobalBrauer
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
    IBr (baseGlobalRoot extensions) :=
  IrreducibleBrauerCharacter.alongMulEquiv
    quotient.iota ambient.baseEquiv quotient.brauer

@[simp]
theorem baseGlobalRestriction
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
    PrimeRegularClassFunction.pullback ambient.base.subtype
        extensions.globalExtension.1.1 =
      (baseGlobalBrauer extensions).1 :=
  extensions.globalExtension.2

/-- The quotient local root transported to the literal local subgroup at the
base intermediate subgroup. -/
def baseLocalRoot
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
      (IntermediateLocalNormalizer (w := w) ambient ambient.base) :=
  (localInflation.iota.alongMulEquiv extensions.localBaseEquiv).alongMulEquiv
    (ambientLocalBaseEquivIntermediateLocalBase ambient)

/-- The quotient local Brauer character transported to the literal local
subgroup at the base intermediate subgroup. -/
def baseLocalBrauer
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
    IBr (baseLocalRoot extensions) :=
  IrreducibleBrauerCharacter.alongMulEquiv
    (localInflation.iota.alongMulEquiv extensions.localBaseEquiv)
    (ambientLocalBaseEquivIntermediateLocalBase ambient)
    (IrreducibleBrauerCharacter.alongMulEquiv
      localInflation.iota extensions.localBaseEquiv localInflation.brauer)

@[simp]
theorem baseLocalRestriction
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
        (intermediateLocalToAmbientLocal (w := w) ambient ambient.base)
        extensions.localExtension.1.1 =
      (baseLocalBrauer extensions).1 := by
  apply PrimeRegularClassFunction.ext
  intro x
  have hx := congrArg
    (fun f =>
      f (PrimeRegularElement.map
        (ambientLocalBaseEquivIntermediateLocalBase ambient).symm.toMonoidHom x))
    extensions.localExtension.2
  simp only [PrimeRegularClassFunction.pullback_apply] at hx ⊢
  have hinput :
      PrimeRegularElement.map
          (AmbientLocalBase P reference psi w quotient ambient).subtype
          (PrimeRegularElement.map
            (ambientLocalBaseEquivIntermediateLocalBase ambient).symm.toMonoidHom x) =
        PrimeRegularElement.map
          (intermediateLocalToAmbientLocal (w := w) ambient ambient.base) x := by
    rfl
  rw [hinput] at hx
  simpa [baseLocalBrauer, ambientLocalBaseEquivIntermediateLocalBase,
    intermediateLocalToAmbientLocal] using hx

/-- Complete literal block data for the one induction relation at the base
intermediate subgroup.  The characters and their restrictions are derived
above rather than supplied as fields. -/
structure BaseBlockInducesFromSelectedWeight
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
  globalCentralCharactersNavarro311 :
    Navarro311CatalogueProvenance P.p P.iota.prime
      globalBlocks globalCentralCharacters
  localCentralCharactersNavarro311 :
    Navarro311CatalogueProvenance P.p P.iota.prime
      localBlocks localCentralCharacters
  inductionEquality :
    BlockInducesTo
      (IntermediateLocalNormalizer (w := w) ambient ambient.base)
      localCentralCharacters globalCentralCharacters
      (irreducibleBrauerCharacterBlock
        (baseLocalRoot extensions) localBrauerInjective
        localBlocks (baseLocalBrauer extensions))
      (irreducibleBrauerCharacterBlock
        (baseGlobalRoot extensions) globalBrauerInjective
        globalBlocks (baseGlobalBrauer extensions))

attribute [instance]
  BaseBlockInducesFromSelectedWeight.fintypeGlobalBlock
  BaseBlockInducesFromSelectedWeight.fintypeLocalBlock

/-- Convert the narrow base packet into the literal intermediate block
equality required at the base subgroup. -/
def intermediateBlockEqualityAtBase
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
    (base : BaseBlockInducesFromSelectedWeight extensions) :
    IntermediateBlockEqualityAt P reference psi w quotient weight
      localInflation ambient extensions ambient.base where
  globalRoot := baseGlobalRoot extensions
  globalBrauer := baseGlobalBrauer extensions
  globalRestriction := baseGlobalRestriction extensions
  localRoot := baseLocalRoot extensions
  localBrauer := baseLocalBrauer extensions
  localRestriction := baseLocalRestriction extensions
  GlobalBlock := base.GlobalBlock
  LocalBlock := base.LocalBlock
  globalBlockIdempotent := base.globalBlockIdempotent
  localBlockIdempotent := base.localBlockIdempotent
  globalBlocks := base.globalBlocks
  localBlocks := base.localBlocks
  globalBrauerInjective := base.globalBrauerInjective
  localBrauerInjective := base.localBrauerInjective
  globalCentralCharacters := base.globalCentralCharacters
  localCentralCharacters := base.localCentralCharacters
  globalCentralCharactersNavarro311 :=
    base.globalCentralCharactersNavarro311
  localCentralCharactersNavarro311 :=
    base.localCentralCharactersNavarro311
  inductionEquality := base.inductionEquality

end ModularRep.PaperProofs.SpathPositiveQBaseBlock


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
