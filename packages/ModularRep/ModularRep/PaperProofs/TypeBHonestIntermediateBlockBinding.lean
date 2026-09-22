import ModularRep.PaperProofs.TypeBCentralKernelTripleCertificate
import ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily

/-!
# Intermediate block data in the chosen ambient

The literal restrictions and block-induction clause are packaged with the
same intermediate roots, characters and specified block catalogues. The
coefficient field metadata supplies their Navarro provenance.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBHonestIntermediateBlockBinding

open ModularRep
open TypeBCentralKernelTripleCertificate
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family
open EvenFieldFLZBAWGoodFamily

universe u

variable {P : Definition35Problem.{u}}
  {reference psi : Definition35Brauer P} {w : Definition35Weight P}
  {quotient : CentralQuotientBrauerSource P reference psi}
  {weight : QuotientWeightBrauerSource P reference w}
  {localInflation : QuotientLocalInflationSource P reference w weight}
  {ambient : SpathAmbientGroup P reference psi quotient}

/-- Preserve the actual intermediate characters and primitive-block
catalogues when forming the Brough--Spath intermediate block datum. -/
def intermediateBlockEqualityAt
    (fieldSource : SpathCoefficientField P.p P.k P.iota.prime)
    (extensions : SpathCharacterExtensions P reference psi w quotient weight
      localInflation ambient)
    (D : TripleData (p := P.p) (k := P.k) (K := P.K)
      ambient.base (AmbientLocalGroup P reference psi w quotient ambient))
    (J : Subgroup ambient.A) (hNJ : ambient.base ≤ J)
    (chiJ : IBr (D.intermediate J hNJ).iota)
    (etaJ : IBr (D.localIntermediateData J hNJ).iota)
    (globalRestriction : PrimeRegularClassFunction.pullback J.subtype
      extensions.globalExtension.1.1 = chiJ.val)
    (localRestriction : PrimeRegularClassFunction.pullback
      (localToU (AmbientLocalGroup P reference psi w quotient ambient) J)
      extensions.localExtension.1.1 = etaJ.val)
    (inductionEquality : IntermediateBlockInduces D J hNJ chiJ etaJ) :
    IntermediateBlockEqualityAt P reference psi w quotient weight
      localInflation ambient extensions J := by
  letI : Fintype J := Fintype.ofFinite J
  letI : Fintype (IntermediateLocalNormalizer (w := w) ambient J) :=
    Fintype.ofFinite (IntermediateLocalNormalizer (w := w) ambient J)
  letI : Fintype (LiteralPrimitiveBlock P.k J) :=
    (D.intermediate J hNJ).blocks.blockFintype
  letI : Fintype (LiteralPrimitiveBlock P.k
      (IntermediateLocalNormalizer (w := w) ambient J)) :=
    (D.localIntermediateData J hNJ).blocks.blockFintype
  exact {
    globalRoot := (D.intermediate J hNJ).iota
    globalBrauer := chiJ
    globalRestriction := globalRestriction
    localRoot := (D.localIntermediateData J hNJ).iota
    localBrauer := etaJ
    localRestriction := localRestriction
    GlobalBlock := LiteralPrimitiveBlock P.k J
    LocalBlock := LiteralPrimitiveBlock P.k
      (IntermediateLocalNormalizer (w := w) ambient J)
    fintypeGlobalBlock := (D.intermediate J hNJ).blocks.blockFintype
    fintypeLocalBlock := (D.localIntermediateData J hNJ).blocks.blockFintype
    globalBlockIdempotent := fun b => b.val
    localBlockIdempotent := fun b => b.val
    globalBlocks := (D.intermediate J hNJ).blocks.decomposition
    localBlocks := (D.localIntermediateData J hNJ).blocks.decomposition
    globalBrauerInjective := (D.intermediate J hNJ).injective
    localBrauerInjective := (D.localIntermediateData J hNJ).injective
    globalCentralCharacters := (D.intermediate J hNJ).blocks.catalogue
    localCentralCharacters := (D.localIntermediateData J hNJ).blocks.catalogue
    globalCentralCharactersNavarro311 := ⟨fieldSource⟩
    localCentralCharactersNavarro311 := ⟨fieldSource⟩
    inductionEquality := inductionEquality }

end ModularRep.PaperProofs.TypeBHonestIntermediateBlockBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
