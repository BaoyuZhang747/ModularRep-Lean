import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnQuotientGroupFacts
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
import ModularRep.Navarro414IntervalCentralCharacterAdapter

/-! Actual block induction on the own central quotient for the same raw
match. The two specified block images and upstairs induction are derived.
Only unselected quotient catalogues and generic primitive-image/interval
source laws are additional inputs. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnQuotientBlockInduction

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRawReduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnCentralQuotient
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnNormalizerBrauer
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnQuotientGroupFacts
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientRoot
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSurjectiveRoot
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientBlockAlgebra
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage

universe u
variable (P : Definition35Problem.{u}) (psi : Definition35Brauer P)
variable (V : CharacterWeight P.p P.K P.H) (source : CanonicalRawReduction P.iota V)
variable (compatibility : CanonicalLocalBlockCompatibility P.iota P.blockSource.operations)
variable (hrawBlock :
  letI := P.blockSource.operations.ambientBlockData.fintypeBlock
  P.blockSource.operations.rawWeightBlock V =
    irreducibleBrauerCharacterBlock P.iota P.irreducibleBrauerInjective
      P.blockSource.operations.ambientBlockData.blocks psi.1)
variable (hprimeTo : ¬ P.p ∣ Nat.card (centralCharacterKernel P psi))

local instance problemPrime : Fact P.p.Prime := ⟨P.iota.prime⟩
local instance quotientFintype : Fintype (CentralCharacterQuotient P psi) := Fintype.ofFinite _
local instance subgroupFintype {G : Type u} [Group G] [Finite G] (H : Subgroup G) :
    Fintype H := Fintype.ofFinite H

variable (normalizers : NavarroTiep23cFixedCentralQuotientSource
  (centralCharacterKernel P psi) (show centralCharacterKernel P psi ≤ Subgroup.center P.H from inf_le_left)
  hprimeTo V.subgroup V.radical)

variable {BG BN : Type u} [Fintype BG] [Fintype BN]
variable {eGbar : BG → P.k[CentralCharacterQuotient P psi]}
variable {eNbar : BN → P.k[Subgroup.normalizer
  (V.subgroup.map (centralCharacterQuotientMap P psi) : Set (CentralCharacterQuotient P psi))]}
variable (DGbar : BlockIdempotentDecomposition eGbar) (DNbar : BlockIdempotentDecomposition eNbar)
variable (CGbar : BlockCentralCharacterCatalogue DGbar) (CNbar : BlockCentralCharacterCatalogue DNbar)
variable (S414 : Navarro414IntervalCentralCharacterSource
  (ownNormalizerInterval P psi V hprimeTo normalizers) DNbar CNbar)
variable (Sglobal : CentralPrimeToPrimitiveImageSource (k := P.k)
  (centralCharacterQuotientMap P psi) (QuotientGroup.mk'_surjective _) P.iota.prime
  (own_quotient_ker_central P psi) (own_quotient_ker_primeTo P psi hprimeTo))
variable (Slocal : CentralPrimeToPrimitiveImageSource (k := P.k)
  (ownNormalizerMap P psi V) (ownNormalizerMap_surjective P psi V hprimeTo normalizers) P.iota.prime
  (own_normalizer_ker_central P psi V) (own_normalizer_ker_primeTo P psi V hprimeTo))

include S414 Sglobal Slocal in
theorem own_quotient_block_induction :
    BlockInducesTo
      (Subgroup.normalizer (V.subgroup.map (centralCharacterQuotientMap P psi) :
        Set (CentralCharacterQuotient P psi))) CNbar CGbar
      (irreducibleBrauerCharacterBlock
        (ownNormalizerRoot P psi V source hprimeTo normalizers)
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) DNbar
        (ownNormalizerBrauer P psi V source compatibility hrawBlock hprimeTo normalizers))
      (irreducibleBrauerCharacterBlock
        (quotientRoot P.iota (centralCharacterKernel P psi))
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) DGbar
        (ownQuotientBrauer P psi)) := by
  let O := P.blockSource.operations
  let localData := O.inflatedNormalizerBlockData V.subgroup
  let := O.ambientBlockData.fintypeBlock
  let := localData.fintypeBlock
  let N := Subgroup.normalizer (V.subgroup : Set P.H)
  let Z0 := centralCharacterKernel P psi
  let pi := centralCharacterQuotientMap P psi
  let Nbar := Subgroup.normalizer (V.subgroup.map pi : Set (CentralCharacterQuotient P psi))
  let f := ownNormalizerMap P psi V
  let injN := irreducibleBrauerCharacterInjectivity_of_rootEmbedding source.normalizerRoot
  have hlocal : irreducibleBrauerCharacterBlock source.normalizerRoot injN
      localData.blocks source.localBrauer =
        O.inflateToNormalizer V.subgroup (O.localCharacterBlock V.subgroup V.localCharacter V.defectZero) :=
    compatibility.normalizerBrauerBlock_eq_inflateToNormalizer V source
  have hbase : BlockInducesTo N localData.catalogue O.ambientBlockData.catalogue
      (irreducibleBrauerCharacterBlock source.normalizerRoot injN localData.blocks source.localBrauer)
      (irreducibleBrauerCharacterBlock P.iota P.irreducibleBrauerInjective
        O.ambientBlockData.blocks psi.1) := by
    rw [hlocal, ← hrawBlock]
    exact inducedBlock_spec N localData.catalogue O.ambientBlockData.catalogue
      (O.inflateToNormalizer V.subgroup (O.localCharacterBlock V.subgroup V.localCharacter V.defectZero))
      (O.blockInductionDefined V)
  have globalPhysical := actualBrauerBlock_image pi (QuotientGroup.mk'_surjective Z0)
    P.iota.prime (own_quotient_ker_central P psi) (own_quotient_ker_primeTo P psi hprimeTo)
    Sglobal P.iota (quotientRoot P.iota Z0)
    (fun W => quotientRoot_compatible P.iota Z0 W.ρ)
    P.irreducibleBrauerInjective (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _)
    O.ambientBlockData.blocks DGbar psi.1 (ownQuotientBrauer P psi)
    (ownQuotientBrauer_inflation P psi).symm
  have localPhysical := actualBrauerBlock_image f
    (ownNormalizerMap_surjective P psi V hprimeTo normalizers)
    P.iota.prime (own_normalizer_ker_central P psi V) (own_normalizer_ker_primeTo P psi V hprimeTo)
    Slocal source.normalizerRoot (ownNormalizerRoot P psi V source hprimeTo normalizers)
    (fun W => surjectiveRoot_compatible source.normalizerRoot f
      (ownNormalizerMap_surjective P psi V hprimeTo normalizers) W.ρ)
    injN (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _)
    localData.blocks DNbar source.localBrauer
    (ownNormalizerBrauer P psi V source compatibility hrawBlock hprimeTo normalizers)
    (ownNormalizerBrauer_pullback P psi V source compatibility hrawBlock hprimeTo normalizers).symm
  exact blockInducesTo_map N Nbar pi (QuotientGroup.mk'_surjective Z0)
    f (ownNormalizerMap_surjective P psi V hprimeTo normalizers) (fun _ => rfl)
    (own_normalizer_saturated P psi V hprimeTo normalizers)
    O.ambientBlockData.catalogue CGbar localData.catalogue CNbar
    _ _ _ _ localPhysical globalPhysical hbase (S414.isBlockInductionDefined _)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOwnQuotientBlockInduction



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
