import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierGlobalExtension
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierLocalExtension
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCyclicBlockChoice
import ModularRep.BrauerCharacterCommonRootCompatibility

/-!
# Lower Späth source data on the named carriers

Actual block catalogues and Navarro's interval central-function identity are
the remaining block data. The subgroup interval, cyclic quotient, quotient
order bound, individual extensions and their root agreements are derived.
One ambient root seed supplies the local seed by restriction and transport.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSpathSource

open Formalisation ModularRep
open ModularRep.FDRepSimpleClassKZero
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZCentrelessLocalPackets
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SpathPositiveQBaseBlock
open ModularRep.PaperProofs.SpathPositiveQTopBlockChoice
open ModularRep.PaperProofs.SporadicFi24SelectedOuterC2
open ModularRep.PaperProofs.SporadicFi24SelectedOuterLocalCarrier
open ModularRep.PaperProofs.SporadicFi24SelectedOuterSpathAmbient
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierABC
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSpathIntervals
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierGlobalExtension
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierLocalExtension
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCyclicBlockChoice

universe u

local instance subgroupFintype {G : Type u} [Group G] [Finite G] (H : Subgroup G) :
    Fintype H := Fintype.ofFinite H

variable (P : Definition35Problem.{u}) (M : EquivariantMatch P)

local instance definition35Prime : Fact P.p.Prime := ⟨P.iota.prime⟩

variable (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
variable (hcenter : Subgroup.center P.H = ⊥) (reference : Definition35Brauer P)
variable (haut : Function.Bijective (semidirectToMulAut (selectedOuterField S)))

local instance outerFinite : Finite (SelectedOuterGroup S) :=
  Finite.of_injective (fun e : SelectedOuterGroup S ↦ (e.1.unop : P.H → P.H))
    (fun _ _ h ↦ Subtype.ext
      (MulOpposite.unop_injective (DFunLike.coe_injective h)))

abbrev Ambient := selectedOuterSpathAmbientCore P hcenter reference M.theta S haut
abbrev SelectedWeight := centerlessQuotientWeightBrauerSource P hcenter reference M.weight

theorem ambient_radical_eq_named :
    ambientRadical P reference M.theta M.weight
      (SelectedCentralQuotient P hcenter reference M.theta)
      (Ambient P M S hcenter reference haut) = QInGTheta P M S :=
  selectedAmbientRadical_eq_raw_subgroupOf P hcenter reference M.theta M.weight S
    M.Omega M.equivariant M.matched haut

theorem ambient_local_eq_named :
    AmbientLocalGroup P reference M.theta M.weight
      (SelectedCentralQuotient P hcenter reference M.theta)
      (Ambient P M S hcenter reference haut) = PairNormalizer P M S := by
  unfold AmbientLocalGroup
  rw [ambient_radical_eq_named P M S hcenter reference haut]

theorem selectedInterval : CentralBrauerInterval (p := P.p)
    (ambientRadical P reference M.theta M.weight
      (SelectedCentralQuotient P hcenter reference M.theta)
      (Ambient P M S hcenter reference haut))
    (AmbientLocalGroup P reference M.theta M.weight
      (SelectedCentralQuotient P hcenter reference M.theta)
      (Ambient P M S hcenter reference haut)) where
  isPGroup := (SelectedWeight P M hcenter reference).radical.isPGroup.map
    (quotientToAmbient P reference M.theta
      (SelectedCentralQuotient P hcenter reference M.theta)
      (Ambient P M S hcenter reference haut))
  pCentralizer_le := sup_le Subgroup.le_normalizer
    (Subgroup.centralizer_le_normalizer _)
  le_normalizer := le_rfl

theorem quotient_cyclic : IsCyclic
    ((Ambient P M S hcenter reference haut).A ⧸
      (Ambient P M S hcenter reference haut).base) := by
  let _ : MulAction (SelectedOuterAmbient S) (IBr P.iota) :=
    selectedBrauerSemidirectAction P.iota S
  exact isCyclic_stabilizer_quotient (phi := selectedOuterField S) M.theta.1

theorem quotient_card_le_two : Nat.card
    ((Ambient P M S hcenter reference haut).A ⧸
      (Ambient P M S hcenter reference haut).base) ≤ 2 :=
  global_quotient_card_le_two P M S

def pairSeedOfAmbient
    (seed : PrimeRegularRootEmbedding P.p P.k P.K (GTheta P M S)) :
    PrimeRegularRootEmbedding P.p P.k P.K (SelectedPairStabilizer P S M.weight) :=
  (PrimeRegularRootEmbedding.ofCommonRoot (G := PairNormalizer P M S)
    P.iota.prime seed.toMulEquiv
    (Nat.ordCompl_dvd_ordCompl_of_dvd
      (Subgroup.card_subgroup_dvd_card (PairNormalizer P M S)) P.p)).alongMulEquiv
        (pairNormalizerEquiv P M S).symm

/-- Complete catalogues and the lower interval identity, before choosing
any ambient extension or its block. -/
structure BlockCatalogues where
  AmbientBlock : Type u
  LocalBlock : Type u
  [ambientFintype : Fintype AmbientBlock]
  [localFintype : Fintype LocalBlock]
  ambientIdempotent : AmbientBlock → P.k[(Ambient P M S hcenter reference haut).A]
  localIdempotent : LocalBlock → P.k[AmbientLocalGroup P reference M.theta M.weight
    (SelectedCentralQuotient P hcenter reference M.theta)
    (Ambient P M S hcenter reference haut)]
  ambientBlocks : BlockIdempotentDecomposition ambientIdempotent
  localBlocks : BlockIdempotentDecomposition localIdempotent
  ambientCharacters : BlockCentralCharacterCatalogue ambientBlocks
  localCharacters : BlockCentralCharacterCatalogue localBlocks
  intervalSource : Navarro414IntervalCentralCharacterSource
    (selectedInterval P M S hcenter reference haut) localBlocks localCharacters

attribute [instance] BlockCatalogues.ambientFintype BlockCatalogues.localFintype

theorem exists_cyclic_inputs_with_retained_lift
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} P.p P.k)
    (seed : PrimeRegularRootEmbedding P.p P.k P.K (GTheta P M S))
    (fieldSource : SpathCoefficientField P.p P.k P.iota.prime)
    (catalogues : BlockCatalogues P M S hcenter reference haut) :
    ∃ localInflation : QuotientLocalInflationSource P reference M.weight
        (SelectedWeight P M hcenter reference),
      ∃ fixedLocal : FixedLocalExtensionData localInflation (Ambient P M S hcenter reference haut),
        ∃ initialGlobal : ChosenGlobalExtensionData (Ambient P M S hcenter reference haut),
          localInflation.iota.lift = (P.localReduction M.weight).iota.lift ∧
          ∀ base : BaseBlockInducesFromSelectedWeight
              (characterExtensionsOfLocalAndGlobal fixedLocal initialGlobal),
            Nonempty (CyclicBlockSource fixedLocal initialGlobal base) := by
  obtain ⟨initialGlobal, hglobal⟩ := exists_global_extension_with_root_agreement
    P hcenter reference M.theta S haut principle seed
  obtain ⟨localInflation, fixedLocal, hselected, hlocal⟩ := exists_local_extension_with_retained_root_agreement
    P hcenter reference M.theta M.weight S M.Omega M.equivariant M.matched haut
    principle (pairSeedOfAmbient P M S seed)
  refine ⟨localInflation, fixedLocal, initialGlobal, hselected, fun base => ⟨?_⟩⟩
  exact {
    AmbientBlock := catalogues.AmbientBlock
    LocalBlock := catalogues.LocalBlock
    fintypeAmbientBlock := catalogues.ambientFintype
    fintypeLocalBlock := catalogues.localFintype
    ambientBlockIdempotent := catalogues.ambientIdempotent
    localBlockIdempotent := catalogues.localIdempotent
    ambientBlocks := catalogues.ambientBlocks
    localBlocks := catalogues.localBlocks
    ambientBrauerInjective := irreducibleBrauerCharacterInjectivity_of_rootEmbedding _
    localBrauerInjective := irreducibleBrauerCharacterInjectivity_of_rootEmbedding _
    ambientCentralCharacters := catalogues.ambientCharacters
    localCentralCharacters := catalogues.localCharacters
    fieldSource := fieldSource
    globalRootAgreement := hglobal
    localRootAgreement := hlocal
    quotientCyclic := quotient_cyclic P M S hcenter reference haut
    quotientCard_le_two := quotient_card_le_two P M S hcenter reference haut
    interval := selectedInterval P M S hcenter reference haut
    intervalSource := catalogues.intervalSource }

theorem exists_cyclic_inputs
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} P.p P.k)
    (seed : PrimeRegularRootEmbedding P.p P.k P.K (GTheta P M S))
    (fieldSource : SpathCoefficientField P.p P.k P.iota.prime)
    (catalogues : BlockCatalogues P M S hcenter reference haut) :
    ∃ localInflation : QuotientLocalInflationSource P reference M.weight
        (SelectedWeight P M hcenter reference),
      ∃ fixedLocal : FixedLocalExtensionData localInflation (Ambient P M S hcenter reference haut),
        ∃ initialGlobal : ChosenGlobalExtensionData (Ambient P M S hcenter reference haut),
          ∀ base : BaseBlockInducesFromSelectedWeight
              (characterExtensionsOfLocalAndGlobal fixedLocal initialGlobal),
            Nonempty (CyclicBlockSource fixedLocal initialGlobal base) := by
  obtain ⟨localInflation, fixedLocal, initialGlobal, _, source⟩ :=
    exists_cyclic_inputs_with_retained_lift P M S hcenter reference haut
      principle seed fieldSource catalogues
  exact ⟨localInflation, fixedLocal, initialGlobal, source⟩
end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSpathSource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
