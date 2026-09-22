import ModularRep.Navarro414IntervalCentralCharacterAdapter

namespace ModularRep

open scoped MonoidAlgebra

noncomputable section

universe u

variable {p : Nat}
variable {k : Type u}
variable {CoverG QuotientG : Type u}
variable {CoverLocal CoverGlobal QuotientLocal QuotientGlobal : Type u}

variable [Field k] [CharP k p] [IsAlgClosed k] [Fact p.Prime]
variable [Group CoverG] [Fintype CoverG]
variable [Group QuotientG] [Fintype QuotientG]
variable [Fintype CoverLocal] [Fintype CoverGlobal]
variable [Fintype QuotientLocal] [Fintype QuotientGlobal]

variable {coverNormalizer : Subgroup CoverG}
variable {quotientNormalizer : Subgroup QuotientG}
variable {quotientDefect : Subgroup QuotientG}

local instance coverNormalizerFintype : Fintype coverNormalizer :=
  Fintype.ofFinite coverNormalizer
local instance quotientNormalizerFintype : Fintype quotientNormalizer :=
  Fintype.ofFinite quotientNormalizer

variable {coverLocalIdempotent : CoverLocal → k[coverNormalizer]}
variable {coverGlobalIdempotent : CoverGlobal → k[CoverG]}
variable {quotientLocalIdempotent : QuotientLocal → k[quotientNormalizer]}
variable {quotientGlobalIdempotent : QuotientGlobal → k[QuotientG]}

variable {coverLocalBlocks :
  BlockIdempotentDecomposition coverLocalIdempotent}
variable {coverGlobalBlocks :
  BlockIdempotentDecomposition coverGlobalIdempotent}
variable {quotientLocalBlocks :
  BlockIdempotentDecomposition quotientLocalIdempotent}
variable {quotientGlobalBlocks :
  BlockIdempotentDecomposition quotientGlobalIdempotent}

variable {coverLocalCatalogue :
  BlockCentralCharacterCatalogue coverLocalBlocks}
variable {coverGlobalCatalogue :
  BlockCentralCharacterCatalogue coverGlobalBlocks}
variable {quotientLocalCatalogue :
  BlockCentralCharacterCatalogue quotientLocalBlocks}
variable {quotientGlobalCatalogue :
  BlockCentralCharacterCatalogue quotientGlobalBlocks}

variable {interval :
  CentralBrauerInterval (p := p) quotientDefect quotientNormalizer}

/-- Reflect a cover-side block induction relation to the quotient side using
Navarro (4.14), forward transport, uniqueness on the cover, and injectivity
of the global block lift. -/
theorem quotientBlockInducesTo_of_414_transport
    (S414 : Navarro414IntervalCentralCharacterSource interval
      quotientLocalBlocks quotientLocalCatalogue)
    (localLift : QuotientLocal → CoverLocal)
    (globalLift : QuotientGlobal ↪ CoverGlobal)
    (transport :
      ∀ {cbar : QuotientLocal} {Bbar : QuotientGlobal},
        BlockInducesTo quotientNormalizer
            quotientLocalCatalogue quotientGlobalCatalogue cbar Bbar →
          BlockInducesTo coverNormalizer
            coverLocalCatalogue coverGlobalCatalogue
            (localLift cbar) (globalLift Bbar))
    (cbar : QuotientLocal) (Bbar : QuotientGlobal)
    (hcover : BlockInducesTo coverNormalizer
      coverLocalCatalogue coverGlobalCatalogue
      (localLift cbar) (globalLift Bbar)) :
    BlockInducesTo quotientNormalizer
      quotientLocalCatalogue quotientGlobalCatalogue cbar Bbar := by
  let Ibar : QuotientGlobal :=
    _root_.ModularRep.navarro414InducedBlock
      S414 quotientGlobalCatalogue cbar
  have hbar : BlockInducesTo quotientNormalizer
      quotientLocalCatalogue quotientGlobalCatalogue cbar Ibar :=
    _root_.ModularRep.navarro414InducedBlock_inducesTo
      S414 quotientGlobalCatalogue cbar
  have hup : BlockInducesTo coverNormalizer
      coverLocalCatalogue coverGlobalCatalogue
      (localLift cbar) (globalLift Ibar) :=
    transport hbar
  have hdefined : IsBlockInductionDefined coverNormalizer
      (coverLocalCatalogue.centralCharacter (localLift cbar)) :=
    _root_.ModularRep.isBlockInductionDefined_of_blockInducesTo
      coverNormalizer coverLocalCatalogue coverGlobalCatalogue hcover
  have hI : globalLift Ibar =
      _root_.ModularRep.inducedBlock
        coverNormalizer coverLocalCatalogue coverGlobalCatalogue
        (localLift cbar) hdefined :=
    _root_.ModularRep.eq_inducedBlock_of_blockInducesTo
      coverNormalizer coverLocalCatalogue coverGlobalCatalogue
      (localLift cbar) hdefined hup
  have hB : globalLift Bbar =
      _root_.ModularRep.inducedBlock
        coverNormalizer coverLocalCatalogue coverGlobalCatalogue
        (localLift cbar) hdefined :=
    _root_.ModularRep.eq_inducedBlock_of_blockInducesTo
      coverNormalizer coverLocalCatalogue coverGlobalCatalogue
      (localLift cbar) hdefined hcover
  have hIbar : Ibar = Bbar :=
    globalLift.injective (hI.trans hB.symm)
  simpa only [hIbar] using hbar

end

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
