import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierEmbeddedChoiceInputs
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualNormalizerBase
import ModularRep.DefectNormalizerCarrier

/-! Unselected local catalogues and their all-block interval law, indexed
only by the specified embedding and radical, before any local character. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierEmbeddedBlockInputs

open ModularRep ModularRep.CharacterWeight
open SporadicFi24P3Definition44NamedCarrierActualNormalizerBase
open SporadicFi24P3Definition44NamedCarrierEmbeddedChoiceInputs

universe u
variable {p : ℕ} {k G A : Type u} [Field k] [IsAlgClosed k] [CharP k p] [Fact p.Prime]
variable [Group G] [Fintype G] [Group A] [Fintype A]

def PositiveLocalCatalogueInput (i : G →* A) : Prop :=
  ∀ Q : RadicalSubgroup (p := p) (G := G), Q.val ≠ ⊥ →
    UnselectedIntervalCatalogue (k := k) (Q.val.map i) (embeddedNormalizer i Q.val)
      (normalizerCentralBrauerInterval (Q.property.isPGroup.map i))

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierEmbeddedBlockInputs


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
