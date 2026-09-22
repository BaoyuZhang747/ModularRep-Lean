import ModularRep.PaperProofs.EvenFieldLemma35E1E4Providers
import ModularRep.PaperProofs.EvenFieldLemma35E9E11Providers

/-!
# Combined exact-provider endpoint for Lemma 3.6

This module connects the source-faithful E1--E4 adapter to the exact E9--E11
endpoint.  The resulting theorem no longer accepts an arbitrary block
predicate, rational-series relation, dual-label comparison, or `GlobalInputs`
package.  E5--E8 and the concrete algebraic-group geometry remain explicit.

This is still a relative theorem: constructing the providers from the cited
results for the actual type `C` groups is not carried out here.
-/

namespace ModularRep.PaperProofs.EvenFieldLemma35ExactProviders

open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPair
open ModularRep.PaperProofs.EvenFieldFMZGenericPair
open ModularRep.PaperProofs.EvenFieldLemma35Conclusion
open ModularRep.PaperProofs.EvenFieldLemma35E1E4Providers
open ModularRep.PaperProofs.EvenFieldLemma35E9E11Providers
open ModularRep.PaperProofs.EvenFieldLemma35Relative
open ModularRep.PaperProofs.EvenFieldLeviTorus
open ModularRep.PaperProofs.EvenFieldSourceShaped

variable {Gbar A Block E Dual : Type}
    [Group Gbar] [Group E] [Group Dual] [Fintype Dual]

variable (F : Gbar →* Gbar) (algebraicLift : E → MulAut Gbar)

abbrev H := frobeniusFixedSubgroup F

/-- The full complex-valued relative deduction with E1--E4 and E9--E11
supplied through their source-faithful providers.

The remaining `geometry` argument is exactly the E5--E8 rational-Levi,
torus-realisation, Weyl-quotient, and series-transport package. -/
theorem lemma_3_5_relative_of_all_exact_providers
    [MulAction (MulAut (H F)) A]
    (ell : ℕ) (D : Definitions ℂ (H F) A Block)
    (coherence : InnerCoherence D) (C : Block)
    (e1e4 : ExactE1E4Provider
      (Dual := Dual) F algebraicLift ell D C)
    (centralSylow : Subgroup Gbar → Subgroup Gbar)
    (centralSylow_natural : CharacteristicTorusNatural centralSylow)
    (realise : A → Subgroup Gbar)
    (realise_injective : Function.Injective realise)
    (geometry : ∀ v : GenericPair D coherence C,
      PairGeometrySource F algebraicLift e1e4.algebraicLift_commutes
        (ExactE1E4Provider.toGlobalInputs F algebraicLift e1e4
          centralSylow centralSylow_natural realise realise_injective) v)
    (characters : ∀ v : GenericPair D coherence C,
      ExactCharacterSourceFor F algebraicLift
        e1e4.algebraicLift_commutes (geometry v)) :
    FixationConclusion ell e1e4.inBlock e1e4.globalSeries.series
      D coherence C e1e4.fieldAction := by
  exact lemma_3_5_relative_of_exact_providers
    F algebraicLift e1e4.algebraicLift_commutes
    ell e1e4.inBlock e1e4.globalSeries.series D coherence C
    (ExactE1E4Provider.toGlobalInputs F algebraicLift e1e4
      centralSylow centralSylow_natural realise realise_injective)
    geometry characters

end ModularRep.PaperProofs.EvenFieldLemma35ExactProviders


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
