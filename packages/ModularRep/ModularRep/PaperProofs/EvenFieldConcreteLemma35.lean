import ModularRep.PaperProofs.EvenFieldConcreteTypeCFiniteModel
import ModularRep.PaperProofs.EvenFieldLemma35ExactProviders

/-!
# Concrete relative endpoint for manuscript Lemma 3.6

This module instantiates the structural carrier of the relative Lemma 3.6
proof with the literal even-field symplectic fixed-point group.  The ambient
group, defining Frobenius, finite group, cyclic field action, and its
identification with `Sp_(2r)(2^a)` are kernel constructed in the preceding
concrete modules.

The remaining fields are the individually exposed representation theoretic
and algebraic-group inputs E1--E11.  No field states character fixation,
generic-weight fixation, or the conclusion of Lemma 3.6.  Consequently the
theorem below is a manuscript-specific relative verification, not an
unconditional formal proof of the cited results.
-/

namespace ModularRep.PaperProofs.EvenFieldConcreteLemma35

open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPair
open ModularRep.PaperProofs.EvenFieldConcreteTypeC
open ModularRep.PaperProofs.EvenFieldFMZGenericPair
open ModularRep.PaperProofs.EvenFieldLemma35Conclusion
open ModularRep.PaperProofs.EvenFieldLemma35E1E4Providers
open ModularRep.PaperProofs.EvenFieldLemma35E9E11Providers
open ModularRep.PaperProofs.EvenFieldLemma35ExactProviders
open ModularRep.PaperProofs.EvenFieldLemma35Relative
open ModularRep.PaperProofs.EvenFieldLeviTorus
open ModularRep.PaperProofs.EvenFieldSourceShaped

noncomputable section

/-- Exact external inputs for Lemma 3.6 after its ambient and finite groups
have been fixed to the concrete type `C` matrix models.

`e1e4` contains the block, Lusztig-series, and dual-Levi inputs.  `geometry`
contains E5--E8, and `characters` contains the exact E9--E11 extension,
Clifford, and Gallagher inputs. -/
structure Inputs
    {A Block Dual : Type} [Group Dual] [Fintype Dual]
    (r a ell : ℕ) (ha : 0 < a)
    [MulAction (MulAut (FiniteSymplecticFixed r a)) A]
    (D : Definitions ℂ (FiniteSymplecticFixed r a) A Block)
    (coherence : InnerCoherence D) (C : Block) where
  e1e4 : E1E4RepresentationInputs
    (A := A) (Block := Block) (Dual := Dual) r a ell ha D C
  centralSylow : Subgroup (AmbientSymplectic r) →
    Subgroup (AmbientSymplectic r)
  centralSylow_natural : CharacteristicTorusNatural centralSylow
  realise : A → Subgroup (AmbientSymplectic r)
  realise_injective : Function.Injective realise
  geometry : ∀ v : GenericPair D coherence C,
    PairGeometrySource (definingFrobenius r a) (algebraicLift r a)
      (algebraicLift_commutes r a)
      (ExactE1E4Provider.toGlobalInputs
        (definingFrobenius r a) (algebraicLift r a)
        (e1e4.toExactProvider r a ell ha)
        centralSylow centralSylow_natural realise realise_injective) v
  characters : ∀ v : GenericPair D coherence C,
    ExactCharacterSourceFor (definingFrobenius r a) (algebraicLift r a)
      (algebraicLift_commutes r a) (geometry v)

/-- Manuscript Lemma 3.6 on the literal group
the fixed-point model `AmbientSymplectic(r)^(F_2^a)`, which
`standardEvenSymplecticEquivFixedPoints` proves isomorphic to
`Sp_(2r)(2^a)`, relative only to the exact source inputs stored in
`Inputs`. -/
theorem lemma_3_5_concrete_relative
    {A Block Dual : Type} [Group Dual] [Fintype Dual]
    (r a ell : ℕ) (ha : 0 < a)
    [MulAction (MulAut (FiniteSymplecticFixed r a)) A]
    (D : Definitions ℂ (FiniteSymplecticFixed r a) A Block)
    (coherence : InnerCoherence D) (C : Block)
    (S : Inputs (A := A) (Block := Block) (Dual := Dual)
      r a ell ha D coherence C) :
    FixationConclusion ell
      (S.e1e4.toExactProvider r a ell ha).inBlock
      (S.e1e4.toExactProvider r a ell ha).globalSeries.series
      D coherence C (fieldAction r a ha) := by
  exact lemma_3_5_relative_of_all_exact_providers
    (definingFrobenius r a) (algebraicLift r a)
    ell D coherence C (S.e1e4.toExactProvider r a ell ha)
    S.centralSylow S.centralSylow_natural S.realise S.realise_injective
    S.geometry S.characters

end

end ModularRep.PaperProofs.EvenFieldConcreteLemma35


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
