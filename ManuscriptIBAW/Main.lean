import ManuscriptIBAW.MainClassical
import ManuscriptIBAW.Sporadic.Theorem

/-!
# The main theorem and its finite group consequence

Theorem 1.1 includes all finite simple groups of Types B and C and all
sporadic simple groups. Its proof applies the classical and sporadic
arguments to the specified group presentations.

Corollary 1.2 uses Späth's published reduction theorem as an explicit
external assumption. Simple sections are actual quotients of subgroups. The
conclusion is the equality between the numbers of irreducible Brauer
characters and weight classes in every block of the chosen finite group.
-/

noncomputable section
set_option autoImplicit false

namespace ManuscriptIBAW.Main

open Formalisation.DependencyCases
open ModularRep ModularRep.PaperProofs
open ModularRep.CurrentManuscriptReduction
  (SupportedPresentation SimpleSection BlockwiseAWC)
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family
open SporadicFi24P3Definition44NamedCarrierAcceleratedNamedModels

/-- The presentations in the main theorem include all Type B cases, as
well as type C and the sporadic groups. -/
abbrev Presentation (bases : SporadicGroup → NamedBase.{0})
    (S : Type) [Group S] := SupportedPresentation bases S

theorem sporadic_complete {bases : SporadicGroup → NamedBase.{0}}
    (sources : Sporadic.Theorem.Inputs bases) (s : SporadicGroup) :
    AllPrimeMain (bases s).S := by
  intro ell prime divides
  let c : RelevantCase bases := ⟨s, ⟨ell, prime, divides⟩⟩
  exact ⟨MainCertificate.sporadic (bases s) (sources.models c)
    (MulEquiv.refl _) (sources.complete c)⟩

/-- Theorem 1.1 follows from the Type C theorem, the Type B cases and the sporadic
theorem under their stated source assumptions. -/
theorem theorem_1_1 {bases : SporadicGroup → NamedBase.{0}}
    (classicalSources : ClassicalInputs)
    (sporadicSources : Sporadic.Theorem.Inputs bases)
    (S : Type) [Group S] [Finite S] [IsSimpleGroup S]
    (nonabelian : ¬ IsMulCommutative S) (presentation : Presentation bases S) :
    AllPrimeMain S := by
  cases presentation with
  | typeC n p F rank notSmall coordinate =>
    exact (typeC_complete classicalSources.typeC n p F rank notSmall).along coordinate
  | sporadic s coordinate =>
    exact (sporadic_complete sporadicSources s).along coordinate
  | typeB n p F rank coordinate =>
    letI : IsSimpleGroup (TypeBOrthogonalOmegaCarriers.Omega n F) :=
      coordinate.isSimpleGroup
    have nonabelianOmega : ¬ IsMulCommutative (TypeBOrthogonalOmegaCarriers.Omega n F) := by
      intro commutative
      letI := commutative
      apply nonabelian
      refine ⟨⟨fun (x y : S) => ?_⟩⟩
      apply coordinate.symm.injective
      simp only [map_mul]
      exact mul_comm' (coordinate.symm x) (coordinate.symm y)
    exact (typeB_complete classicalSources n p F rank nonabelianOmega).along coordinate

/-- Corollary 1.2, with the published reduction on the actual simple sections
and the usual defect zero case as its explicit external source. -/
theorem corollary_1_2 {ell : ℕ} (family : Definition35Family.{0} ell)
    (physical : CurrentSpathDescent.PhysicalFamilySource family)
    (field : SpathCoefficientField ell family.k family.ellPrime)
    (reduction : FiniteGroupReductionSource family physical field)
    {bases : SporadicGroup → NamedBase.{0}}
    (classicalSources : ClassicalInputs)
    (sporadicSources : Sporadic.Theorem.Inputs bases)
    (covered : ∀ piece : SimpleSection family.H,
      ell ∣ Nat.card piece.Group → Nonempty (Presentation bases piece.Group)) :
    BlockwiseAWC family := by
  apply reduction.reduce
  intro piece
  by_cases divides : ell ∣ Nat.card piece.Group
  · obtain ⟨presentation⟩ := covered piece divides
    obtain ⟨certificate⟩ := theorem_1_1 classicalSources sporadicSources
      piece.Group piece.nonabelian presentation ell family.ellPrime divides
    exact ⟨SectionEvidence.supported certificate⟩
  · exact ⟨SectionEvidence.primeTo divides⟩

end ManuscriptIBAW.Main

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
this package's formalisation report and source records.
-/
