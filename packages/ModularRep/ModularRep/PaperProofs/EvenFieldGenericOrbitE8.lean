import ModularRep.PaperProofs.EvenFieldRelativeDifferenceAdapter

/-!
# A coherent E8 package for one generic pair

This structure groups the representative-level relative Weyl data and the
rational-Levi transport used for one generic pair.  Its exported
`relativeDifference` is derived by the audited E8 adapter.  Packaging these
fields prevents the standard normaliser, Levi subgroup, Weyl quotient, and
selected finite normaliser from being chosen independently at later theorem
boundaries.
-/

namespace ModularRep.PaperProofs.EvenFieldGenericOrbitE8

open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPair
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPairAssembly
open ModularRep.PaperProofs.EvenFieldFixedQuotient
open ModularRep.PaperProofs.EvenFieldRelativeDifferenceAdapter
open ModularRep.PaperProofs.EvenFieldSourceShaped

universe u

variable {G H A WeylNormalizer : Type u}
    [Group G] [Group H] [MulAction (MulAut H) A]
    [Group WeylNormalizer]

/-- Coherent source data for E8 and E5 at one selected algebraic torus. -/
structure Data (sigma : G →* G) (tau : MulAut H) (T : A)
    (L : Subgroup G)
    (B : Subgroup (finiteNormalizer (H := H) (A := A) T))
    (WeylNormalizer : Type u) [Group WeylNormalizer] where
  F : G →* G
  commute : ∀ x : G, F (sigma x) = sigma (F x)
  standardNormalizer : Subgroup (frobeniusFixedSubgroup F)
  standardNormalizer_stable : ∀ x : standardNormalizer,
    frobeniusFixedSubgroupHom F sigma commute x ∈ standardNormalizer
  WeylLevi : Subgroup WeylNormalizer
  weyl : WeylRepresentativeData F sigma commute standardNormalizer
    standardNormalizer_stable L WeylNormalizer WeylLevi
  transport : RationalLeviNormalizerTransport F standardNormalizer L
    (finiteNormalizer (H := H) (A := A) T) B
  intertwines : ∀ (label_fixed : tau • T = T)
      (y : standardNormalizer),
    transport.normalizerEquiv
        (restrictToStableSubgroup standardNormalizer
          (frobeniusFixedSubgroupHom F sigma commute)
          standardNormalizer_stable y) =
      inducedFiniteNormalizerAut tau T label_fixed
        (transport.normalizerEquiv y)

/-- The exact universal relative-difference relation, derived from the E8
package rather than stored in it. -/
theorem Data.relativeDifference
    {sigma : G →* G} {tau : MulAut H} {T : A} {L : Subgroup G}
    {B : Subgroup (finiteNormalizer (H := H) (A := A) T)}
    (D : Data sigma tau T L B WeylNormalizer) :
    ∀ (label_fixed : tau • T = T)
      (x : finiteNormalizer (H := H) (A := A) T),
      x⁻¹ * inducedFiniteNormalizerAut tau T label_fixed x ∈ B :=
  relativeDifference_for_genericOrbit_of_weylData D.F sigma D.commute
    D.standardNormalizer D.standardNormalizer_stable L WeylNormalizer
    D.WeylLevi D.weyl tau T B D.transport D.intertwines

end ModularRep.PaperProofs.EvenFieldGenericOrbitE8


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
