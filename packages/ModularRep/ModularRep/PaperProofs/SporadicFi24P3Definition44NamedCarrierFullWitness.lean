import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierLocalCharacter

/-!
# The concrete pointwise Definition 4.4(3) witness

The fixed associated models afford the same selected theta and local
(theta*)^0 as the ABC carriers. The centraliser and gamma are trivial,
so the two source product denominators and characters reduce to these
named bases and characters. Their quotient cocycles agree up to an
explicit coboundary under the isomorphism induced by normaliser inclusion.

Navarro 8.14--8.15 identifies these associated cocycles with the canonical
obstruction classes used in An--Dietrich 4.4(3d). No implication to an
arbitrary character-triple predicate is part of this witness.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullWitness

open Formalisation ModularRep
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicFi24SelectedOuterC2
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual
open ModularRep.PaperProofs.SporadicFi24P3Definition44Clause3ACWindow
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierABC
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotients
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAssociatedProjectiveModel
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSelectedModels
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierLocalCharacter
open scoped Pointwise

universe u

variable (P : Definition35Problem.{u}) (M : EquivariantMatch P)
variable (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))
variable (hcenter : Subgroup.center P.H = ⊥)
variable (haut : Function.Bijective (semidirectToMulAut (selectedOuterField S)))

include hcenter haut in
theorem centralizer_eq_bot : Centralizer P M S = ⊥ :=
  selectedClause3Centralizer_eq_bot P hcenter M.theta S haut

include hcenter haut in
theorem centralizer_le_pairNormalizer : Centralizer P M S ≤ PairNormalizer P M S := by
  rw [centralizer_eq_bot P M S hcenter haut]
  exact bot_le

include hcenter haut in
theorem global_product_denominator :
    (XInGTheta P M S : Set (GTheta P M S)) * (Centralizer P M S) = XInGTheta P M S := by
  rw [centralizer_eq_bot P M S hcenter haut]
  simp

include hcenter haut in
theorem local_product_denominator :
    (LocalBase P M S : Set (PairNormalizer P M S)) *
      ((Centralizer P M S).subgroupOf (PairNormalizer P M S)) = LocalBase P M S := by
  rw [centralizer_eq_bot P M S hcenter haut]
  simp

include hcenter haut in
theorem centralizer_element_eq_one (c : Centralizer P M S) :
    (c : GTheta P M S) = 1 :=
  (centralizer_eq_bot P M S hcenter haut).le c.2

include hcenter haut in
theorem global_product_element (x : XInGTheta P M S) (c : Centralizer P M S) :
    x.1 * c.1 = x.1 := by
  rw [centralizer_element_eq_one P M S hcenter haut c, mul_one]

include hcenter haut in
theorem local_product_element (x : LocalBase P M S) (c : Centralizer P M S) :
    x.1.1 * c.1 = x.1.1 := by
  rw [centralizer_element_eq_one P M S hcenter haut c, mul_one]

theorem global_gamma_product
    (x : PrimeRegularElement (G := XInGTheta P M S) P.p)
    (c : PrimeRegularElement (G := Centralizer P M S) P.p) :
    (globalCharacter P M S).1 x * (gamma P M S hcenter haut).1 c =
      (globalCharacter P M S).1 x := by
  rw [selectedClause3Gamma_eq_one P hcenter M.theta S haut c, mul_one]

theorem local_gamma_product
    (x : PrimeRegularElement (G := LocalBase P M S) P.p)
    (c : PrimeRegularElement (G := Centralizer P M S) P.p) :
    (namedLocalBrauer P M S).1 x * (gamma P M S hcenter haut).1 c =
      (namedLocalBrauer P M S).1 x := by
  rw [selectedClause3Gamma_eq_one P hcenter M.theta S haut c, mul_one]

/-- Associated-cocycle comparison on the named bases. The centreless
product/character identifications above make this clause (3d) in the full join. -/
structure NamedClause3DWitness where
  globalModel : GlobalModel P M S
  localModel : LocalModel P M S
  cohomology : ScalarFactorSet.Cohomologous localModel.projective.factorSet
    (ScalarFactorSet.pullback (naturalQuotientEquiv P M S) globalModel.projective.factorSet)

theorem namedClause3DWitness_of_cyclicExtension
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} P.p P.k) :
    Nonempty (NamedClause3DWitness P M S) := by
  obtain ⟨G⟩ := selectedGlobalModel P M S principle
  obtain ⟨L⟩ := selectedLocalModel P M S principle
  refine ⟨⟨G, L, ?_⟩⟩
  rw [G.factor_one, L.factor_one]
  exact ScalarFactorSet.trivial_cohomologous_pullback_trivial (naturalQuotientEquiv P M S)

/-- All of pointwise Definition 4.4(3), on the fixed named matched carriers. -/
structure NamedClause3Witness where
  abc : NamedClause3ABCWitness P M S hcenter haut
  d : NamedClause3DWitness P M S

theorem namedClause3Witness_of_equivariantMatch
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} P.p P.k) :
    Nonempty (NamedClause3Witness P M S hcenter haut) := by
  obtain ⟨D⟩ := namedClause3DWitness_of_cyclicExtension P M S principle
  exact ⟨⟨namedClause3ABCWitness_of_equivariantMatch P M S hcenter haut, D⟩⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullWitness


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
