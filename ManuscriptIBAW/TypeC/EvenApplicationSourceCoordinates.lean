import ModularRep.PaperProofs.EvenFieldFLZ57ChosenRootMetadata

/-! A standard coefficient realisation shared by a covering family and its
finite fixed point quotient. These data identify the coefficients and roots.
Block bijections, character extensions and character triple relations are
separate. -/
noncomputable section
namespace ManuscriptIBAW.TypeC
open ModularRep ModularRep.PaperProofs
open EvenFieldFLZDefinition35Family EvenFieldFLZSourceConditions
open EvenFieldFLZ57ChosenRootMetadata TypeCCoherentFiniteRootConvention

universe u
structure CommonFamilyRoots {ell : ℕ}
    (cover target : Definition35Family.{u} ell) where
  modularField_eq : cover.k = target.k
  ordinaryField_eq : cover.K = target.K
  convention : Convention ell cover.k cover.K
  coverAdmissible : FamilyRootAdmissibility cover convention
  targetAmbient : HEq target.iota (convention.rootAt target.H)
  targetSelected : ∀ (b : target.Block)
      (w : Definition35Weight (target.problem b)),
    HEq (target.localReduction b w).iota
      (convention.rootAt (NormalizerQuotient
        (EvenFieldFLZBAWGoodFamily.selectedRadical (target.problem b) w)))
end ManuscriptIBAW.TypeC

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
