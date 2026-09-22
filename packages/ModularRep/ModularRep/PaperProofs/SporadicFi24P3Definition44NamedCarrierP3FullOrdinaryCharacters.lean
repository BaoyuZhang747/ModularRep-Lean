import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3FullOrdinaryData
import ModularRep.PaperProofs.SporadicDefectZeroLiteralBaseActual
import ModularRep.FDRepFiniteLength
import Mathlib.Algebra.Category.ModuleCat.Simple
import Mathlib.RepresentationTheory.Character

/-! Consequences of an explicit complete ordinary degree-table realization.
The table realization is an open E2 identification. It contains actual
characters, completeness, degree values and group order, with no defect-zero,
uniqueness, vanishing or block-count field. -/

noncomputable section
open CategoryTheory Module
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3FullOrdinaryCharacters
open ModularRep
open SporadicCompleteCollapseLemma52Actual (GlobalDefectZeroCharacter)
open SporadicFi24P3Definition44NamedCarrierP3FullOrdinaryData

universe u
variable {K G : Type u} [Field K] [CharZero K] [Group G] [Fintype G]

structure FullOrdinaryDegreeTable (K G : Type u)
    [Field K] [CharZero K] [Group G] [Fintype G] where
  character : Fin 108 → OrdinaryIrreducibleCharacter.Irr K G
  complete : Function.Surjective character
  degree : ∀ r, character r 1 = (degrees r : K)
  groupOrder : Nat.card G = 1255205709190661721292800

theorem ordinary_defectZero_iff_degree
    (p : ℕ) (chi : OrdinaryIrreducibleCharacter.Irr K G)
    (n : ℕ) (hdegree : chi 1 = (n : K)) :
    IsDefectZeroOrdinaryCharacter p chi ↔
      ordProj[p] n = ordProj[p] (Nat.card G) := by
  have hdim (V : FDRep K G) (hchar : V.character = chi.val) :
      Module.finrank K V = n := by
    apply Nat.cast_injective (R := K)
    exact (FDRep.char_one V).symm.trans
      ((congrFun hchar 1).trans hdegree)
  constructor
  · rintro ⟨V, _hV, hchar, hz⟩
    simpa only [IsDefectZeroRepresentation, hdim V hchar] using hz
  · intro hz
    obtain ⟨r⟩ := chi.property
    let V : FDRep K G := FDRep.of r.representation
    let F := FDRepFiniteLength.toModuleMonoidAlgebra (k := K) (G := G)
    have hirr : Representation.IsIrreducible V.ρ := r.irreducible
    let _ : Simple (F.obj V) := by
      rw [simple_iff_isSimpleModule]
      exact (Representation.irreducible_iff_isSimpleModule_asModule V.ρ).mp hirr
    have hV : Simple V := Functor.simple_of_simple_obj F V
    have hchar : V.character = chi.val := r.character_eq
    refine ⟨V, hV, hchar, ?_⟩
    change ordProj[p] (Module.finrank K V) = ordProj[p] (Nat.card G)
    rw [hdim V hchar]
    exact hz

theorem defectZero_iff_selected (C : FullOrdinaryDegreeTable K G)
    (chi : OrdinaryIrreducibleCharacter.Irr K G) :
    IsDefectZeroOrdinaryCharacter 3 chi ↔ chi = C.character 93 := by
  constructor
  · intro hchi
    obtain ⟨r, rfl⟩ := C.complete chi
    have hpart := (ordinary_defectZero_iff_degree 3 (C.character r)
      (degrees r) (C.degree r)).mp hchi
    have hdvd := Nat.ordProj_dvd (degrees r) 3
    rw [hpart, C.groupOrder, group_order_three_part] at hdvd
    exact congrArg C.character ((full_part_dvd_degree_iff r).mp hdvd)
  · rintro rfl
    apply (ordinary_defectZero_iff_degree 3 (C.character 93)
      (degrees 93) (C.degree 93)).mpr
    rw [C.groupOrder, group_order_three_part, selected_degree_three_part]

def selectedDefectZeroCharacter (C : FullOrdinaryDegreeTable K G) :
    GlobalDefectZeroCharacter (p := 3) (K := K) (X := G) :=
  ⟨C.character 93, (defectZero_iff_selected C _).mpr rfl⟩

theorem globalDefectZero_subsingleton (C : FullOrdinaryDegreeTable K G) :
    Subsingleton (GlobalDefectZeroCharacter (p := 3) (K := K) (X := G)) := by
  constructor
  intro d e
  apply Subtype.ext
  exact ((defectZero_iff_selected C d.val).mp d.property).trans
    ((defectZero_iff_selected C e.val).mp e.property).symm

theorem regularRestriction_injective (C : FullOrdinaryDegreeTable K G)
    (d e : GlobalDefectZeroCharacter (p := 3) (K := K) (X := G))
    (_ : ∀ g : PrimeRegularElement (G := G) 3, d.val g.val = e.val g.val) :
    d = e :=
  (globalDefectZero_subsingleton C).elim d e

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3FullOrdinaryCharacters


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
