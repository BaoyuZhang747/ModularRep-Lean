import ModularRep.IBrSimpleModuleClass
import ModularRep.OrdinaryIrreducibleCharacter
import ModularRep.SimpleTraceLinearIndependence

/-!
# Simple-module labels for ordinary irreducible characters

This file associates to every function-valued ordinary irreducible character
the simple group algebra module class of a chosen realisation.  Over an
algebraically closed field, the association is injective because the
characters of the chosen simple modules are linearly independent.

The construction is used only to connect the actual `Irr` carrier with exact
`K₀`; it does not choose a basic set or a blockwise bijection.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.OrdinaryIrreducibleCharacter

open ModularRep.FDRepSimpleClassKZero

universe u

variable {K G : Type u}
variable [Field K] [CharZero K] [IsAlgClosed K] [Group G] [Finite G]

/-- A chosen finite-dimensional irreducible realisation of an ordinary
irreducible character. -/
def chosenRealisation (chi : Irr K G) : Realisation K G chi.1 :=
  Classical.choice chi.2

/-- The chosen realisation as a bundled finite-dimensional
representation. -/
def chosenFDRep (chi : Irr K G) : FDRep K G :=
  FDRep.of (chosenRealisation chi).representation

/-- The chosen representation realising `chi` is irreducible. -/
theorem chosenFDRep_irreducible (chi : Irr K G) :
    Representation.IsIrreducible (FDRep.ρ (chosenFDRep chi)) := by
  change Representation.IsIrreducible (chosenRealisation chi).representation
  exact (chosenRealisation chi).irreducible

/-- The trace character of the chosen representation is the original
function-valued character. -/
theorem chosenFDRep_character (chi : Irr K G) :
    (chosenFDRep chi).character = chi.1 :=
  (chosenRealisation chi).character_eq

/-- The simple group algebra module class underlying the chosen
realisation. -/
def simpleModuleClassLabel (chi : Irr K G) : SimpleModuleClass K[G] :=
  simpleClassOfIrreducibleFDRep (chosenFDRep chi)
    (chosenFDRep_irreducible chi)

/-- The chosen representative of `simpleModuleClassLabel chi` has trace
character `chi`. -/
theorem simpleModuleClassLabel_character (chi : Irr K G) :
    (simpleClassFDRep (simpleModuleClassLabel chi)).character = chi.1 := by
  calc
    (simpleClassFDRep (simpleModuleClassLabel chi)).character =
        (chosenFDRep chi).character :=
      FDRep.char_iso
        (simpleClassOfIrreducibleFDRepIso (chosenFDRep chi)
          (chosenFDRep_irreducible chi))
    _ = chi.1 := chosenFDRep_character chi

/-- The characters of the selected simple-module representatives separate
their simple-module classes. -/
theorem simpleModuleClass_character_injective :
    Function.Injective (fun X : SimpleModuleClass K[G] ↦
      (simpleClassFDRep X).character) :=
  ModularRep.SimpleTraceLinearIndependence.simpleModuleClass_character_linearIndependent.injective

/-- Distinct function-valued ordinary irreducible characters receive
distinct simple-module labels. -/
theorem simpleModuleClassLabel_injective :
    Function.Injective (simpleModuleClassLabel (K := K) (G := G)) := by
  intro chi psi hlabel
  apply OrdinaryIrreducibleCharacter.ext
  intro g
  have hcharacters := congrArg
    (fun X : SimpleModuleClass K[G] ↦
      (simpleClassFDRep X).character) hlabel
  rw [simpleModuleClassLabel_character,
    simpleModuleClassLabel_character] at hcharacters
  exact congrFun hcharacters g

end ModularRep.OrdinaryIrreducibleCharacter


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
