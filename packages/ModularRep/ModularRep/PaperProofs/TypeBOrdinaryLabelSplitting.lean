import ModularRep.OrdinaryIrrSimpleModuleClass

/-!
# Literal ordinary labels over the prescribed characteristic-zero field

This Type B supplement uses the same chosen realization and finite-dimensional
representation as the shared ordinary-character label construction. It proves
the trace equation and forward label injectivity directly. No reverse trace
separation, ordinary orthogonality, basic set, or source certificate is used.

The ordinary field need not be algebraically closed. In particular these
declarations can be used with the fraction field of the actual modular system.
The splitting-field and root agreements required by a later published
rational-series input remain separate from this elementary label construction.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBOrdinaryLabelSplitting

open ModularRep OrdinaryIrreducibleCharacter FDRepSimpleClassKZero
open scoped MonoidAlgebra

universe u

variable {K G : Type u} [Field K] [CharZero K] [Group G] [Finite G]

/-- The shared choice of an actual irreducible realization of `chi`. -/
def realisation (chi : Irr K G) : Realisation K G chi.val :=
  OrdinaryIrreducibleCharacter.chosenRealisation chi

/-- The shared finite-dimensional representation of the same character. -/
def representation (chi : Irr K G) : FDRep K G :=
  OrdinaryIrreducibleCharacter.chosenFDRep chi

/-- Irreducibility is read from the actual realization, without the broader
ordinary-field context of the shared theorem. -/
theorem representation_irreducible (chi : Irr K G) :
    Representation.IsIrreducible (representation chi).ρ := by
  change Representation.IsIrreducible (realisation chi).representation
  exact (realisation chi).irreducible

/-- The trace function is the literal function carried by `chi`. -/
theorem representation_character (chi : Irr K G) :
    (representation chi).character = chi.val :=
  (realisation chi).character_eq

/-- The actual simple-module class of the shared chosen irreducible
representation. Proof irrelevance makes the irreducibility witness immaterial. -/
def ordinaryLabel (chi : Irr K G) : SimpleModuleClass K[G] :=
  simpleClassOfIrreducibleFDRep (representation chi)
    (representation_irreducible chi)

/-- The chosen representative of this actual simple class has trace `chi`.
Only the explicit representation isomorphism and trace invariance are used. -/
theorem ordinaryLabel_character (chi : Irr K G) :
    (simpleClassFDRep (ordinaryLabel chi)).character = chi.val := by
  calc
    (simpleClassFDRep (ordinaryLabel chi)).character =
        (representation chi).character :=
      FDRep.char_iso (simpleClassOfIrreducibleFDRepIso (representation chi)
        (representation_irreducible chi))
    _ = chi.val := representation_character chi

/-- Equal simple labels force equality of the original character functions.
This is the forward direction; character separation of arbitrary simple
representatives is not an input or a dependency. -/
theorem ordinaryLabel_injective :
    Function.Injective (ordinaryLabel (K := K) (G := G)) := by
  intro chi psi labels
  apply Subtype.ext
  have characters := congrArg
    (fun X : SimpleModuleClass K[G] => (simpleClassFDRep X).character) labels
  rw [ordinaryLabel_character, ordinaryLabel_character] at characters
  exact characters

/-- The literal selected subset of the same function-valued ordinary
irreducible characters. A later source supplies the meaning of `series`. -/
def OrdinarySeriesCarrier (series : Irr K G → Prop) :=
  {chi : Irr K G // series chi}

/-- The actual ordinary label on this selected series carrier. -/
def ordinarySeriesLabel (series : Irr K G → Prop) :
    OrdinarySeriesCarrier series → SimpleModuleClass K[G] :=
  fun chi => ordinaryLabel chi.val

@[simp]
theorem ordinarySeriesLabel_apply (series : Irr K G → Prop)
    (chi : OrdinarySeriesCarrier series) :
    ordinarySeriesLabel series chi = ordinaryLabel chi.val :=
  rfl

/-- The series label retains the exact underlying ordinary trace function. -/
theorem ordinarySeriesLabel_character (series : Irr K G → Prop)
    (chi : OrdinarySeriesCarrier series) :
    (simpleClassFDRep (ordinarySeriesLabel series chi)).character = chi.val.val :=
  ordinaryLabel_character chi.val

/-- Forward label injectivity on the actual selected ordinary carrier. -/
theorem ordinarySeriesLabel_injective (series : Irr K G → Prop) :
    Function.Injective (ordinarySeriesLabel series) := by
  intro chi psi labels
  apply Subtype.ext
  exact ordinaryLabel_injective labels

end ModularRep.PaperProofs.TypeBOrdinaryLabelSplitting

/- Audit-only output: the root executor checks the actual imported and new
arities while running the focused native check. These commands add no axioms. -/
#check @ModularRep.OrdinaryIrreducibleCharacter.chosenRealisation
#check @ModularRep.OrdinaryIrreducibleCharacter.chosenFDRep
#check @ModularRep.FDRepSimpleClassKZero.simpleClassOfIrreducibleFDRep
#check @ModularRep.FDRepSimpleClassKZero.simpleClassOfIrreducibleFDRepIso
#check @ModularRep.PaperProofs.TypeBOrdinaryLabelSplitting.ordinaryLabel
#check @ModularRep.PaperProofs.TypeBOrdinaryLabelSplitting.ordinaryLabel_character
#check @ModularRep.PaperProofs.TypeBOrdinaryLabelSplitting.ordinaryLabel_injective
#check @ModularRep.PaperProofs.TypeBOrdinaryLabelSplitting.ordinarySeriesLabel_injective


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
