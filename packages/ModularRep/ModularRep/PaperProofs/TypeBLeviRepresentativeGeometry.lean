import ModularRep.PaperProofs.TypeBLeviRepresentativeCarriers
import ModularRep.PaperProofs.TypeBRegularLeviOrbitAssembly
import ModularRep.PaperProofs.TypeBRegularLeviCliffordBinding

/-!
# The representative construction's original primal component maps

This supporting module instantiates the accepted regular-Levi component and
Lang-supported action machinery on the SAME actual primal Lbar and original
rational subgroup copies. Product-image surjectivity and the conjugation
square are derived, not fields of a new representative source packet.

The lower source boundary is the actual component/Frobenius presentation,
the geometric decomposition of the same paired Levi into its derived group
and centre, and the central Lang consequence on that same group and F.
Authentic algebraic realization remains explicit E1/E2/U. No dual Levi or
identification of arbitrary regular embeddings with Clifford is made.
The reused CliffordBinding module contains generic point-subgroup maps here;
none of its concrete special-Clifford specialization is invoked.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBLeviRepresentativeGeometry

open TypeBRegularLeviRationalCarriers TypeBRegularLeviComponentPointSource
open TypeBLeviRepresentativeCarriers

variable {A : Type} [Group A]
variable (Frob : MulAut A) (Lbar : Subgroup A)
variable (levi_stable : Lbar.map Frob.toMonoidHom = Lbar)

abbrev pairedFrobenius :=
  TypeBRegularLeviCliffordBinding.frobeniusB Frob Lbar levi_stable

abbrev derivedInside := TypeBRegularLeviCliffordBinding.H Lbar

theorem derived_stable :
    ∀ h ∈ derivedInside Lbar,
      pairedFrobenius Frob Lbar levi_stable h ∈ derivedInside Lbar :=
  TypeBRegularLeviCliffordBinding.geometricH_stable Frob Lbar levi_stable

variable {I : Type} (m : I → ℕ)
variable (components : ComponentPointData (pairedFrobenius Frob Lbar levi_stable)
  (derivedInside Lbar) (derived_stable Frob Lbar levi_stable) m)

/-- These are the original components' actual return-fixed subgroups. -/
abbrev factor (i : I) :=
  rationalFactor (pairedFrobenius Frob Lbar levi_stable) (derivedInside Lbar)
    (derived_stable Frob Lbar levi_stable) m components i

/-- The canonical map from derived fixed points to their copy inside Gamma. -/
def rationalDerivedEquiv :
    rationalSubgroup (pairedFrobenius Frob Lbar levi_stable) (derivedInside Lbar) ≃*
      TypeBLeviRepresentativeCarriers.N Frob Lbar :=
  (TypeBRegularLeviCliffordBinding.rationalHEquivL0 Frob Lbar levi_stable).trans
    (originalL0Equiv Frob Lbar)

/-- The literal original N has the computed product of return-fixed factors. -/
def componentProduct :
    TypeBLeviRepresentativeCarriers.N Frob Lbar ≃*
      ((i : I) → factor Frob Lbar levi_stable m components i) :=
  TypeBRegularLeviOrbitAssembly.originalProduct
    (pairedFrobenius Frob Lbar levi_stable) (derivedInside Lbar)
    (derived_stable Frob Lbar levi_stable) m components
    (rationalDerivedEquiv Frob Lbar levi_stable)

variable (central : ∀ b : pairedLevi Lbar,
  ∃ h : derivedInside Lbar, ∃ z : Subgroup.center (pairedLevi Lbar),
    b = (h : pairedLevi Lbar) * z)

/-- The actual image of conjugation on this original rational factor. -/
abbrev factorImage (i : I) :=
  TypeBRegularLeviOrbitAssembly.imageGroup
    (pairedFrobenius Frob Lbar levi_stable) (derivedInside Lbar)
    (derived_stable Frob Lbar levi_stable) m components central i

def factorImageAction (i : I) :
    factorImage Frob Lbar levi_stable m components central i →*
      MulAut (factor Frob Lbar levi_stable m components i) :=
  TypeBRegularLeviOrbitAssembly.imageAction
    (pairedFrobenius Frob Lbar levi_stable) (derivedInside Lbar)
    (derived_stable Frob Lbar levi_stable) m components central i

/-- The same map from the original Gamma into its actual factor images. -/
def imageProduct : Gamma Frob Lbar →*
    ((i : I) → factorImage Frob Lbar levi_stable m components central i) :=
  TypeBRegularLeviOrbitAssembly.originalImageProduct
    (pairedFrobenius Frob Lbar levi_stable) (derivedInside Lbar)
    (derived_stable Frob Lbar levi_stable) m components central
    (TypeBRegularLeviCliffordBinding.fixedBEquivM Frob Lbar levi_stable)

/-- Reuse of the actual supported-Lang surjectivity deduction. -/
theorem imageProduct_surjective [Finite I]
    (lang : TypeBRegularLeviSupportedLift.CentralLangSource
      (pairedFrobenius Frob Lbar levi_stable)) :
    Function.Surjective (imageProduct Frob Lbar levi_stable m components central) :=
  TypeBRegularLeviOrbitAssembly.originalImageProduct_surjective
    (pairedFrobenius Frob Lbar levi_stable) (derivedInside Lbar)
    (derived_stable Frob Lbar levi_stable) m components central
    (TypeBRegularLeviCliffordBinding.fixedBEquivM Frob Lbar levi_stable) lang

/-- The transported action is definitionally the original conjugation action. -/
theorem originalAction_eq_conjugation :
    TypeBRegularLeviOrbitAssembly.originalAction
      (pairedFrobenius Frob Lbar levi_stable) (derivedInside Lbar) central
      (rationalDerivedEquiv Frob Lbar levi_stable)
      (TypeBRegularLeviCliffordBinding.fixedBEquivM Frob Lbar levi_stable) =
      (MulAut.conjNormal : Gamma Frob Lbar →*
        MulAut (TypeBLeviRepresentativeCarriers.N Frob Lbar)) := by
  ext g x
  rfl

/-- The literal group square needed by the original-character transport. -/
theorem groupSquare (g : Gamma Frob Lbar) :
    MulAut.congr (componentProduct Frob Lbar levi_stable m components)
      (MulAut.conjNormal g) =
      TypeBRegularLeviCharacterActionAdapter.coordinateMulAut
        (factor Frob Lbar levi_stable m components)
        (fun i ↦ factorImage Frob Lbar levi_stable m components central i)
        (factorImageAction Frob Lbar levi_stable m components central)
        (imageProduct Frob Lbar levi_stable m components central g) := by
  have square := TypeBRegularLeviOrbitAssembly.original_groupSquare
    (pairedFrobenius Frob Lbar levi_stable) (derivedInside Lbar)
    (derived_stable Frob Lbar levi_stable) m components central
    (rationalDerivedEquiv Frob Lbar levi_stable)
    (TypeBRegularLeviCliffordBinding.fixedBEquivM Frob Lbar levi_stable) g
  rw [originalAction_eq_conjugation Frob Lbar levi_stable central] at square
  exact square

section Finiteness

variable [Finite (fixedPoints Frob.toMonoidHom)]

local instance pairedFinite : Finite (fixedPoints (pairedFrobenius Frob Lbar levi_stable)) :=
  Finite.of_equiv (Gamma Frob Lbar)
    (TypeBRegularLeviCliffordBinding.fixedBEquivM Frob Lbar levi_stable).symm.toEquiv

instance factorFinite (i : I) : Finite (factor Frob Lbar levi_stable m components i) :=
  TypeBRegularLeviOrbitAssembly.rationalFactor_finite
    (pairedFrobenius Frob Lbar levi_stable) (derivedInside Lbar)
    (derived_stable Frob Lbar levi_stable) m components i

end Finiteness

end ModularRep.PaperProofs.TypeBLeviRepresentativeGeometry


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
