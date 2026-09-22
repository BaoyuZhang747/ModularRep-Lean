import ModularRep.PaperProofs.TypeBRegularLeviCharacterOrbit

/-!
# Transport of the regular-Levi action square to the original subgroups

The rational subgroup inside the paired geometric Levi and its image inside
the original ambient fixed group have different nested subtype presentations.
This file transports the constructed action and product map through their
actual group equivalences. It has no external source input: its square and
surjectivity premises are intermediate deductions supplied by the geometric
construction in the final construction.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBRegularLeviOrbitTransport

open TypeBRegularLeviCharacterActionAdapter

variable {G G' M M' I : Type} [Group G] [Group G'] [Group M] [Group M']
variable (eG : G ≃* G') (eM : M ≃* M')
variable (action : M →* MulAut G)

/-- The original conjugation action on the alternative literal subgroup
presentation, using the specified value-preserving carrier equivalences. -/
def actionOnOriginal : M' →* MulAut G' :=
  (MulAut.congr eG).toMonoidHom.comp (action.comp eM.symm.toMonoidHom)

@[simp] theorem actionOnOriginal_value (b : M') (x : G') :
    actionOnOriginal eG eM action b x = eG (action (eM.symm b) (eG.symm x)) := rfl

variable (Q D : I → Type) [∀ i, Group (Q i)] [∀ i, Group (D i)]
variable (decomposition : G ≃* ((i : I) → Q i))
variable (factorAut : ∀ i, D i →* MulAut (Q i))
variable (rho : M →* ((i : I) → D i))

/-- The same rational product identification, starting on the original
ambient subgroup presentation. -/
def decompositionOnOriginal : G' ≃* ((i : I) → Q i) :=
  eG.symm.trans decomposition

/-- The same product of actual action images, with the original acting
subgroup as its domain. -/
def productMapOnOriginal : M' →* ((i : I) → D i) :=
  rho.comp eM.symm.toMonoidHom

theorem productMapOnOriginal_surjective (h : Function.Surjective rho) :
    Function.Surjective (productMapOnOriginal eM D rho) :=
  h.comp eM.symm.surjective

/-- Changing the nested subtype presentations preserves the proved group
square. No new automorphism-coordinate identification is an input. -/
theorem groupSquareOnOriginal
    (square : ∀ b, MulAut.congr decomposition (action b) =
      coordinateMulAut Q D factorAut (rho b)) (b : M') :
    MulAut.congr (decompositionOnOriginal eG Q decomposition)
      (actionOnOriginal eG eM action b) =
      coordinateMulAut Q D factorAut (productMapOnOriginal eM D rho b) := by
  apply MulEquiv.ext
  intro x
  have h := congrArg (fun a : MulAut ((i : I) → Q i) ↦ a x) (square (eM.symm b))
  simpa [decompositionOnOriginal, actionOnOriginal, productMapOnOriginal,
    MulAut.congr] using h

end ModularRep.PaperProofs.TypeBRegularLeviOrbitTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
