import ModularRep.PaperProofs.TypeBSpinHallJGInstantiation
import ModularRep.PaperProofs.TypeBSpinCoverSource

/-!
# Structural criterion data from the actual Spin cover

Only three natural automorphism facts remain at the source boundary.
They concern the literal conjugation/Frobenius map and the actual outer
automorphism quotient. FLZ Section 3.5, p. 546 (citing GLS Number 3,
Theorem 2.5.1) gives this automorphism description. No character, block,
extension, matching or all-blocks hypothesis is supplied here.

The finite derived equality follows from perfectness of the same cover;
the cyclic SC/Spin quotient follows from the actual norm. The centralizer
identity then follows from the checked kernel-centralizer equality.
Malle--Testerman Theorem 24.17, Table 24.2 and Remark 24.19/Table 24.3,
pp. 211--214, supply the generic cover scope, excluding (n,q) = (3,3).
The existing generic-cover packet and its fixed quotient map are reused.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBSpinStructuralCoverBinding

open TypeBCliffordCarriers TypeBSpinCoverSource

/-- The published natural automorphism facts on their literal carriers.
The finite defining field, odd-field parameters and rank are explicit
constructor indices. The outer quotient is Aut(Spin)/Inn(Spin), not an
arbitrarily chosen abelian action group. -/
structure NaturalAutomorphismFacts {n p f : ℕ} {F : Type}
    [Field F] [Finite F] [CharP F p]
    (N : NormSource n F) {parameters : OddFieldParameters F p f}
    (fs : FieldActionSource n F p f parameters N) (rank : 3 ≤ n) : Prop where
  kernel : (TypeBAutomorphismSource.ambientAutomorphism fs).ker =
    TypeBAutomorphismSource.embeddedCenter fs
  surjective : Function.Surjective (TypeBAutomorphismSource.ambientAutomorphism fs)
  outer_abelian : IsMulCommutative (TypeBAutomorphismSource.OuterAutomorphism N)

variable {n p f ell : ℕ} {F : Type}
  [Field F] [Finite F] [CharP F p]
  (N : NormSource n F) {parameters : OddFieldParameters F p f}
  (fs : FieldActionSource n F p f parameters N)
  [Finite (Spin n F N)]

/-- Construct the old structural source with no independent perfectness
or cyclic-quotient input. Both refer to the same norm kernel. -/
def structuralSource
    (cover : GenericSpinCoverSource (p := p) (f := f) (ell := ell) N)
    (facts : NaturalAutomorphismFacts N fs cover.rank) :
    TypeBAutomorphismSource.StructuralSource fs where
  rank := cover.rank
  spin_perfect := cover.perfect
  kernel := facts.kernel
  surjective := facts.surjective
  quotient_cyclic := TypeBSpinHallJGInstantiation.normQuotient_cyclic N
  outer_abelian := facts.outer_abelian

/-- The actual structural clause used by the full criterion. All seven
fields are bound to the existing natural action on the literal subgroup. -/
theorem structural
    (cover : GenericSpinCoverSource (p := p) (f := f) (ell := ell) N)
    (facts : NaturalAutomorphismFacts N fs cover.rank) :
    TypeBCriterionHypotheses.Structural (SpinSubgroup n F N) fs.action
      (TypeBCriterionCarrierBindings.naturalAction N fs) where
  derived := TypeBAutomorphismSource.derived_eq_spin N cover.perfect
  acting_abelian := inferInstance
  quotient_cyclic := TypeBSpinHallJGInstantiation.normQuotient_cyclic N
  centralizer := TypeBAutomorphismSource.centralizer_eq_embeddedCenter fs
    (structuralSource N fs cover facts)
  natural_kernel := facts.kernel
  natural_surjective := facts.surjective
  outer_abelian := facts.outer_abelian

local instance spinFintype : Fintype (Spin n F N) := Fintype.ofFinite _

/-- The same generic Spin packet supplies the actual maximal perfect
prime-to-ell cover, with its literal quotient by the Spin centre. -/
def ellPrimeCover (hEll : Nat.Prime ell) (hOdd : Odd ell)
    (cover : GenericSpinCoverSource (p := p) (f := f) (ell := ell) N) :
    EvenFieldFLZSourceConditions.EllPrimeCoverSource ell (Spin n F N) :=
  genericSpinEllPrimeCover N hEll hOdd cover

end ModularRep.PaperProofs.TypeBSpinStructuralCoverBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
