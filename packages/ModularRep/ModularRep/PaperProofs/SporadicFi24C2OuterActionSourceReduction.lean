import ModularRep.PaperProofs.SporadicFi24ThreeBlockAutomorphismPromotionActual
import ModularRep.PaperProofs.CyclicOuterLemma37Concrete

/-!
# Structural reduction of the Fischer outer-action source

This experimental module replaces the two operational carrier-fixation
fields of `C2OuterActionSource` by the structural identification of the
kernel of the outer-class map with the inner automorphisms.  Inner
automorphisms fix function-valued irreducible Brauer characters and ambient
conjugacy classes of character weights by the existing literal-carrier
theorems, so both carrier-fixation fields are kernel deductions.

The ordered three-field binding is an explicit E1/U source boundary.  It is
generic in `X`: its fields record a chosen two-point class map, the selected
class's nontriviality, and the literal inner-automorphism kernel for the
intended concrete Fischer instantiation.  The record is not itself a proof
that `Out(Fi'_24)` is isomorphic to `C2`.  The constructor is K relative to
that source.  No character--weight map, fibre equivalence, raw sector family,
orbit census, additional output/block-preservation equality, An--Dietrich
input, Spath input, Proposition 5.7 conclusion, BAW-goodness, or iBAW
conclusion is accepted or proved here.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24C2OuterActionSourceReduction

open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual
open ModularRep.PaperProofs.SporadicFi24ThreeBlockAutomorphismPromotionActual

universe u

variable {k K X : Type u}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

/-- Generic structural E1/U binding intended for the selected Fischer outer
class.  It does not prove the concrete outer-group identification.  The
carrier-specific fixation properties are deliberately absent: they follow
in K from `kernel_eq_inner`. -/
structure Fi24C2OuterQuotientBinding
    (S : Fi24ThreeBlockSource (k := k) (X := X)) where
  outerClass : (MulAut X)ᵐᵒᵖ →* Equiv.Perm (Fin 2)
  selectedOuter_nontrivial : outerClass S.outer ≠ 1
  kernel_eq_inner : outerClass.ker =
    (RepresentationWeight.innerInverseOpHom (G := X)).range

/-- Construct the operational outer-action source from the three structural
quotient fields.  Both literal-carrier fixation clauses are consequences of
the standard inner-fixation theorems, rather than source premises. -/
def c2OuterActionSource_ofQuotientBinding
    (iota : PrimeRegularRootEmbedding 3 k K X)
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (B : Fi24C2OuterQuotientBinding S) :
    C2OuterActionSource iota S where
  outerClass := B.outerClass
  selectedOuter_nontrivial := B.selectedOuter_nontrivial
  kernel_fixes_brauer := by
    intro alpha hclass phi
    have hmem : alpha ∈ B.outerClass.ker := hclass
    rw [B.kernel_eq_inner] at hmem
    rcases hmem with ⟨x, hx⟩
    rw [← hx]
    change IrreducibleBrauerCharacter.twist iota phi
      (MulAut.conj x⁻¹) = phi
    exact inner_fixes_ibr iota x phi
  kernel_fixes_weight := by
    intro alpha hclass weight
    have hmem : alpha ∈ B.outerClass.ker := hclass
    rw [B.kernel_eq_inner] at hmem
    rcases hmem with ⟨x, hx⟩
    rw [← hx]
    change CharacterWeight.rightTwistConjugacyClass
      (p := 3) (K := K) (G := X) (MulAut.conj x⁻¹) weight = weight
    exact inner_fixes_weightClass x weight

end ModularRep.PaperProofs.SporadicFi24C2OuterActionSourceReduction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
