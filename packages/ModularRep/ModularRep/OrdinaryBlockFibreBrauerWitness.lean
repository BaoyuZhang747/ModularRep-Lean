import ModularRep.OrdinaryBlockFibreCommonWitness
import ModularRep.IrreducibleBrauerCharacter

/-!
# A common ordinary character from a common Brauer character

The external inputs are nonzero decomposition columns,
the block support law, and preservation of nonzero decomposition numbers
under quotient inflation in one compatible modular system. These are the
standard statements in Navarro, Corollary (2.11) and its following paragraph,
Theorem (3.3), and equation (2) in the discussion preceding Theorem (7.6).

The predicates below must be bound to genuine nonzero decomposition numbers.
Arbitrary predicates and arbitrary root lifts do not instantiate these sources.
The kernel deduction constructs the first common ordinary-character witness
used by the manuscript, from its separately established Brauer pullback.
It assumes no common ordinary witness, block containment, block equality,
weight correspondence, or inductive condition.
-/

noncomputable section

namespace ModularRep.OrdinaryBlockFibreBrauerWitness

open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.OrdinaryBlockFibreCommonWitness

universe u v w

/-- The source support laws construct a common inflated ordinary character
for the two blocks containing a specified quotient/cover Brauer pair. -/
theorem commonInflatedOrdinaryCharacter_of_brauer_pullback
    {p : Nat} {k K CoverG QuotientG : Type u}
    {CoverBlock : Type v} {QuotientBlock : Type w}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group CoverG] [Group QuotientG] [Finite CoverG] [Finite QuotientG]
    (pi : CoverG →* QuotientG) (hpi : Function.Surjective pi)
    (iotaCover : PrimeRegularRootEmbedding p k K CoverG)
    (iotaQuotient : PrimeRegularRootEmbedding p k K QuotientG)
    (ordinaryCoverBlock : Irr K CoverG → CoverBlock)
    (ordinaryQuotientBlock : Irr K QuotientG → QuotientBlock)
    (brauerCoverBlock : IBr iotaCover → CoverBlock)
    (brauerQuotientBlock : IBr iotaQuotient → QuotientBlock)
    (supportCover : Irr K CoverG → IBr iotaCover → Prop)
    (supportQuotient : Irr K QuotientG → IBr iotaQuotient → Prop)
    (hcolumn : ∀ phi, ∃ chi, supportQuotient chi phi)
    (hcoverBlock : ∀ chi phi, supportCover chi phi →
      ordinaryCoverBlock chi = brauerCoverBlock phi)
    (hquotientBlock : ∀ chi phi, supportQuotient chi phi →
      ordinaryQuotientBlock chi = brauerQuotientBlock phi)
    (hinflation : ∀ (chi : Irr K QuotientG)
      (phi : IBr iotaQuotient) (psi : IBr iotaCover),
      (∀ g : PrimeRegularElement (G := CoverG) p,
        psi.1 g = phi.1 (PrimeRegularElement.map pi g)) →
      supportQuotient chi phi →
      supportCover (inflateAlong pi hpi chi) psi)
    (phiQuotient : IBr iotaQuotient) (phiCover : IBr iotaCover)
    (hphi : ∀ g : PrimeRegularElement (G := CoverG) p,
      phiCover.1 g = phiQuotient.1 (PrimeRegularElement.map pi g)) :
    CommonInflatedOrdinaryCharacter pi hpi
      ordinaryQuotientBlock ordinaryCoverBlock
      (brauerQuotientBlock phiQuotient) (brauerCoverBlock phiCover) := by
  obtain ⟨chi, hchi⟩ := hcolumn phiQuotient
  refine ⟨chi, hquotientBlock chi phiQuotient hchi, ?_⟩
  exact hcoverBlock (inflateAlong pi hpi chi) phiCover
    (hinflation chi phiQuotient phiCover hphi hchi)

end ModularRep.OrdinaryBlockFibreBrauerWitness


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
