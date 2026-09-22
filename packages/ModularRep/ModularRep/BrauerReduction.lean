import ModularRep.IrreducibleBrauerCharacter
import ModularRep.NormalizerQuotient
import ModularRep.OrdinaryIrreducibleCharacter

/-!
# Brauer reduction of an inflated local character

This file gives the literal function equality saying that an irreducible
Brauer character of `N_G(Q)` is the reduction of the ordinary inflation of a
character of `N_G(Q) / Q`.  It contains no block assignment or induction
statement.
-/

noncomputable section

namespace ModularRep.CharacterWeight

universe u

variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Finite G]

/-- `phiN` is the restriction to the `p`-regular elements of the ordinary
inflation of `chi` from `N_G(Q) / Q` to `N_G(Q)`.

The quotient kernel is `Q` regarded as a normal subgroup of its normaliser.
The definition is only a pointwise character equality.  In particular, it
contains no assertion about the block of either character. -/
def NormalizerInflatedReduction
    (Q : Subgroup G)
    (chi : OrdinaryIrreducibleCharacter.Irr K (NormalizerQuotient Q))
    (iotaN : PrimeRegularRootEmbedding p k K
      (Subgroup.normalizer (Q : Set G)))
    (phiN : IBr iotaN) : Prop :=
  ∀ g : PrimeRegularElement
      (G := Subgroup.normalizer (Q : Set G)) p,
    chi (QuotientGroup.mk'
      (Q.subgroupOf (Subgroup.normalizer (Q : Set G))) g.1) =
        phiN.1 g

end ModularRep.CharacterWeight


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
