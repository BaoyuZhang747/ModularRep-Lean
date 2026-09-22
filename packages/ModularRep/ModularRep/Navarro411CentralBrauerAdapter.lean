import ModularRep.Navarro411CentralBrauerSource

/-!
# Kernel consequences of the Navarro (4.11) source

Every theorem here is a kernel deduction relative to the explicit E1 source
record and separately supplied p-group evidence for each nominated subgroup.
-/

namespace ModularRep

open scoped MonoidAlgebra

variable {p : Nat} {k G Block : Type*}
variable [Field k] [CharP k p] [IsAlgClosed k]
variable [Group G] [Fintype G] [Fintype Block] [Fact p.Prime]
variable {blockIdempotent : Block → k[G]}
variable {blocks : BlockIdempotentDecomposition blockIdempotent}
variable {B : Block} {D E : Subgroup G}

/-- The nominated subgroup lies in the nonzero support, relative to Navarro
(4.11) and its separately supplied p-group evidence. -/
theorem Navarro411CentralBrauerSource.nonzero_at_D
    (hD : IsPGroup p D)
    (S : Navarro411CentralBrauerSource blocks B D) :
    HasNonzeroCentralBrauerRestriction blocks B D :=
  (S.nonzero_iff_isSubconjugate D hD).mpr
    (Subgroup.IsSubconjugate.refl D)

/-- Navarro (4.11) makes the nominated p-subgroup maximal by literal
inclusion in the nonzero central Brauer support. -/
theorem Navarro411CentralBrauerSource.to_maximalCentralBrauerDefect
    (hD : IsPGroup p D)
    (S : Navarro411CentralBrauerSource blocks B D) :
    IsMaximalCentralBrauerDefect (p := p) blocks B D :=
  IsMaximalNonzeroPSubgroup.of_nonzero_iff_isSubconjugate hD
    S.nonzero_iff_isSubconjugate

/-- Two separately nominated p-subgroups satisfying Navarro (4.11) for the
same literal block are conjugate. -/
theorem Navarro411CentralBrauerSource.areConjugate
    (hD : IsPGroup p D) (hE : IsPGroup p E)
    (sD : Navarro411CentralBrauerSource blocks B D)
    (sE : Navarro411CentralBrauerSource blocks B E) :
    D.AreConjugate E := by
  apply Subgroup.IsSubconjugate.areConjugate_of_mutual
  · exact (sE.nonzero_iff_isSubconjugate D hD).mp
      (sD.nonzero_at_D hD)
  · exact (sD.nonzero_iff_isSubconjugate E hE).mp
      (sE.nonzero_at_D hE)

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
