import ModularRep.LinearCharacterCompleteness
import ModularRep.CentralCharacterAction
import ModularRep.RepresentationCentralSupport

/-!
# Decomposition by central characters

This file combines the character orthogonality, completeness, and action
results.  Over an algebraically closed coefficient field in which the order
of a finite central subgroup is invertible, the idempotents indexed by all
linear characters form a complete orthogonal central family.  The support of
an irreducible representation in this family is its central character.
-/

namespace ModularRep

open scoped MonoidAlgebra

/-- The central character idempotents form a complete orthogonal central
family over an algebraically closed field in which the order of the central
subgroup is invertible.

The `Fintype` structure on the character group is the one constructed from
finite abelian duality in `centralSubgroupLinearCharacterFintypeOfIsAlgClosed`.
-/
theorem completeCentralCharacterIdempotentsOfIsAlgClosed
    {k G : Type*} [Field k] [Group G] (Z : Subgroup G) [Fintype Z]
    (hZ : Z ≤ Subgroup.center G) [IsAlgClosed k]
    [Invertible (Fintype.card Z : k)] :
    letI : Fintype (Z →* kˣ) :=
      centralSubgroupLinearCharacterFintypeOfIsAlgClosed Z hZ
    CompleteOrthogonalCentralIdempotents
      (fun nu : Z →* kˣ ↦ centralCharacterIdempotent Z nu) := by
  let _ : Fintype (Z →* kˣ) :=
    centralSubgroupLinearCharacterFintypeOfIsAlgClosed Z hZ
  let _ : HasEnoughRootsOfUnity k (Monoid.exponent Z) :=
    hasEnoughRootsOfUnity_of_isAlgClosed_card_invertible
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact centralCharacterIdempotent_isIdempotentElem Z
  · intro nu mu hne
    exact centralCharacterIdempotent_mul_eq_zero Z nu mu hne
  · exact sum_centralCharacterIdempotent_eq_one Z hZ
  · intro nu
    exact centralCharacterIdempotent_mem_center Z nu hZ

end ModularRep

namespace Representation

open ModularRep

variable {k G V : Type*} [Field k] [Group G]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable [IsAlgClosed k]

/-- The support of an irreducible representation under the complete family
of central character idempotents is its central character. -/
theorem centralIdempotentSupport_eq_centralCharacter
    (rho : Representation k G V) [rho.IsIrreducible]
    (Z : Subgroup G) [Fintype Z] [Invertible (Fintype.card Z : k)]
    (hZ : Z ≤ Subgroup.center G) :
    letI : Fintype (Z →* kˣ) :=
      centralSubgroupLinearCharacterFintypeOfIsAlgClosed Z hZ
    rho.centralIdempotentSupport
        (completeCentralCharacterIdempotentsOfIsAlgClosed Z hZ) =
      rho.centralCharacter Z hZ := by
  let _ : Fintype (Z →* kˣ) :=
    centralSubgroupLinearCharacterFintypeOfIsAlgClosed Z hZ
  let E : CompleteOrthogonalCentralIdempotents
      (fun nu : Z →* kˣ ↦ centralCharacterIdempotent Z nu) :=
    completeCentralCharacterIdempotentsOfIsAlgClosed (k := k) (G := G) Z hZ
  symm
  exact E.support_unique (V := rho.asModule)
    (rho.centralCharacterIdempotent_isSupport Z hZ)

end Representation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
