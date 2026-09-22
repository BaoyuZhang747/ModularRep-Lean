import ModularRep.CentralCharacterDecomposition
import ModularRep.PrimitiveCentralIdempotent

/-!
# Central character sectors of primitive central idempotents

A block idempotent of a finite group algebra is a primitive central
idempotent.  This file proves that every such idempotent has a unique sector
with respect to the central character idempotents.  It also shows that an
irreducible module on which the block idempotent acts as the identity has the
central character indexing that sector.
-/

open scoped MonoidAlgebra

namespace ModularRep

variable {k G : Type*} [Field k] [Group G]

/-- The assertion that `nu` is the central character sector of the
idempotent `b`.  Thus `b * e_nu = b`, while `b * e_mu = 0` for every
`mu ≠ nu`. -/
def IsCentralCharacterSector (Z : Subgroup G) [Fintype Z]
    [Invertible (Fintype.card Z : k)] (b : k[G]) (nu : Z →* kˣ) : Prop :=
  IsPrimitiveCentralIdempotent.IsSupport b
    (fun mu : Z →* kˣ ↦ centralCharacterIdempotent Z mu) nu

namespace IsCentralCharacterSector

theorem mul_eq_self {Z : Subgroup G} [Fintype Z]
    [Invertible (Fintype.card Z : k)] {b : k[G]} {nu : Z →* kˣ}
    (h : IsCentralCharacterSector Z b nu) :
    b * centralCharacterIdempotent Z nu = b :=
  h.1

theorem mul_eq_zero_of_ne {Z : Subgroup G} [Fintype Z]
    [Invertible (Fintype.card Z : k)] {b : k[G]} {nu mu : Z →* kˣ}
    (h : IsCentralCharacterSector Z b nu) (hmu : mu ≠ nu) :
    b * centralCharacterIdempotent Z mu = 0 :=
  h.2 mu hmu

end IsCentralCharacterSector

namespace IsPrimitiveCentralIdempotent

/-- A primitive central idempotent in a group algebra belongs to a unique
central character sector.  The finite enumeration of the character group is
kept out of the public statement. -/
theorem existsUnique_centralCharacterSector
    {b : k[G]} (hb : IsPrimitiveCentralIdempotent b)
    (Z : Subgroup G) [Fintype Z] (hZ : Z ≤ Subgroup.center G)
    [IsAlgClosed k] [Invertible (Fintype.card Z : k)] :
    ∃! nu : Z →* kˣ, IsCentralCharacterSector Z b nu := by
  let _ : Fintype (Z →* kˣ) :=
    centralSubgroupLinearCharacterFintypeOfIsAlgClosed
      (k := k) (G := G) Z hZ
  let E : CompleteOrthogonalCentralIdempotents
      (fun nu : Z →* kˣ ↦ centralCharacterIdempotent Z nu) :=
    completeCentralCharacterIdempotentsOfIsAlgClosed
      (k := k) (G := G) Z hZ
  exact hb.existsUnique_isSupport E

/-- The unique central character indexing the sector of a primitive central
idempotent. -/
noncomputable def centralCharacterSector
    {b : k[G]} (hb : IsPrimitiveCentralIdempotent b)
    (Z : Subgroup G) [Fintype Z] (hZ : Z ≤ Subgroup.center G)
    [IsAlgClosed k] [Invertible (Fintype.card Z : k)] : Z →* kˣ :=
  Classical.choose (hb.existsUnique_centralCharacterSector Z hZ).exists

theorem centralCharacterSector_isSector
    {b : k[G]} (hb : IsPrimitiveCentralIdempotent b)
    (Z : Subgroup G) [Fintype Z] (hZ : Z ≤ Subgroup.center G)
    [IsAlgClosed k] [Invertible (Fintype.card Z : k)] :
    IsCentralCharacterSector Z b (hb.centralCharacterSector Z hZ) :=
  Classical.choose_spec (hb.existsUnique_centralCharacterSector Z hZ).exists

@[simp]
theorem mul_centralCharacterSector
    {b : k[G]} (hb : IsPrimitiveCentralIdempotent b)
    (Z : Subgroup G) [Fintype Z] (hZ : Z ≤ Subgroup.center G)
    [IsAlgClosed k] [Invertible (Fintype.card Z : k)] :
    b * centralCharacterIdempotent Z (hb.centralCharacterSector Z hZ) = b :=
  (hb.centralCharacterSector_isSector Z hZ).mul_eq_self

theorem mul_centralCharacterIdempotent_eq_zero_of_ne_sector
    {b : k[G]} (hb : IsPrimitiveCentralIdempotent b)
    (Z : Subgroup G) [Fintype Z] (hZ : Z ≤ Subgroup.center G)
    [IsAlgClosed k] [Invertible (Fintype.card Z : k)]
    {mu : Z →* kˣ} (hmu : mu ≠ hb.centralCharacterSector Z hZ) :
    b * centralCharacterIdempotent Z mu = 0 :=
  (hb.centralCharacterSector_isSector Z hZ).mul_eq_zero_of_ne hmu

theorem centralCharacterSector_unique
    {b : k[G]} (hb : IsPrimitiveCentralIdempotent b)
    (Z : Subgroup G) [Fintype Z] (hZ : Z ≤ Subgroup.center G)
    [IsAlgClosed k] [Invertible (Fintype.card Z : k)]
    {nu : Z →* kˣ} (hnu : IsCentralCharacterSector Z b nu) :
    nu = hb.centralCharacterSector Z hZ :=
  (hb.existsUnique_centralCharacterSector Z hZ).unique hnu
    (hb.centralCharacterSector_isSector Z hZ)

end IsPrimitiveCentralIdempotent

end ModularRep

namespace Representation

open ModularRep

variable {k G V : Type*} [Field k] [Group G]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable [IsAlgClosed k]

/-- If `b` acts as the identity on an irreducible representation and `nu`
is the central character sector of `b`, then `nu` is the central character
of the representation. -/
theorem centralCharacter_eq_of_isCentralCharacterSector
    (rho : Representation k G V) [rho.IsIrreducible]
    (Z : Subgroup G) [Fintype Z] [Invertible (Fintype.card Z : k)]
    (hZ : Z ≤ Subgroup.center G) {b : k[G]} {nu : Z →* kˣ}
    (hsector : IsCentralCharacterSector Z b nu)
    (hbV : ∀ v : rho.asModule, b • v = v) :
    nu = rho.centralCharacter Z hZ := by
  let _ : Fintype (Z →* kˣ) :=
    centralSubgroupLinearCharacterFintypeOfIsAlgClosed
      (k := k) (G := G) Z hZ
  let E : CompleteOrthogonalCentralIdempotents
      (fun mu : Z →* kˣ ↦ centralCharacterIdempotent Z mu) :=
    completeCentralCharacterIdempotentsOfIsAlgClosed
      (k := k) (G := G) Z hZ
  exact (E.existsUnique_isSupport (V := rho.asModule)).unique
    (IsPrimitiveCentralIdempotent.IsSupport.toModuleSupport hsector hbV)
    (rho.centralCharacterIdempotent_isSupport Z hZ)

/-- An irreducible representation on which a primitive central idempotent
acts as the identity has the central character indexing the idempotent's
unique sector. -/
theorem primitiveCentralIdempotentSector_eq_centralCharacter
    (rho : Representation k G V) [rho.IsIrreducible]
    (Z : Subgroup G) [Fintype Z] [Invertible (Fintype.card Z : k)]
    (hZ : Z ≤ Subgroup.center G) {b : k[G]}
    (hb : IsPrimitiveCentralIdempotent b)
    (hbV : ∀ v : rho.asModule, b • v = v) :
    hb.centralCharacterSector Z hZ = rho.centralCharacter Z hZ :=
  rho.centralCharacter_eq_of_isCentralCharacterSector Z hZ
    (hb.centralCharacterSector_isSector Z hZ) hbV

end Representation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
