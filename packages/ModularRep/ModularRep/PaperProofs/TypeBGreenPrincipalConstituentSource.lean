import ModularRep.NavarroCoveringBrauerExtension
import ModularRep.PaperProofs.TypeBCentralKernelBlockSource
import ModularRep.PaperProofs.TypeBCentralKernelInertia
import Mathlib.GroupTheory.PGroup

/-!
# Green's theorem and principal constituents on literal normal subgroups

The four E1/U interfaces are separate one-way readings of Navarro (1998):
Clifford restriction (8.5)/(8.7), Green (8.11), principal restriction via
(9.2), and principal lifting via (9.2)/(9.6) for a p-group quotient.
Characters are the actual root-valued irreducible Brauer characters;
occurrence is the existing nonnegative restriction expansion. Principal
support uses actual primitive idempotents and affording simple modules.

The source's coefficient field scope, subgroup-root agreement and quotient
hypothesis remain explicit. These interfaces assert no orbit equivalence,
weight correspondence, selected-pair triple or inductive condition.
Their literal modular-system/K-valued realization remains an obligation.
The chosen character and all uniqueness deductions below are kernel proofs.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBGreenPrincipalConstituentSource

open ModularRep NavarroCoveringBrauerExtension
open TypeBCentralKernelBlockSource TypeBCentralKernelInertia

universe u

variable {p : ℕ} {k K A : Type u}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
  [Group A] [Finite A] (N : Subgroup A) [N.Normal]
  (rootA : PrimeRegularRootEmbedding p k K A)
  (rootN : PrimeRegularRootEmbedding p k K N)

/-- Equality only on roots required by the literal subgroup, not equality
of the zero-extended root-lift functions on the whole coefficient field. -/
def RootAgreement : Prop :=
  ∀ z : rootsOfUnity (primeRegularExponent p N) k,
    rootN.lift (((z : kˣ) : k)) = rootA.lift (((z : kˣ) : k))

/-- The displayed root guard authenticates representation restriction
on the actual subgroup inclusion, by the existing eigenvalue theorem. -/
theorem restriction_brauerCharacter
    (roots : RootAgreement N rootA rootN) (V : FDRep k A) :
    Representation.brauerCharacterOfRootEmbedding
        (Representation.pullback V.ρ N.subtype) rootN =
      PrimeRegularClassFunction.pullback N.subtype
        (Representation.brauerCharacterOfRootEmbedding V.ρ rootA) :=
  Representation.brauerCharacterOfRootEmbedding_pullback_of_compatible
    V.ρ rootA rootN N.subtype
    (Representation.brauerRootLiftCompatibleAlong_of_eq_on_source_roots
      V.ρ rootA rootN N.subtype roots)

/-- Navarro (8.11), p.162: existence and uniqueness above one actual
constituent. The distinct-conjugate restriction formula is not needed as
an additional field; conjugacy below has its own narrower Clifford source. -/
structure Green811Source
    (roots : RootAgreement N rootA rootN)
    (fieldScope : SpathCoefficientField p k rootA.prime)
    (quotientPGroup : IsPGroup p (A ⧸ N)) : Prop where
  exists_above : ∀ theta : IBr rootN, ∃ Phi : IBr rootA,
    BrauerOccursInRestriction N rootA rootN Phi theta
  unique_above : ∀ (theta : IBr rootN) (Phi Psi : IBr rootA),
    BrauerOccursInRestriction N rootA rootN Phi theta →
    BrauerOccursInRestriction N rootA rootN Psi theta → Phi = Psi

/-- Navarro (8.5)/(8.7), pp.157--159: a restriction has constituents
and any two are actual ambient conjugates. This does not require a
p-group quotient. The action is the repository's fixed opposite convention. -/
structure Clifford85_87Source
    (roots : RootAgreement N rootA rootN)
    (fieldScope : SpathCoefficientField p k rootA.prime) : Prop where
  constituent_exists : ∀ Phi : IBr rootA, ∃ theta : IBr rootN,
    BrauerOccursInRestriction N rootA rootN Phi theta
  constituents_conjugate : ∀ (Phi : IBr rootA) (theta eta : IBr rootN),
    BrauerOccursInRestriction N rootA rootN Phi theta →
    BrauerOccursInRestriction N rootA rootN Phi eta →
      ∃ a : A, conjugationOp N a • theta = eta

/-- Routine principal specialization of Navarro (9.2)(a⇒b), p.194:
the principal ambient block covers the principal base block, and all
constituents lie in its conjugates. Its principal cover follows from
trivial restriction and principal-block invariance. No quotient hypothesis
is needed for this direction. The literal support/root adapter is E1/U. -/
structure PrincipalRestrictionSource
    [normalN : N.Normal]
    (roots : RootAgreement N rootA rootN)
    (fieldScope : SpathCoefficientField p k rootA.prime) : Prop where
  restricts_principal : ∀
    (B : LiteralPrimitiveBlock k A) (b : LiteralPrimitiveBlock k N),
    IsPrincipal B → IsPrincipal b →
    ∀ (Phi : IBr rootA) (theta : IBr rootN),
      Supported rootA B Phi →
      BrauerOccursInRestriction N rootA rootN Phi theta →
      Supported rootN b theta

/-- Routine principal specialization of Navarro (9.2)(c⇒a) and (9.6),
pp.194--196: occurrence gives block covering, and the p-group quotient
makes the upper covering block unique. Its comparison block is the
literal principal block, which covers the literal principal base block.
This direction is deliberately separate from unrestricted restriction. -/
structure PrincipalLiftSource
    (roots : RootAgreement N rootA rootN)
    (fieldScope : SpathCoefficientField p k rootA.prime)
    (quotientPGroup : IsPGroup p (A ⧸ N)) : Prop where
  lifts_principal : ∀
    (B : LiteralPrimitiveBlock k A) (b : LiteralPrimitiveBlock k N),
    IsPrincipal B → IsPrincipal b →
    ∀ (Phi : IBr rootA) (theta : IBr rootN),
      Supported rootN b theta →
      BrauerOccursInRestriction N rootA rootN Phi theta →
      Supported rootA B Phi

variable (roots : RootAgreement N rootA rootN)
  (fieldScope : SpathCoefficientField p k rootA.prime)
  (quotientPGroup : IsPGroup p (A ⧸ N))
  (green : Green811Source N rootA rootN roots fieldScope quotientPGroup)

/-- The actual character selected from Green's existence clause. -/
def above (theta : IBr rootN) : IBr rootA :=
  Classical.choose (green.exists_above theta)

theorem above_occurs (theta : IBr rootN) :
    BrauerOccursInRestriction N rootA rootN
      (above N rootA rootN roots fieldScope quotientPGroup green theta) theta :=
  Classical.choose_spec (green.exists_above theta)

theorem above_eq (theta : IBr rootN) (Phi : IBr rootA)
    (occurs : BrauerOccursInRestriction N rootA rootN Phi theta) :
    above N rootA rootN roots fieldScope quotientPGroup green theta = Phi :=
  green.unique_above theta _ Phi
    (above_occurs N rootA rootN roots fieldScope quotientPGroup green theta) occurs

theorem occurs_iff_above_eq (theta : IBr rootN) (Phi : IBr rootA) :
    BrauerOccursInRestriction N rootA rootN Phi theta ↔
      above N rootA rootN roots fieldScope quotientPGroup green theta = Phi := by
  constructor
  · exact above_eq N rootA rootN roots fieldScope quotientPGroup green theta Phi
  · intro equal
    rw [← equal]
    exact above_occurs N rootA rootN roots fieldScope quotientPGroup green theta

/-- The actual quotient condition for the index-two Type B applications
is a cardinal deduction, not a new structural source clause. -/
theorem quotient_isTwoGroup {X : Type*} [Group X]
    (U : Subgroup X) [U.Normal] (indexTwo : U.index = 2) :
    IsPGroup 2 (X ⧸ U) := by
  apply IsPGroup.of_card (p := 2) (n := 1)
  simpa only [pow_one] using U.index_eq_card.symm.trans indexTwo

end ModularRep.PaperProofs.TypeBGreenPrincipalConstituentSource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
