import ManuscriptIBAW.TypeB.ExceptionalTarget
import ModularRep.PaperProofs.TypeBCurrentQ3Inputs
import ModularRep.PaperProofs.CurrentFiniteSplittingAssembly

/-!
# A common primitive block family for the exceptional triple cover

The family below uses the actual triple cover, the original modular system,
the original root and the existing local block operations. Its local Brauer
reductions are obtained from the Navarro sources already used by the
faithful block construction. The ambient and local root identities are
proved here. The ordinary field requires finite splitting, not algebraic
closure.

`AmbientIdempotents` is a structural interpretation of the existing block
operations on every actual primitive block. The identification restricted
to faithful blocks does not supply this statement for every block.

`NaturalQuotientTransport` is an explicit external assumption interpreting the
complete natural quotient criteria as the relative block condition on this
fixed family. It includes the specified quotient, character, local block and
root interpretations needed to apply Spath's character-triple criterion
(Theorem 4.4). This interpretation is not proved here, and is not asserted
to be the literal statement of that theorem. The full universal cover is
6.S. In characteristic two its central involution acts trivially, so
inflation identifies the Brauer characters on 3.S with those on 6.S. The
own central-character quotients are S and 3.S in the trivial and faithful
central sectors, respectively. The corresponding preimages of radicals
have the same normalizer quotients. The interpretation of the published
characters and block laws over the fixed K, with the displayed modular
system and roots, is also part of this external assumption. Finite
splitting for X alone is not claimed here to prove that interpretation.

The existing `CurrentFiniteSplittingAssembly.Source` separately supplies
the passage from compatible block conditions to a full family, following
Koshitani--Spath Lemma 3.3 and Spath Definition 5.17/Remark 5.18. Neither
source is a completed exceptional family or an independently supplied matching.
-/

noncomputable section
set_option autoImplicit false

namespace ManuscriptIBAW.TypeB.Exceptional

open ModularRep ModularRep.PaperProofs FDRepSimpleClassKZero
open TypeBQ3TripleCoverCarrier TypeBCentralKernelBlockSource
open TypeBQ3PrincipalWeightInflation TypeBLocalReductionInstantiation
open TypeBFixedRootDefinitionFamily TypeBQ3FaithfulLocalReduction
open CyclicOuterLemma37LiteralLocalExtension EvenFieldFLZDefinition35Family
open EvenFieldFLZSourceConditions TypeBFullBlockCondition
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction

local instance exceptionalFamilyFintype (Y : Type) [Group Y] [Finite Y] : Fintype Y :=
  Fintype.ofFinite Y

section Construction

variable {k K O : Type} [Field k] [Field K] [CommRing O] [IsDomain O]
  [Algebra O K] [CharP k 2] [IsAlgClosed k] [CharZero K]
  {matrixSource : MatrixExceptionalSource}
  {freeSource : TypeBExceptionalCanonicalCover.FreePresentationCoverSource}
  [Finite X] [HasEnoughRootsOfUnity K (Nat.card X)]
  (B : TypeBCurrentQ3Inputs.BeforeInputs (k := k) (K := K) (O := O)
    matrixSource freeSource)

/-- The existing ambient block operations use the literal primitive
idempotent on every block of the triple cover. -/
def AmbientIdempotents : Prop :=
  ∀ b : LiteralPrimitiveBlock k X,
    B.faithful.R.operations.ambientBlockData.blockIdempotent b = b.val

/-- The selected character's own reduction, obtained from its existing
scoped Navarro source on the same normalizer quotient. -/
def familyReduction (b : LiteralPrimitiveBlock k X)
    (w : LiteralWeightFibre B.faithful.R b) :
    SelectedLocalReductionSource B.faithful.R b w := by
  let W := selectedCharacterWeight B.faithful.R b w
  let reduction := TypeBQ3FaithfulLocalReduction.of_scoped
    B.Msys B.root B.calibration W (B.faithful.navarro W)
  exact {
    iota := localQuotientRoot B.root W.subgroup
    brauer := reduction.brauer
    reduction := reduction.reduction }

theorem familyReduction_roots (b : LiteralPrimitiveBlock k X)
    (w : LiteralWeightFibre B.faithful.R b) :
    QuotientRootAgreement B.root (SelectedRadical B.faithful.R b w)
      (familyReduction B b w).iota := by
  change QuotientRootAgreement B.root (SelectedRadical B.faithful.R b w)
    (localQuotientRoot B.root (SelectedRadical B.faithful.R b w))
  rw [localQuotientRoot_eq_localRoot]
  exact localRoot_agrees B.root (SelectedRadical B.faithful.R b w)

/-- The original residue calibration determines the ambient modular-system
root, without an independent choice of roots. -/
theorem root_eq_groupRoot :
    B.root = TypeBModularGroupRootBinding.groupRoot B.Msys X :=
  TypeBModularGroupRootBinding.eq_groupRoot_of_residue B.Msys X B.root B.calibration

def familyPhysical (literal : AmbientIdempotents B) :
    CurrentFiniteSplittingFamily.PrimitivePhysicalSource B.root where
  ordinaryRoots := inferInstance
  blockSource := B.faithful.R
  idempotent := literal
  blockCompatibility := B.faithful.physical
  reduction := familyReduction B
  reduction_roots := familyReduction_roots B

/-- The family is fixed before any block-condition conclusion is used. -/
def commonFamily (literal : AmbientIdempotents B) : Definition35Family 2 := by
  letI := B.faithful.R.operations.ambientBlockData.fintypeBlock
  exact CurrentFiniteSplittingFamily.primitiveFamily B.root
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding B.root)
    (coverDecomposition B.faithful.R literal) Nat.prime_two (familyPhysical B literal)

/-- The specified universal 2′-cover of the simple group. -/
def commonCover (literal : AmbientIdempotents B) :
    EllPrimeCoverSource 2 (commonFamily B literal).H :=
  TypeBQ3PrimeToTwoCover.ellPrimeCover matrixSource freeSource

@[simp] theorem commonFamily_root (literal : AmbientIdempotents B) :
    (commonFamily B literal).iota = B.root := rfl

@[simp] theorem commonFamily_blockSource (literal : AmbientIdempotents B) :
    (commonFamily B literal).blockSource = B.faithful.R := rfl

@[simp] theorem commonFamily_idempotent (literal : AmbientIdempotents B)
    (b : LiteralPrimitiveBlock k X) :
    (commonFamily B literal).blockIdempotent b = b.val := rfl

@[simp] theorem commonCover_projection (literal : AmbientIdempotents B) :
    (commonCover B literal).quotient = q matrixSource freeSource := rfl

/-- Interpret each established natural quotient criterion as a block
witness on the fixed common family over 3.Omega7(3).
Koshitani--Spath, Lemma 3.3, proves the abstract lifting of characters,
weights and blocks from faithful central quotients. The character and block
identifications over these fixed coefficient fields, together with the root
correspondences for quotient groups, extension groups and intermediate
subgroups, remain part of this explicit interpretation assumption.
This transport is not proved here. -/
structure NaturalQuotientTransport (literal : AmbientIdempotents B) : Prop where
  block : ∀ b : LiteralPrimitiveBlock k X,
    TypeBQ3AssemblyApplication.ActualBlockCriterion matrixSource freeSource
      B.root B.R B.faithful.R b →
    Nonempty (BlockWitness (commonFamily B literal) (commonCover B literal) b)

end Construction

section Assembly

variable {k K O : Type} [Field k] [Field K] [CommRing O] [IsDomain O]
  [Algebra O K] [CharP k 2] [IsAlgClosed k] [CharZero K]
  {matrixSource : MatrixExceptionalSource}
  {freeSource : TypeBExceptionalCanonicalCover.FreePresentationCoverSource}
  [Finite X] [HasEnoughRootsOfUnity K (Nat.card X)]
  (B : TypeBCurrentQ3Inputs.BeforeInputs (k := k) (K := K) (O := O)
    matrixSource freeSource)

/-- The constructed family uses the original ambient and local roots.
The natural source transports each proved quotient criterion to a relative
block witness. The separate source passes from these compatible block conditions to the
full inductive condition. -/
theorem commonFamily_complete (literal : AmbientIdempotents B)
    (natural : NaturalQuotientTransport B literal)
    (compatibleFamilySource : CurrentFiniteSplittingAssembly.Source)
    (blocks : TypeBCurrentQ3Inputs.AllBlocksCertificate B) :
    Nonempty (FamilyWitness (commonFamily B literal) (commonCover B literal)) := by
  let : Algebra O (commonFamily B literal).K := inferInstanceAs (Algebra O K)
  apply CurrentFiniteSplittingAssembly.fullFamily
    (commonFamily B literal) (commonCover B literal) B.Msys compatibleFamilySource
    (inferInstanceAs (HasEnoughRootsOfUnity K (Nat.card X)))
    (root_eq_groupRoot B) B.fieldSource literal B.faithful.physical
    (familyReduction_roots B)
  intro b
  exact natural.block b (blocks b)

end Assembly

end ManuscriptIBAW.TypeB.Exceptional

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
