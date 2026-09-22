import ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
import ModularRep.PaperProofs.OddTwoActualLocalBlockSupport
import ModularRep.ModularSystem
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# The cover-free type A consequence on actual fixed-point groups

This is the independent type A input to the relative Jordan reduction, not
the Type C conclusion. Its carriers are literal special linear or special
unitary groups over finite fields, with positive rank and nonabelian simple
central quotient. The defining and coefficient primes must be distinct.
The represented group need not be a universal prime-to-ell cover, and its
centre may have order divisible by ell.

The external implication is the type A consequence used after the current
manuscript's Jordan-reduction lemma. Its source chain is as follows.

* For universal covering groups, Feng--Li--Zhang, Transactions of the AMS
  376 (2023), Theorem 5.2 and the proof of Theorem 1, pp. 6515--6517,
  give BAW-goodness. The passage to the Definition 3.5 relation uses
  Feng--Li--Zhang (2022), Section 3.5, with the central-prime-core and
  central character quotient passages on the actual group when necessary.
* The remaining SL/SU groups are SL2(4), SL2(9), SL3(2), SL3(4), SL4(2),
  SU4(2), SU4(3), and SU6(2), as in Malle--Testerman, Remark 24.19 and
  Table 24.3. Feng--Conghui Li--Zhang, J. Algebra 631 (2023), Proposition
  4.6, supplies iBAW for their simple quotients. Spath's fixed-point
  descent supplies the quotient block bijection. For the nontrivial
  central-prime-core cases, Martinez--Rizo--Rossi (2026), Lemma 3.6(i),
  restricts the actor, and the central normal-core passage gives the
  bijection on the same actual SL/SU group. The remaining nondefining
  primes have cyclic Sylow subgroups and use their Proposition 8.5.

This composite, independently established type A consequence remains an
explicit E2 input; it is not attributed to the universal-cover theorem
alone. The finite-field presentations, complete primitive blocks, local
operations, roots, and interpretation of the fixed Definition 3.5 relation
are its E1/U hypotheses. No source is asserted for arbitrary interpretations
of that relation. No source inhabitant or Type C block conclusion is defined.

The coefficient boundary uses a complete modular system and enough roots
for the finite base group and the actual block-stabilizer semidirect
products. It never requires the fraction field to be algebraically closed.
The K endpoint only applies the scoped source and projects the same block.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeAQuasisimpleSource

open ModularRep CharacterWeight
open CyclicOuterLemma37LiteralLocalExtension
open EvenFieldFLZDefinition35Family EvenFieldFLZSourceConditions

universe u

/-- Actual split type A coordinates, valid in every defining characteristic.
The exponent and characteristic refer to the same finite field. -/
structure LinearCoordinates (pDef rank : ℕ) (H : Type u) [Group H] where
  F : Type u
  [fieldF : Field F]
  [fintypeF : Fintype F]
  [charF : CharP F pDef]
  exponent : ℕ
  exponentPositive : 0 < exponent
  fieldSize : Fintype.card F = pDef ^ exponent
  groupEquiv : H ≃* Matrix.SpecialLinearGroup (Fin (rank + 1)) F

attribute [instance] LinearCoordinates.fieldF LinearCoordinates.fintypeF
  LinearCoordinates.charF

/-- Actual unitary coordinates: the involution is the specified q-power
map on the field of order q squared, not an arbitrary star operation. -/
structure UnitaryCoordinates (pDef rank : ℕ) (H : Type u) [Group H] where
  E : Type u
  [fieldE : Field E]
  [fintypeE : Fintype E]
  [charE : CharP E pDef]
  [starE : StarRing E]
  exponent : ℕ
  exponentPositive : 0 < exponent
  fieldSize : Fintype.card E = pDef ^ (2 * exponent)
  star_eq_frobenius : ∀ x : E, star x = x ^ (pDef ^ exponent)
  groupEquiv : H ≃* Matrix.specialUnitaryGroup (Fin (rank + 1)) E

attribute [instance] UnitaryCoordinates.fieldE UnitaryCoordinates.fintypeE
  UnitaryCoordinates.charE UnitaryCoordinates.starE

/-- The exact two matrix families, on the already prescribed group H. -/
inductive ActualPresentation (pDef rank : ℕ) (H : Type u) [Group H] : Type (u + 1) where
  | linear (coordinates : LinearCoordinates pDef rank H)
  | unitary (coordinates : UnitaryCoordinates pDef rank H)

/-- Group-only applicability. There is no assumption about the order of
the centre or the full Schur multiplier. -/
structure QuasisimpleScope (H : Type u) [Group H] : Prop where
  perfect : commutator H = ⊤
  centralQuotientSimple : IsSimpleGroup (H ⧸ Subgroup.center H)
  centralQuotientNonabelian :
    ¬ IsMulCommutative (H ⧸ Subgroup.center H)

/-- Coefficients and specified interpretation of the same prescribed family.
The ordinary roots also cover every subgroup of H semidirect Gamma for
the actual block-stabilizer actors. Own-character reductions are supplied
on the literal normalizers and agree with the original ambient convention.
These hypotheses contain no character/weight matching or block relation. -/
structure InputSemantics {ell : ℕ} (family : Definition35Family.{u} ell) where
  O : Type u
  [ringO : CommRing O]
  [domainO : IsDomain O]
  [algebraOK : Algebra O family.K]
  modularSystem : ModularSystem ell family.K O family.k
  ordinaryRoots : HasEnoughRootsOfUnity family.K (Nat.card family.H)
  ordinaryActorRoots : ∀ b : family.Block,
    HasEnoughRootsOfUnity family.K
      (Nat.card family.H * Nat.card (family.automorphisms b).Gamma)
  root_residue : ∀ z : O, z ^ primeRegularExponent ell family.H = 1 →
    family.iota.lift (modularSystem.residue z) = algebraMap O family.K z
  catalogue_idempotent : ∀ b : family.Block,
    family.blockSource.operations.ambientBlockData.blockIdempotent b =
      family.blockIdempotent b
  support : OddTwoActualLocalBlockSupport.Source
    family.iota family.blockSource.operations
  reductions : ∀ W : CharacterWeight ell family.K family.H,
    ∃ root : PrimeRegularRootEmbedding ell family.k family.K
        (Subgroup.normalizer (W.subgroup : Set family.H)),
      ∃ phi : IBr root,
        OddTwoActualLocalBlockSupport.RootCompatibleAlong family.iota root
          (Subgroup.normalizer (W.subgroup : Set family.H)).subtype ∧
        NormalizerInflatedReduction W.subgroup W.localCharacter root phi

attribute [instance] InputSemantics.ringO InputSemantics.domainO
  InputSemantics.algebraOK

/-- The scoped, independently established type A consequence described
above. The family, actual SL/SU presentation, block-stabilizer actions and
Definition 3.5 relations are fixed before the implication is supplied.
Its source-to-relation interpretation remains E2/U, not a theorem for a
caller-chosen predicate. Neither an ell-prime cover nor a Type C premise
is present. -/
structure PublishedIBAWSource {ell : ℕ} (pDef rank : ℕ)
    (family : Definition35Family.{u} ell)
    (presentation : ActualPresentation pDef rank family.H)
    (automorphisms : ∀ block : family.Block,
      Definition35AutomorphismStabilizerAdapter (family.problem block))
    (source : ∀ block : family.Block,
      FLZSourceSemantics (family.problem block) (automorphisms block)) : Prop where
  typeA_iBAWBijection : Nat.Prime pDef → Nat.Prime ell → ell ≠ pDef →
    0 < rank → QuasisimpleScope family.H → InputSemantics family →
      Nonempty (Definition35IBAWFamilyWitness family automorphisms source)

/-- Applicability and the named independent type A source, before any
family witness or selected block is produced. -/
structure ApplicationData {ell : ℕ} (pDef : ℕ)
    (family : Definition35Family.{u} ell)
    (automorphisms : ∀ block : family.Block,
      Definition35AutomorphismStabilizerAdapter (family.problem block))
    (source : ∀ block : family.Block,
      FLZSourceSemantics (family.problem block) (automorphisms block)) where
  rank : ℕ
  rankPositive : 0 < rank
  presentation : ActualPresentation pDef rank family.H
  groupScope : QuasisimpleScope family.H
  inputSemantics : InputSemantics family
  published : PublishedIBAWSource pDef rank family presentation automorphisms source

namespace ApplicationData

variable {ell pDef : ℕ} {family : Definition35Family.{u} ell}
variable {automorphisms : ∀ block : family.Block,
  Definition35AutomorphismStabilizerAdapter (family.problem block)}
variable {source : ∀ block : family.Block,
  FLZSourceSemantics (family.problem block) (automorphisms block)}

/-- Apply the authentic source with the family's original coefficient prime. -/
theorem hasDefinition35IBAWFamilyWitness
    (A : ApplicationData pDef family automorphisms source)
    (definingPrime : Nat.Prime pDef) (distinctPrimes : ell ≠ pDef) :
    Nonempty (Definition35IBAWFamilyWitness family automorphisms source) :=
  A.published.typeA_iBAWBijection definingPrime family.ellPrime distinctPrimes
    A.rankPositive A.groupScope A.inputSemantics

/-- Select the same literal block from the source's fixed-family result. -/
theorem blockWitness (A : ApplicationData pDef family automorphisms source)
    (definingPrime : Nat.Prime pDef) (distinctPrimes : ell ≠ pDef)
    (block : family.Block) :
    Nonempty (Definition35IBAWBijection (family.problem block)
      (automorphisms block) (source block)) := by
  obtain ⟨witness⟩ := A.hasDefinition35IBAWFamilyWitness definingPrime distinctPrimes
  exact ⟨witness.blockWitness block⟩

end ApplicationData

end ModularRep.PaperProofs.TypeAQuasisimpleSource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
