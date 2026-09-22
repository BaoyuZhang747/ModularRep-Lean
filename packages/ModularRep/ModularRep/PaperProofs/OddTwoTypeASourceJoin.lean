import ModularRep.PaperProofs.OddTwoFullHGPrincipalRouting
import ModularRep.PaperProofs.OddTwoActualLocalBlockSupport
import ModularRep.PaperProofs.OddTwoPrincipalOrbitAdjustment

/-!
# Coefficient-two type A and the full relative strict-block join

The type-A source statement is the cover-free iBAW-bijection consequence
on the actual special linear or unitary group.  Feng--Li--Zhang (2023),
Theorem 5.2 and the proof of Theorem 1, pp. 6515--6517, give the all-block
type-A result; Section 3.2, pp. 6504--6505, and its use on the actual
quasi-simple factors on p. 6516 give the fixed equation-(3.6) consequence.
The source interpretation of that relation is FLZ (2022), Definition 3.5.
The old even-field source with `ell != 2` and a universal prime-to-ell
cover on the represented group is not applicable here.

An actual SL/SU matrix presentation, defining prime, nondefining coefficient
two, quasi-simplicity and the same literal coefficients/blocks/local
reductions are retained.  No prime-to-two centre, full multiplier, lower
degree beyond positive rank, or nonexceptional multiplier is required.
Rank-one groups are included whenever their central quotient is nonabelian
simple.  The small solvable SL2(3)/SU2(3) case is outside this particular
interface because its central quotient is not simple, hence is not a
member of the existing source class H_G.  This does not restrict the
published theorem's separate solvable-factor argument.

The principal supplier below contains the existing actual intrinsic data,
FM map certificate, orbit correction input, and selected-weight transport.
Its seed is computed by `PrincipalOrbitCorrectionInput.transportedSeed`.
There is no field giving a principal iBAW seed or an all-H_G block theorem.
This supplier is an OPEN mathematical task, not a licensed external theorem.

K combines the existing full-H_G routing with these two branch suppliers
to construct the exact strict-block quantifier of Hypothesis 5.5(b).
It constructs neither supplier, authenticates none of the source predicates
or relations, and applies neither FLZ Theorem 5.7 nor the final Type C goal.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoTypeASourceJoin

open ModularRep
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZFullHG
open ModularRep.PaperProofs.OddTwoFullHGPrincipalRouting
open ModularRep.PaperProofs.OddTwoJordanLabelAndSeedTransport
open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier.PrincipalCharacterData
open ModularRep.PaperProofs.OddTwoPrincipalOrbitAdjustment

universe u

/-- Group-only quasi-simple scope on the represented group itself.
In particular its centre may have even order. -/
structure TypeAQuasisimpleScope (H : Type u) [Group H] : Prop where
  perfect : commutator H = ⊤
  centralQuotientSimple : IsSimpleGroup (H ⧸ Subgroup.center H)
  centralQuotientNonabelian :
    ¬ IsMulCommutative (H ⧸ Subgroup.center H)

/-- E1 interpretation of this exact family.  The ambient catalogue agrees
with the family's actual primitive idempotents.  Each ordinary local
defect-zero character has an actual normalizer reduction under roots
compatible with the ambient convention, and the shared source law binds
its block to the operations used by the weight fibre.  These are source
choices and block facts, not a global correspondence or local triple match.

The family's older selected quotient reductions remain auxiliary choices;
they are not substituted for these prescribed normalizer reductions. -/
structure TypeAInputSemantics (family : Definition35Family.{u} 2) : Prop where
  ordinarySplitting : IsAlgClosed family.K
  catalogue_idempotent : ∀ b : family.Block,
    family.blockSource.operations.ambientBlockData.blockIdempotent b =
      family.blockIdempotent b
  support : OddTwoActualLocalBlockSupport.Source
    family.iota family.blockSource.operations
  reductions : ∀ W : CharacterWeight 2 family.K family.H,
    ∃ root : PrimeRegularRootEmbedding 2 family.k family.K
        (Subgroup.normalizer (W.subgroup : Set family.H)),
      ∃ phi : IBr root,
        OddTwoActualLocalBlockSupport.RootCompatibleAlong family.iota root
          (Subgroup.normalizer (W.subgroup : Set family.H)).subtype ∧
        NormalizerInflatedReduction W.subgroup W.localCharacter root phi

/-- The precise substantial E2 type-A corollary on these actual carriers.
`source` must be interpreted as the published Definition 3.5 relation on
these exact characters, canonical actions, normalizers and reductions.
This field is not asserted for arbitrary interpretations of that relation.
There is no selectable conclusion, cover argument, or principal premise. -/
structure FLZ2023TypeATwoSource (pDef rank : ℕ)
    (family : Definition35Family.{u} 2)
    (presentation : TypeAActualPresentation pDef rank family.H)
    (automorphisms : ∀ block : family.Block,
      Definition35AutomorphismStabilizerAdapter (family.problem block))
    (source : ∀ block : family.Block,
      FLZSourceSemantics (family.problem block) (automorphisms block)) : Prop where
  typeA_iBAWBijection : Nat.Prime pDef → 2 ≠ pDef → 0 < rank →
    TypeAQuasisimpleScope family.H → TypeAInputSemantics family →
      Nonempty (Definition35IBAWFamilyWitness family automorphisms source)

/-- A group-only source scope, coefficient/block interpretation and the
named published theorem.  No iBAW witness is stored as an additional field. -/
structure TypeAApplicationData {pDef rank : ℕ}
    (family : Definition35Family.{u} 2)
    (presentation : TypeAActualPresentation pDef rank family.H)
    (automorphisms : ∀ block : family.Block,
      Definition35AutomorphismStabilizerAdapter (family.problem block))
    (source : ∀ block : family.Block,
      FLZSourceSemantics (family.problem block) (automorphisms block)) : Prop where
  groupScope : TypeAQuasisimpleScope family.H
  inputSemantics : TypeAInputSemantics family
  published : FLZ2023TypeATwoSource pDef rank family presentation automorphisms source

namespace TypeAApplicationData

variable {pDef rank : ℕ} {family : Definition35Family.{u} 2}
variable {presentation : TypeAActualPresentation pDef rank family.H}
variable {automorphisms : ∀ block : family.Block,
  Definition35AutomorphismStabilizerAdapter (family.problem block)}
variable {source : ∀ block : family.Block,
  FLZSourceSemantics (family.problem block) (automorphisms block)}

/-- Apply the fixed published corollary, then select the SAME literal block. -/
theorem blockWitness (A : TypeAApplicationData family presentation automorphisms source)
    (definingPrime : Nat.Prime pDef) (distinctPrimes : 2 ≠ pDef)
    (rankPositive : 0 < rank) (block : family.Block) :
    Nonempty (Definition35IBAWBijection (family.problem block)
      (automorphisms block) (source block)) := by
  obtain ⟨witness⟩ := A.published.typeA_iBAWBijection definingPrime
    distinctPrimes rankPositive A.groupScope A.inputSemantics
  exact ⟨witness.blockWitness block⟩

end TypeAApplicationData

section PrincipalSupplier

variable (family : Definition35Family.{u} 2) (block : family.Block)
variable (automorphisms : Definition35AutomorphismStabilizerAdapter
  (family.problem block))
variable (source : FLZSourceSemantics (family.problem block) automorphisms)
variable (rank : ℕ) (F : Type u) [Field F] [Fintype F]

local instance spFintype : Fintype (Sp rank F) := Fintype.ofFinite _

/-- The remaining principal work, expressed by the existing concrete
construction rather than its desired iBAW conclusion.  Both coefficient
fields are literally those of the selected target family.  The group map
is the inverse of its supplied actual symplectic coordinates, and the
ordinary coefficient map is the identity.

In particular `correction.orbitWitness` and the forward relation/actual
carrier maps in `transport` still require their mathematical proofs or
precisely licensed source bindings.  No inhabitant is declared here. -/
structure CompletedPrincipalSeedAt
    (carrier : OddSymplecticPrincipalCarrier (family.problem block) rank F) where
  SpBlock : Type u
  [blockAction : MulAction (MulAut (Sp rank F))ᵐᵒᵖ SpBlock]
  data : PrincipalCharacterData (n := rank) (F := F)
    (k := family.k) (K := family.K) (Block := SpBlock)
  reduction : ∀ w : data.PrincipalWeight,
    SelectedLocalReductionSource data.blockSource data.principalBlock w
  FM : data.FengMalleTheorem62LiteralCertificate
  principalSource : FLZSourceSemantics
    (data.problem reduction) (data.automorphisms reduction)
  correction : PrincipalOrbitCorrectionInput data reduction FM principalSource
  transport : PrincipalSeedCarrierTransport
    (data.problem reduction) (data.automorphisms reduction) principalSource
    (family.problem block) automorphisms source rank F
  group_coordinates : transport.groupEquiv = carrier.symplecticEquiv.symm
  coefficients_identity : transport.coefficientFieldEquiv = RingEquiv.refl family.K

attribute [instance] CompletedPrincipalSeedAt.blockAction

namespace CompletedPrincipalSeedAt

variable {family block automorphisms source rank F}
variable {carrier : OddSymplecticPrincipalCarrier (family.problem block) rank F}

/-- The principal witness is the existing corrected seed under its actual
selected-character transport; it is not a field of the supplier. -/
def seed (S : CompletedPrincipalSeedAt family block automorphisms source rank F carrier) :
    Definition35IBAWBijection (family.problem block) automorphisms source :=
  S.correction.transportedSeed S.transport

end CompletedPrincipalSeedAt

end PrincipalSupplier

section FullRelativeJoin

variable {pDef : ℕ} {scope : FLZFullHGUniverse pDef 2}
variable {coverage : FullHGDefinition35Coverage scope}
variable {strictSource : FullHGStrictQuasiIsolationAdapter coverage}
variable (routing : FullHGPrincipalRoutingSource coverage strictSource)
variable (blockSource : FullHGBlockSource coverage)

/-- This supplier is explicitly the remaining principal construction, only
at actual principal symplectic carriers of the SAME selected family/block.
It is not an all-relative-block theorem and is not labelled as an external
published input.  Its values retain the actual construction data above. -/
structure CompletedPrincipalSeeds where
  atPrincipal : ∀ (pair : FullHG scope)
      (block : (coverage.presentation pair).family.Block)
      (coordinates : SymplecticCoordinates pDef (routing.pairSource pair).rank
        (coverage.presentation pair).family.H)
      (carrier : OddSymplecticPrincipalCarrier
        ((coverage.presentation pair).family.problem block)
        (routing.pairSource pair).rank coordinates.F),
    Nonempty (CompletedPrincipalSeedAt
      (coverage.presentation pair).family block
      (blockSource.automorphisms pair block) (blockSource.source pair block)
      (routing.pairSource pair).rank coordinates.F carrier)

/-- K: consume the named type-A corollary or the computed principal seed
after the already checked routing of every source-strict block.  No source
pair or strict block can be omitted.  This constructs the exact Hypothesis
5.5(b) packet only AFTER both branch suppliers have been provided. -/
def fullHG_strictBlocks
    (typeA : ∀ (pair : FullHG scope)
      (presentation : TypeAActualPresentation pDef (routing.pairSource pair).rank
        (coverage.presentation pair).family.H),
      TypeAApplicationData (coverage.presentation pair).family presentation
        (blockSource.automorphisms pair) (blockSource.source pair))
    (principal : CompletedPrincipalSeeds routing blockSource) :
    FullHGRelativeHypothesis55StrictBlocks blockSource strictSource where
  iBAWBijection pair block hstrict := by
    rcases routing.strictBlock_typeA_or_principal pair block hstrict with hA | hC
    · obtain ⟨presentation⟩ := hA
      exact (typeA pair presentation).blockWitness scope.definingPrime
        scope.distinctPrimes (routing.pairSource pair).rankPositive block
    · obtain ⟨coordinates, ⟨carrier⟩⟩ := hC
      obtain ⟨S⟩ := principal.atPrincipal pair block coordinates carrier
      exact ⟨S.seed⟩

end FullRelativeJoin

end ModularRep.PaperProofs.OddTwoTypeASourceJoin


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
